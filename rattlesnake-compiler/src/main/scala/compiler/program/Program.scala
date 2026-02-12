package compiler.program

import compiler.datastructures.Graph
import compiler.identifiers.{ThisId, TypeIdentifier}
import compiler.irs.SSA
import compiler.lang.Formulas.{And, Formula, IdValue}
import compiler.lang.Types.PrimitiveType.UnitType
import compiler.lang.Types.{PrimitiveType, Type, TypeVariable}
import compiler.lang.Visibility.Private
import compiler.lang.*
import compiler.lang.Variance.Contravariant
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.{SSAGeneration, TypeChecking}
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typing.phases.Typer1
import compiler.typing.TypeStore
import compiler.typing.smartcasting.TypesReasoningCache
import compiler.util.zipCommons
import compiler.valuesconversion.GlobalValuesContext

import java.util
import scala.collection.{SeqMap, mutable}
import scala.reflect.ClassTag
import scala.util.boundary

final case class Program(
                          globalValuesContext: GlobalValuesContext,
                          interfaces: Map[TypeIdentifier, InterfaceSignature],
                          classes: Map[TypeIdentifier, ClassSignature],
                          objects: Map[TypeIdentifier, ObjectSignature],
                          datatypes: Map[TypeIdentifier, DatatypeSignature],
                          records: Map[TypeIdentifier, RecordSignature],
                          typeAliases: Map[TypeIdentifier, TypeAliasSignature],
                          functions: SeqMap[FunctionSignature, SSA.Function]
                        ) {

  def runtimeSignatures: Iterable[RuntimeTypeSignature] = (interfaces ++ classes ++ objects ++ datatypes ++ records).values

  def allTypeSignatures: Iterable[TypeSignature] = runtimeSignatures ++ typeAliases.values

  def checkDefinitions()(using typer: Typer1, program: Program, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    checkInterfaceSignatures()
    checkClassSignatures()
    checkObjectSignatures()
    checkDatatypeSignatures()
    checkRecordSignatures()
    checkTypeAliasSignatures()

    checkSubtypingCyclicity()
    checkObjectImportsCyclicity()
    checkTypeAliasesCyclicity()
    er.displayAndTerminateIfErrors()

    buildAndCheckFlattenedSubtypingMaps()
    er.displayAndTerminateIfErrors()

    checkFunctionSignatures()
    analyzeOverrides()

    er.displayAndTerminateIfErrors()
  }

  def isEnumCaseOf(subId: TypeIdentifier, superId: TypeIdentifier): Boolean =
    subToSuperSubst(subId, superId).isDefined

  def forceComputeJoins(tpe: Type)(using program: Program): Option[NamedType] = tpe match {
    case namedType: NamedType => Some(namedType)
    case _: UnionType => boundary {

      def extractTypeIds(tpe: Type): Set[TypeIdentifier] = tpe match {
        case NamedType(tid, _, _) => Set(tid)
        case UnionType(types) => types.flatMap(extractTypeIds)
        case _ => boundary.break(None)
      }

      val allTypeIds = extractTypeIds(tpe)
      val commonDirectSupertypes = allTypeIds.map { tid =>
        val sig = program.resolveSignatureAs[RuntimeTypeSignature](tid).getOrElse {
          boundary.break(None)
        }
        sig.directSupertypes.toSet
      }.reduce(_.intersect(_))

      val possibleSubstitutions = {
        for {
          NamedType(superTypeId, _, _) <- commonDirectSupertypes
          subst <- program.subToSuperSubst(allTypeIds.head, superTypeId)
          if allTypeIds.tail.forall {
            program.subToSuperSubst(_, superTypeId).contains(subst)
          }
        } yield (superTypeId, subst)
      }
      if (possibleSubstitutions.size == 1) {
        val (superTypeId, subst) = possibleSubstitutions.head
        program.resolveSignatureAs[RuntimeTypeSignature](superTypeId).flatMap { sig =>
          sig.toType(subst, Map.empty) match {
            case namedType: NamedType => Some(namedType)
            case _ => None
          }
        }
      } else None
    }
    case _ => None
  }

  private def findMentionedTypes(tpe: Type): Set[TypeIdentifier] = tpe match {
    case primitiveType: Types.PrimitiveType => Set.empty
    case NamedType(typeName, typeParams, params) =>
      Set(typeName) ++ typeParams.flatMap(findMentionedTypes) ++ params.flatMap(findMentionedTypes)
    case _: TypeVariable => Set.empty
    case UnionType(types) =>
      types.flatMap(findMentionedTypes)
    case IntersectionType(types) =>
      types.flatMap(findMentionedTypes)
    case ClosureType(params, resultType) =>
      params.flatMap(findMentionedTypes).toSet ++ findMentionedTypes(resultType)
    case IntRangeType(lowerBound, upperBound) =>
      lowerBound.collectFormulas(findMentionedTypes).flatten ++ upperBound.collectFormulas(findMentionedTypes).flatten
  }

  private def findMentionedTypes(formula: Formula): Set[TypeIdentifier] = formula match {
    case value: Formulas.Value => Set.empty
    case op: Formulas.BinOp => findMentionedTypes(op.lhs) ++ findMentionedTypes(op.rhs)
    case op: Formulas.UnaryOp => findMentionedTypes(op.operand)
    case Formulas.Call(receiver, funId, typeArgs, args) => findMentionedTypes(receiver) ++ typeArgs.flatMap(findMentionedTypes) ++ args.flatMap(findMentionedTypes)
    case Formulas.ClosureInvocation(closure, args) => findMentionedTypes(closure) ++ args.flatMap(findMentionedTypes)
    case Formulas.Select(owner, fieldName) => findMentionedTypes(owner)
    case Formulas.HasType(formula, tpe) => findMentionedTypes(formula) + tpe
  }

  private def checkTypeParamsAndMkTSigCheckingCtx(id: TypeIdentifier, typeParams: Iterable[TypeTypeParamInfo])(using typer: Typer1, ts: TypeStore, er: ErrorReporter, posOpt: Option[Position]): FunctionContext = {
    val noTypeParamsCtx = FunctionContext(this, Map.empty, Map.empty, globalValuesContext.valuesGen.newValue(ThisId), id, expectedReturnType = UnitType)
    typeParams.foldLeft(noTypeParamsCtx) {
      case (ctx, ttp@TypeTypeParamInfo(tid, variance, upperBoundOpt, lowerBoundOpt)) =>
        upperBoundOpt.foreach(ctx.checkType(_, None, posOpt))
        lowerBoundOpt.foreach(ctx.checkType(_, None, posOpt))
        ctx.withNewTypeTypeParam(ttp)
    }
  }

  private def reportError(msg: String, posOpt: Option[Position])(using er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    er.report(Err(compilationStep, msg, posOpt))
  }

}

object Program {

  final class Builder(er: ErrorReporter) {
    private val signatures = mutable.LinkedHashMap.empty[TypeIdentifier, TypeSignature]

    val globalValuesContext: GlobalValuesContext = GlobalValuesContext()

    def saveSignature(sig: TypeSignature, posOpt: Option[Position]): Unit = {
      if (PrimitiveType.values.exists(_.str == sig.id.toString)) {
        er.report(Err(SSAGeneration, s"identifier ${sig.id} is illegal since it conflicts with a primitive type", posOpt))
      } else if (signatures.contains(sig.id)) {
        er.report(Err(SSAGeneration, s"redefinition of type ${sig.id}", posOpt))
      } else {
        signatures(sig.id) = sig
      }
    }

    def build(allFunctions: SeqMap[FunctionSignature, SSA.Function]): Program = {
      val interfacesB = Map.newBuilder[TypeIdentifier, InterfaceSignature]
      val classesB = Map.newBuilder[TypeIdentifier, ClassSignature]
      val packagesB = Map.newBuilder[TypeIdentifier, ObjectSignature]
      val datatypes = Map.newBuilder[TypeIdentifier, DatatypeSignature]
      val recordsB = Map.newBuilder[TypeIdentifier, RecordSignature]
      val typeAliasesB = Map.newBuilder[TypeIdentifier, TypeAliasSignature]
      for ((id, sig) <- signatures) {
        sig match {
          case sig: InterfaceSignature => interfacesB.addOne(id, sig)
          case sig: ClassSignature => classesB.addOne(id, sig)
          case sig: ObjectSignature => packagesB.addOne(id, sig)
          case sig: DatatypeSignature => datatypes.addOne(id, sig)
          case sig: RecordSignature => recordsB.addOne(id, sig)
          case sig: TypeAliasSignature => typeAliasesB.addOne(id, sig)
        }
      }
      Program(
        globalValuesContext,
        interfacesB.result(),
        classesB.result(),
        packagesB.result(),
        datatypes.result(),
        recordsB.result(),
        typeAliasesB.result(),
        allFunctions
      )
    }
  }

  extension (er: ErrorReporter) private def reportError(msg: String, posOpt: Option[Position])(using compilationStep: CompilationStep): Unit = {
    er.report(Err(compilationStep, msg, posOpt))
  }

}
