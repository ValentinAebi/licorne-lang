package compiler.program

import compiler.datastructures.Graph
import compiler.irs.SSA
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.{SSAGeneration, TypeChecking}
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.SubtypeRelation.{enforceSubtypingConstraintCustomMsg, enforceExpectedSubtypingConstraint}
import compiler.typechecking.{FunctionContext, TypeStore, Typer}
import compiler.util.zipCommons
import compiler.valuesconversion.GlobalValuesContext
import identifiers.{ThisId, TypeIdentifier}
import lang.*
import lang.Types.*
import lang.Types.PrimitiveType.UnitType
import lang.Formulas.{And, Formula, IdValue}
import lang.Variance.*
import lang.Visibility.Private

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
                          functions: SeqMap[FunctionSignature, SSA.Function],
                          typeDeclPositions: Map[TypeIdentifier, Position],
                          formulaPositions: util.IdentityHashMap[Formula, Position]
                        ) {

  private given ifTyperThenTypeChecking(using Typer): CompilationStep = TypeChecking

  private val subtypingGraph: Graph[TypeIdentifier] = buildSubtypingGraph()
  private val flattenedSupertypesSubstitutions = mutable.LinkedHashMap.empty[TypeIdentifier, mutable.LinkedHashMap[TypeIdentifier, Map[TypeIdentifier, Type]]]

  private val typesReasoningCache = TypesReasoningCache(this)

  private val allTypeVariables = mutable.ListBuffer.empty[(TypeVariable, Option[Position])]

  export typesReasoningCache.developUnencapsulated

  def runtimeSignatures: Iterable[RuntimeTypeSignature] = (interfaces ++ classes ++ objects ++ datatypes ++ records).values

  def allTypeSignatures: Iterable[TypeSignature] = runtimeSignatures ++ typeAliases.values

  def checkDefinitions()(using typer: Typer, program: Program, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
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

  def resolveSignature(typeId: TypeIdentifier): Option[TypeSignature] =
    (interfaces.get(typeId)
      orElse classes.get(typeId)
      orElse objects.get(typeId)
      orElse datatypes.get(typeId)
      orElse records.get(typeId)
      orElse typeAliases.get(typeId))

  def resolveSignatureAs[S <: TypeSignature : ClassTag](typeId: TypeIdentifier): Option[S] =
    resolveSignature(typeId) match {
      case Some(sig: S) => Some(sig)
      case _ => None
    }

  def subToSuperSubst(subT: TypeIdentifier, superT: TypeIdentifier): Option[Map[TypeIdentifier, Type]] = {
    if subT == superT then resolveSignatureAs[RuntimeTypeSignature](subT).map {
      _.typeParams.map {
        case TypeTypeParamInfo(tid, variance, upperBounds, lowerBounds) =>
          tid -> NamedType(tid, List.empty, List.empty)
      }.toMap
    } else for {
      subTSupers <- flattenedSupertypesSubstitutions.get(subT)
      superSubst <- subTSupers.get(superT)
    } yield superSubst
  }

  def isEnumCaseOf(subId: TypeIdentifier, superId: TypeIdentifier): Boolean =
    subToSuperSubst(subId, superId).isDefined

  def desugarType(tpe: Type): Type = {
    val desugaredType = tpe match {
      case primitiveType: Types.PrimitiveType => primitiveType
      case NamedType(typeName, typeArgsRaw, args) =>
        val typeArgsSubst = typeArgsRaw.map(desugarType)
        typeAliases.get(typeName) match {
          case Some(TypeAliasSignature(id, typeParams, thisValue, params, rhs)) =>
            val typesSubst =
              typeParams.map(_.tid)
                .zipCommons(typeArgsSubst)
                .toMap
            val valsSubst = params.map {
              case (paramId, (paramType, paramVal)) => paramVal
            }.zipCommons(args).toMap
            desugarType(rhs.substitute(typesSubst, valsSubst))
          case None => NamedType(typeName, typeArgsSubst, args)
        }
      case typeVariable: TypeVariable => typeVariable.substitutedIfResolved
      case UnionType(types) => UnionType(types.map(desugarType))
      case IntersectionType(types) => IntersectionType(types.map(desugarType))
      case ClosureType(params, resultType) => ClosureType(params.map(desugarType), desugarType(resultType))
      case intRangeType: IntRangeType => intRangeType
    }
    if desugaredType == tpe then tpe
    else desugarType(desugaredType)
  }

  def saveTypeVariable(tv: TypeVariable, posOpt: Option[Position]): Unit = {
    allTypeVariables.addOne((tv, posOpt))
  }

  def checkAllTypeVariablesHaveBeenResolved()(using ErrorReporter, CompilationStep): Unit = {
    for ((tv, posOpt) <- allTypeVariables) {
      if (!tv.isResolved) {
        reportError(s"type variable $tv could not be resolved", posOpt)
      }
    }
  }

  private def buildSubtypingGraph(): Graph[TypeIdentifier] = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for (sig <- runtimeSignatures) {
      val id = sig.id
      graphB.addVertex(id)
      graphB.addDescendants(id, sig.directSupertypes.map(_.typeName))
    }
    graphB.build()
  }

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

  private def checkInterfaceSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, InterfaceSignature(id, typeParams, functions, directSupertypes)) <- interfaces) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      checkSuperinterfaces(id, directSupertypes)
    }
  }

  private def checkClassSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, ClassSignature(id, typeParams, fields, importedObjects, functions, directSupertypes)) <- classes) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      val posOpt = positions.get(id)
      checkFields(fields.values)
      checkImportedObjects(importedObjects)
      checkSuperinterfaces(id, directSupertypes)
    }
  }

  private def checkObjectSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, ObjectSignature(id, importedObjects, functions, directSupertypes)) <- objects) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, Set.empty)

      checkImportedObjects(importedObjects)
      checkSuperinterfaces(id, directSupertypes)
    }
  }

  private def checkDatatypeSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, DatatypeSignature(id, typeParams, directSupertypes, directSubtypes)) <- datatypes) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      checkSupertypesOfUnencapsulated(id, directSupertypes)
    }
  }

  private def checkRecordSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, RecordSignature(id, typeParams, fields, directSupertypes)) <- records) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      checkFields(fields.values)
      checkSupertypesOfUnencapsulated(id, directSupertypes)
    }
  }

  private def checkTypeAliasSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, TypeAliasSignature(id, typeParams, itValue, params, rhs)) <- typeAliases) {
      given posOpt: Option[Position] = positions.get(id)

      given funCtx: FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      for ((paramId, (paramType, paramVal)) <- params) {
        funCtx.checkType(paramType, None, posOpt)
        ts(paramVal) = paramType
      }
      funCtx.checkType(rhs, None, posOpt)
    }
  }

  private def checkImportedObjects(importedObjects: mutable.LinkedHashSet[IdValue])
                                  (using er: ErrorReporter, compilationStep: CompilationStep, positions: Map[TypeIdentifier, Position]): Unit = {
    importedObjects.foreach { objVal =>
      val objId = globalValuesContext.getNameOfObject(objVal)
      resolveSignature(objId) match {
        case Some(_: ObjectSignature) => ()
        case _ =>
          reportError(s"no object named $objId found", positions.get(objId))
      }
    }
  }

  private def checkFields(fields: Iterable[Field])
                         (using funCtx: FunctionContext, er: ErrorReporter, posOpt: Option[Position], compilationStep: CompilationStep): Unit = {
    fields.foreach { field =>
      val variance = if field.isStable then Covariant else Invariant
      funCtx.checkType(field.tpe, Some(variance), posOpt)
    }
  }

  private def checkFunctionSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for ((funSig@FunctionSignature(ownerName, functionName, funTypeParams, funParamsInclThis, funRetType, funVisibility), SSA.Function(_, funBodyOpt, funPosOpt)) <- functions) {
      val ownerSig = resolveSignatureAs[RuntimeTypeSignature](ownerName).get

      val funCtxWithoutFunTypeParams = FunctionContext(
        this,
        ownerSig.typeParams.map(tp => tp.tid -> tp).toMap,
        Map.empty,
        funSig.receiverVal,
        ownerName,
        expectedReturnType = funRetType
      )
      val funCtx = funTypeParams.foldLeft(funCtxWithoutFunTypeParams) {
        case (ctx, ftp@FunctionTypeParamInfo(tid, upperBoundOpt, lowerBoundOpt)) =>
          upperBoundOpt.foreach(ctx.checkType(_, None, funPosOpt))
          lowerBoundOpt.foreach(ctx.checkType(_, None, funPosOpt))
          ctx.withNewFunctionTypeParam(ftp)
      }

      if (funVisibility == Private && ownerSig.isInstanceOf[InterfaceSignature]) {
        reportError(s"$Private methods are not allowed in interfaces", funPosOpt)
      }
      val conflictingTypeParams = funTypeParams.intersect(ownerSig.typeParams)
      if (conflictingTypeParams.nonEmpty) {
        reportError(s"type parameter(s) ${conflictingTypeParams.mkString(",")} conflict(s) with type parameter(s) of $ownerName that have the same name(s)", funPosOpt)
      }
      ts(funSig.receiverVal) = funSig.receiverType
      for ((paramVal, paramType) <- funParamsInclThis.tail) {
        funCtx.checkType(paramType, Some(Contravariant), funPosOpt)
        ts(paramVal) = paramType
      }
      funCtx.checkType(funRetType, Some(Covariant), funPosOpt)
    }
  }

  private def analyzeOverrides()(using program: Program, er: ErrorReporter, compilationStep: CompilationStep, typeDefPositions: Map[TypeIdentifier, Position]): Unit = {
    for ((subT, subTSupertypes) <- flattenedSupertypesSubstitutions; (superT, typeTypeParamsSubst) <- subTSupertypes) {
      val subTSig = resolveSignature(subT).get
      val superTSig = resolveSignature(superT).get
      (subTSig, superTSig) match {
        case (subTSig: Encapsulated, superTSig: Encapsulated) =>
          for ((funId, superFunSig@FunctionSignature(_, _, superFunTypeParams, superFunParams, superFunRetType, superFunVisibility)) <- superTSig.functions) {
            subTSig.functions.get(funId) match {
              // TODO allow method implementation in interfaces?
              case None if subTSig.isInstanceOf[InterfaceSignature] => ()
              case None =>
                reportError(s"$subT does not implement method $funId declared in its supertype $superT", typeDefPositions.get(subT))
              case Some(subFunSig@FunctionSignature(_, _, subFunTypeParams, subFunParams, subFunRetType, subFunVisibility)) =>
                val funPosOpt = functions.get(subFunSig).flatMap(_.posOpt)
                val typeParamsLenMatch = subFunTypeParams.size == superFunTypeParams.size
                val paramsLenMatch = subFunParams.size == superFunParams.size
                if (!typeParamsLenMatch) {
                  reportError(s"length of type parameters list in method $funId in $subT does not match its length in its supertype $superT", funPosOpt)
                }
                if (!paramsLenMatch) {
                  reportError(s"length of parameters list in method $funId in $subT does not match its length in its supertype $superT", funPosOpt)
                }
                if (typeParamsLenMatch && paramsLenMatch) {
                  val funTypeParamsSubst = mutable.Map.empty[TypeIdentifier, Type]
                  for ((superFunTp, subFunTp) <- superFunTypeParams zip subFunTypeParams) {

                    def mkErrorMsg(upOrLow: String): String =
                      s"$upOrLow bound of type parameter ${subFunTp.tid} of function $funId in $subT does not conform to the signature of the overridden function in $superT"

                    subFunTp.upperBoundOpt.foreach { subFunUpperBound =>
                      superFunTp.upperBoundOpt match {
                        case Some(superFunUpperBound) =>
                          enforceSubtypingConstraintCustomMsg(superFunUpperBound, subFunUpperBound, mkErrorMsg("upper"))(using funPosOpt)
                        case None =>
                          reportError(mkErrorMsg("upper"), funPosOpt)
                      }
                    }
                    subFunTp.lowerBoundOpt.foreach { subFunLowerBound =>
                      superFunTp.lowerBoundOpt match {
                        case Some(superFunLowerBound) =>
                          enforceSubtypingConstraintCustomMsg(subFunLowerBound, superFunLowerBound, mkErrorMsg("lower"))(using funPosOpt)
                        case None =>
                          reportError(mkErrorMsg("lower"), funPosOpt)
                      }
                    }
                    funTypeParamsSubst.addOne(superFunTp.tid -> NamedType(subFunTp.tid, List.empty, List.empty))
                  }
                  val typeParamsSubst = typeTypeParamsSubst ++ funTypeParamsSubst
                  val valsSubst = mutable.Map.empty[IdValue, IdValue]
                  // TODO do not forget to check refinements on the receiver (the base type is not checked here)
                  val superTSubst = superTSig.toType(typeParamsSubst, Map.empty)
                  for (((subParamVal, subParamType), (superParamVal, superParamType)) <- subFunParams.tail zip superFunParams.tail) {
                    val expectedSubParamType = superParamType.substitute(typeParamsSubst, valsSubst.toMap)
                    if (subParamType != expectedSubParamType) {
                      reportError(s"type mismatch on parameter ${subParamVal.sourceLevelDescrOrDefault} of method $funId: " +
                        s"type is $subParamType but should be $expectedSubParamType since the method overrides $funId in $superTSubst", funPosOpt)
                    }
                    valsSubst(superParamVal) = subParamVal
                  }
                  val expectedRetType = superFunRetType.substitute(typeParamsSubst, valsSubst.toMap)
                  enforceExpectedSubtypingConstraint(subFunRetType, expectedRetType, s"return type of method $funId that overrides $funId in $superT")(using funPosOpt, er, this)
                }
                if (!subFunVisibility.atLeastAsPermissiveAs(superFunVisibility)) {
                  reportError(s"$funId in $subT overrides $funId in $superT but has a more restricted visibility", funPosOpt)
                }
            }
          }
        case _ => ()
      }
    }
  }

  private def checkSuperinterfaces(childTypeId: TypeIdentifier, superTypes: List[NamedType])
                                  (using funCtx: FunctionContext, er: ErrorReporter, posOpt: Option[Position], compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      funCtx.checkType(superT, Some(Covariant), posOpt)
      resolveSignature(superT.typeName).foreach {
        case _: InterfaceSignature => ()
        case _ => reportError(s"interface not found: ${superT.typeName}", posOpt)
      }
    }
  }

  private def checkSupertypesOfUnencapsulated(id: TypeIdentifier, superTypes: List[NamedType])
                                             (using funCtx: FunctionContext, er: ErrorReporter, posOpt: Option[Position], compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      funCtx.checkType(superT, Some(Covariant), posOpt)
      resolveSignature(superT.typeName).foreach {
        case DatatypeSignature(superTypeId, _, _, subOfSuper) =>
          if (!subOfSuper.contains(id)) {
            reportError(s"$id cannot extend $superTypeId since they are defined in distinct source files", posOpt)
          }
        case _ => reportError(s"datatype not found: ${superT.typeName}", posOpt)
      }
    }
  }

  private def checkSubtypingCyclicity()(using er: ErrorReporter, compilationStep: CompilationStep, positions: Map[TypeIdentifier, Position]): Unit = {
    subtypingGraph.findShortestCycle().foreach { cycle =>
      reportError("cyclic subtyping: " ++ cycle.mkString(" <: "), positions.get(cycle.head))
    }
  }

  private def checkObjectImportsCyclicity()(using er: ErrorReporter, compilationStep: CompilationStep, positions: Map[TypeIdentifier, Position]): Unit = {
    val graphB = Graph.Builder[IdValue]()
    for ((id, sig) <- objects) {
      val objVal = globalValuesContext.resolveObject(id)
      graphB.addVertex(objVal).addDescendants(objVal, sig.importedObjects)
    }
    graphB.build().findShortestCycle().foreach { cycle =>
      reportError("cyclic imports between the following objects, violating ocap: " ++ cycle.map(globalValuesContext.getNameOfObject).mkString(" -> "),
        positions.get(globalValuesContext.getNameOfObject(cycle.head)))
    }
  }

  private def checkTypeAliasesCyclicity()(using er: ErrorReporter, compilationStep: CompilationStep, positions: Map[TypeIdentifier, Position]): Unit = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for ((id, sig) <- typeAliases) {
      val rhsFreeTypes = findMentionedTypes(sig.rhs) -- sig.typeParams.map(_._1)
      graphB.addDescendants(id, rhsFreeTypes)
    }
    graphB.build().findShortestCycle().foreach { cycle =>
      reportError("cyclic dependencies between the following type aliases: " ++ cycle.mkString(" -> "), positions.get(cycle.head))
    }
  }

  private def buildAndCheckFlattenedSubtypingMaps()(using er: ErrorReporter, compilationStep: CompilationStep, positions: Map[TypeIdentifier, Position]): Unit = {
    for (subtypeId <- subtypingGraph.topologicalSort().reverse) {
      val subtypeSupertypes = mutable.LinkedHashMap.empty[TypeIdentifier, Map[TypeIdentifier, Type]]

      def checkAndSave(name: TypeIdentifier, newSubst: Map[TypeIdentifier, Type]): Unit = {
        subtypeSupertypes.get(name) match {
          case Some(prevSubst) =>
            if (prevSubst != newSubst) {
              val supertype2Sig = resolveSignatureAs[RuntimeTypeSignature](name).get
              val conflictingType1 = supertype2Sig.toType(prevSubst, Map.empty)
              val conflictingType2 = supertype2Sig.toType(newSubst, Map.empty)
              reportError(s"$subtypeId subtypes both $conflictingType1 and $conflictingType2", positions.get(subtypeId))
            }
          case None =>
            subtypeSupertypes(name) = newSubst
        }
      }

      val subtypeSig = resolveSignatureAs[RuntimeTypeSignature](subtypeId).get
      for (supertype1 <- subtypeSig.directSupertypes) {
        val supertype1Sig = resolveSignatureAs[RuntimeTypeSignature](supertype1.typeName).get
        val oneStepSubst = (supertype1Sig.typeParams.map(_._1) zip supertype1.typeArgs).toMap
        checkAndSave(supertype1.typeName, oneStepSubst)
        for ((supertype2Id, superSubst) <- flattenedSupertypesSubstitutions(supertype1.typeName)) {
          val composedSubst = for (tid, tpe) <- superSubst yield tid -> tpe.substitute(oneStepSubst, Map.empty)
          checkAndSave(supertype2Id, composedSubst)
        }
      }
      flattenedSupertypesSubstitutions(subtypeId) = subtypeSupertypes
    }
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

  private def checkTypeParamsAndMkTSigCheckingCtx(id: TypeIdentifier, typeParams: Iterable[TypeTypeParamInfo])(using typer: Typer, ts: TypeStore, er: ErrorReporter, posOpt: Option[Position]): FunctionContext = {
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

    def build(allFunctions: SeqMap[FunctionSignature, SSA.Function],
              typeDeclPositions: Map[TypeIdentifier, Position],
              formulaPositions: util.IdentityHashMap[Formula, Position]): Program = {
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
        allFunctions,
        typeDeclPositions,
        formulaPositions
      )
    }
  }

  extension (er: ErrorReporter) private def reportError(msg: String, posOpt: Option[Position])(using compilationStep: CompilationStep): Unit = {
    er.report(Err(compilationStep, msg, posOpt))
  }

}
