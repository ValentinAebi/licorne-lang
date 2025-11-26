package compiler.program

import compiler.datastructures.Graph
import compiler.irs.SSA
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.TypeCheckingContext
import compiler.valuesconversion.GlobalValuesContext
import identifiers.TypeIdentifier
import lang.*
import lang.Field.ReassignableField
import lang.Types.{NamedType, PrimitiveType, Type}
import lang.Values.{Formula, IdValue}
import lang.Variance.*

import scala.collection.mutable
import scala.reflect.ClassTag

final case class Program(
                          globalValuesContext: GlobalValuesContext,
                          interfaces: Map[TypeIdentifier, InterfaceSignature],
                          classes: Map[TypeIdentifier, ClassSignature],
                          objects: Map[TypeIdentifier, ObjectSignature],
                          datatypes: Map[TypeIdentifier, DatatypeSignature],
                          structs: Map[TypeIdentifier, StructSignature],
                          typeAliases: Map[TypeIdentifier, TypeAliasSignature],
                          functions: Map[FunctionSignature, SSA.Function]
                        ) {
  private val subtypingGraph: Graph[TypeIdentifier] = buildSubtypingGraph()
  private val flattenedSupertypesSubstitutions = mutable.Map.empty[TypeIdentifier, mutable.Map[TypeIdentifier, Map[TypeIdentifier, Type]]]

  def checkDefinitions()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    checkInterfaceSignatures()
    checkClassSignatures()
    checkObjectSignatures()
    checkDatatypeSignatures()
    checkStructSignatures()
    checkSubtypingCyclicity()
    checkObjectImportsCyclicity()
    checkTypeAliasesCyclicity()
    er.displayAndTerminateIfErrors()

    buildAndCheckFlattenedSubtypingMaps()
    er.displayAndTerminateIfErrors()

    checkFunctionSignatures()
    er.displayAndTerminateIfErrors()
  }

  def resolveSignature(typeId: TypeIdentifier): Option[TypeSignature] =
    (interfaces.get(typeId)
      orElse classes.get(typeId)
      orElse objects.get(typeId)
      orElse datatypes.get(typeId)
      orElse structs.get(typeId)
      orElse typeAliases.get(typeId))

  def resolveSignatureAs[S <: TypeSignature : ClassTag](typeId: TypeIdentifier): Option[S] =
    resolveSignature(typeId) match {
      case Some(sig: S) => Some(sig)
      case _ => None
    }

  def subToSuperSubst(subT: TypeIdentifier, superT: TypeIdentifier): Option[Map[TypeIdentifier, Type]] =
    for {
      subTSupers <- flattenedSupertypesSubstitutions.get(subT)
      superSubst <- subTSupers.get(superT)
    } yield superSubst

  private def buildSubtypingGraph(): Graph[TypeIdentifier] = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for ((id, sig) <- interfaces ++ classes ++ objects ++ datatypes ++ structs) {
      graphB.addVertex(id)
      graphB.addDescendants(id, sig.directSupertypes.map(_.typeName))
    }
    graphB.build()
  }

  private def checkInterfaceSignatures()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    for ((_, InterfaceSignature(id, typeParams, functions, directSupertypes)) <- interfaces) {
      given tcCtx: TypeCheckingContext = TypeCheckingContext(this, typeParams.toMap, Set.empty)

      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
  }

  private def checkClassSignatures()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    for ((_, ClassSignature(id, typeParams, fields, importedObjects, functions, directSupertypes)) <- classes) {
      given tcCtx: TypeCheckingContext = TypeCheckingContext(this, typeParams.toMap, Set.empty)

      val posOpt = positions.get(id)
      checkFields(fields.values, posOpt)
      checkImportedObjects(importedObjects)
      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
  }

  private def checkObjectSignatures()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    for ((_, ObjectSignature(id, importedObjects, functions, directSupertypes)) <- objects) {
      given tcCtx: TypeCheckingContext = TypeCheckingContext(this, Map.empty, Set.empty)

      checkImportedObjects(importedObjects)
      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
  }

  private def checkDatatypeSignatures()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    for ((_, DatatypeSignature(id, typeParams, directSupertypes, directSubtypes)) <- datatypes) {
      given tcCtx: TypeCheckingContext = TypeCheckingContext(this, typeParams.toMap, Set.empty)

      checkSupertypesOfStructLike(id, directSupertypes, positions.get(id))
    }
  }

  private def checkStructSignatures()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    for ((_, StructSignature(id, typeParams, fields, directSupertypes)) <- structs) {
      given tcCtx: TypeCheckingContext = TypeCheckingContext(this, typeParams.toMap, Set.empty)

      val posOpt = positions.get(id)
      checkFields(fields.values, posOpt)
      checkSupertypesOfStructLike(id, directSupertypes, posOpt)
    }
  }

  private def checkImportedObjects(importedObjects: mutable.LinkedHashSet[IdValue])
                                  (using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    importedObjects.foreach { objVal =>
      val objId = globalValuesContext.getNameOfObject(objVal)
      resolveSignature(objId) match {
        case Some(_: ObjectSignature) => ()
        case _ =>
          er.reportError(s"no object named $objId found", positions.get(objId))
      }
    }
  }

  private def checkFields(fields: Iterable[Field], posOpt: Option[Position])
                         (using tcCtx: TypeCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    fields.foreach { field =>
      tcCtx.varianceOf(field.tpe.baseType).foreach {
        case Invariant => ()
        case Covariant =>
          if (field.isInstanceOf[ReassignableField]) {
            er.reportError(s"variance error: reassignable field ${field.id} has covariant type ${field.tpe.baseType}", posOpt)
          }
        case Contravariant =>
          er.reportError(s"variance error: field ${field.id} has contravariant type ${field.tpe.baseType}", posOpt)
      }
      tcCtx.checkTypesWellDefined(field.tpe, posOpt)
    }
  }

  private def checkFunctionSignatures()(using er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    // TODO check the types in signature
    // TODO check overrides (presence of the method, parameters, type parameters, return type, visibility)
    for ((funSig@FunctionSignature(ownerName, functionName, funTypeParams, funParamsInclThis, funRetType, funVisibility), SSA.Function(_, body, posOpt)) <- functions) {
      val ownerSig = resolveSignatureAs[RuntimeTypeSignature](ownerName).get

      given tcCtx: TypeCheckingContext = TypeCheckingContext(this, ownerSig.typeParams.toMap, funTypeParams.toSet)

      for ((paramId, paramType) <- funParamsInclThis) {
        tcCtx.checkTypesWellDefined(paramType, posOpt)
        // TODO check variance (and be careful about "composition", e.g. double contravariance)
      }
    }
  }

  private def checkSuperinterfaces(childTypeId: TypeIdentifier, superTypes: List[NamedType], posOpt: Option[Position])
                                  (using tcCtx: TypeCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      tcCtx.checkTypesWellDefined(superT, posOpt)
      resolveSignature(superT.typeName).foreach {
        case _: InterfaceSignature => ()
        case _ => er.reportError(s"interface not found: ${superT.typeName}", posOpt)
      }
    }
  }

  private def checkSupertypesOfStructLike(id: TypeIdentifier, superTypes: List[NamedType], posOpt: Option[Position])
                                         (using tcCtx: TypeCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      tcCtx.checkTypesWellDefined(superT, posOpt)
      resolveSignature(superT.typeName).foreach {
        case DatatypeSignature(superTypeId, _, _, subOfSuper) =>
          if (!subOfSuper.contains(id)) {
            er.reportError(s"$id cannot extend $superTypeId since they are defined in distinct source files", posOpt)
          }
        case _ => er.reportError(s"datatype not found: ${superT.typeName}", posOpt)
      }
    }
  }

  private def checkSubtypingCyclicity()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    subtypingGraph.findShortestCycle().foreach { cycle =>
      er.reportError("cyclic subtyping: " ++ cycle.mkString(" <: "), positions.get(cycle.head))
    }
  }

  private def checkObjectImportsCyclicity()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    val graphB = Graph.Builder[IdValue]()
    for ((id, sig) <- objects) {
      val objVal = globalValuesContext.resolveObject(id)
      graphB.addVertex(objVal).addDescendants(objVal, sig.importedObjects)
    }
    graphB.build().findShortestCycle().foreach { cycle =>
      er.reportError("cyclic imports between the following objects, violating ocap: " ++ cycle.map(globalValuesContext.getNameOfObject).mkString(" -> "),
        positions.get(globalValuesContext.getNameOfObject(cycle.head)))
    }
  }

  private def checkTypeAliasesCyclicity()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for ((id, sig) <- typeAliases) {
      val rhsFreeTypes = findMentionedTypes(sig.rhs) -- sig.typeParams.map(_._1)
      graphB.addDescendants(id, rhsFreeTypes)
    }
    graphB.build().findShortestCycle().foreach { cycle =>
      er.reportError("cyclic dependencies between the following type aliases: " ++ cycle.mkString(" -> "), positions.get(cycle.head))
    }
  }

  private def buildAndCheckFlattenedSubtypingMaps()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    for (subtypeId <- subtypingGraph.topologicalSort().reverse) {
      val subtypeSupertypes = mutable.Map.empty[TypeIdentifier, Map[TypeIdentifier, Type]]

      def checkAndSave(name: TypeIdentifier, newSubst: Map[TypeIdentifier, Type]): Unit = {
        subtypeSupertypes.get(name) match {
          case Some(prevSubst) =>
            if (prevSubst != newSubst) {
              val supertype2Sig = resolveSignatureAs[RuntimeTypeSignature](name).get
              val conflictingType1 = supertype2Sig.toType(prevSubst, Map.empty)
              val conflictingType2 = supertype2Sig.toType(newSubst, Map.empty)
              er.reportError(s"$subtypeId subtypes both $conflictingType1 and $conflictingType2", positions.get(subtypeId))
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
        for (supertype2 <- supertype1Sig.directSupertypes) {
          val superSubst = flattenedSupertypesSubstitutions(supertype1.typeName)(supertype2.typeName)
          val composedSubst = for (tid, tpe) <- superSubst yield tid -> tpe.substitute(oneStepSubst, Map.empty)
          checkAndSave(supertype2.typeName, composedSubst)
        }
      }
      flattenedSupertypesSubstitutions(subtypeId) = subtypeSupertypes
    }
  }

  private def findMentionedTypes(tpe: Type): Set[TypeIdentifier] = tpe match {
    case Types.RefinedType(baseType, itValue, predicate) =>
      findMentionedTypes(baseType) ++ findMentionedTypes(predicate)
    case typeVar: Types.TypeVar =>
      throw AssertionError("should not happen: typeVar in typealias definition")
    case primitiveType: Types.PrimitiveType => Set.empty
    case Types.NamedType(typeName, typeParams, params) =>
      Set(typeName) ++ typeParams.flatMap(findMentionedTypes) ++ params.flatMap(findMentionedTypes)
  }

  private def findMentionedTypes(formula: Formula): Set[TypeIdentifier] = formula match {
    case value: Values.Value => Set.empty
    case op: Values.BinOp => findMentionedTypes(op.lhs) ++ findMentionedTypes(op.rhs)
    case op: Values.UnaryOp => findMentionedTypes(op.operand)
    case Values.Call(receiver, funId, args) => findMentionedTypes(receiver) ++ args.flatMap(findMentionedTypes)
    case Values.Select(owner, fieldName) => findMentionedTypes(owner)
    case Values.HasType(formula, tpe) => findMentionedTypes(formula) ++ findMentionedTypes(tpe)
  }

  extension (er: ErrorReporter) private def reportError(msg: String, posOpt: Option[Position])(using compilationStep: CompilationStep): Unit = {
    er.push(Err(compilationStep, msg, posOpt))
  }

}

object Program {

  final class Builder(er: ErrorReporter) {
    private val signatures = mutable.Map.empty[TypeIdentifier, TypeSignature]

    val globalValuesContext: GlobalValuesContext = GlobalValuesContext()

    def saveSignature(sig: TypeSignature, posOpt: Option[Position]): Unit = {
      if (PrimitiveType.values.exists(_.str == sig.id.toString)) {
        er.push(Err(SSAGeneration, s"identifier ${sig.id} is illegal since it conflicts with a primitive type", posOpt))
      } else if (signatures.contains(sig.id)) {
        er.push(Err(SSAGeneration, s"redefinition of type ${sig.id}", posOpt))
      } else {
        signatures(sig.id) = sig
      }
    }

    def build(allFunctions: Map[FunctionSignature, SSA.Function]): Program = {
      val interfacesB = Map.newBuilder[TypeIdentifier, InterfaceSignature]
      val classesB = Map.newBuilder[TypeIdentifier, ClassSignature]
      val packagesB = Map.newBuilder[TypeIdentifier, ObjectSignature]
      val datatypes = Map.newBuilder[TypeIdentifier, DatatypeSignature]
      val structsB = Map.newBuilder[TypeIdentifier, StructSignature]
      val typeAliasesB = Map.newBuilder[TypeIdentifier, TypeAliasSignature]
      for ((id, sig) <- signatures) {
        sig match {
          case sig: InterfaceSignature => interfacesB.addOne(id, sig)
          case sig: ClassSignature => classesB.addOne(id, sig)
          case sig: ObjectSignature => packagesB.addOne(id, sig)
          case sig: DatatypeSignature => datatypes.addOne(id, sig)
          case sig: StructSignature => structsB.addOne(id, sig)
          case sig: TypeAliasSignature => typeAliasesB.addOne(id, sig)
        }
      }
      Program(
        globalValuesContext,
        interfacesB.result(),
        classesB.result(),
        packagesB.result(),
        datatypes.result(),
        structsB.result(),
        typeAliasesB.result(),
        allFunctions
      )
    }
  }

}
