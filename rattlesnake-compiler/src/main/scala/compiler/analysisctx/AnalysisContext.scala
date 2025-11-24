package compiler.analysisctx

import compiler.datastructures.Graph
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.valuesconversion.GlobalValuesContext
import identifiers.TypeIdentifier
import lang.*
import lang.Types.{NamedType, Type}
import lang.Values.{Formula, IdValue}

import scala.collection.mutable

final case class AnalysisContext(
                                  globalValuesContext: GlobalValuesContext,
                                  interfaces: Map[TypeIdentifier, InterfaceSignature],
                                  classes: Map[TypeIdentifier, ClassSignature],
                                  objects: Map[TypeIdentifier, ObjectSignature],
                                  datatypes: Map[TypeIdentifier, DatatypeSignature],
                                  structs: Map[TypeIdentifier, StructSignature],
                                  typeAliases: Map[TypeIdentifier, TypeAliasSignature]
                                ) {

  def performTypeReferenceChecks()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    for ((_, InterfaceSignature(id, typeParams, functions, directSupertypes)) <- interfaces) {
      checkFunctionSignatures(functions.values)
      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
    for ((_, ClassSignature(id, typeParams, fields, importedObjects, functions, directSupertypes)) <- classes) {
      val posOpt = positions.get(id)
      fields.foreach { (_, field) =>
        checkTypesWellDefined(field.tpe)(using er, posOpt, compilationStep)
      }
      checkImportedObjects(importedObjects)
      checkFunctionSignatures(functions.values)
      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
    for ((_, ObjectSignature(id, importedObjects, functions, directSupertypes)) <- objects) {
      checkImportedObjects(importedObjects)
      checkFunctionSignatures(functions.values)
      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
    for ((_, DatatypeSignature(id, typeParams, directSupertypes, directSubtypes)) <- datatypes) {
      checkSupertypesOfStructLike(id, directSupertypes, positions.get(id))
    }
    for ((_, StructSignature(id, typeParams, fields, directSupertypes)) <- structs) {
      val posOpt = positions.get(id)
      fields.foreach { (_, field) =>
        checkTypesWellDefined(field.tpe)(using er, posOpt, compilationStep)
      }
      checkSupertypesOfStructLike(id, directSupertypes, posOpt)
    }
    checkSubtypingCyclicity()
    checkObjectImportsCyclicity()
    checkTypeAliasesCyclicity()
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

  private def checkFunctionSignatures(functions: Iterable[FunctionSignature])(using compilationStep: CompilationStep): Unit = {
    // TODO
  }

  private def checkSuperinterfaces(childTypeId: TypeIdentifier, superTypes: List[NamedType], posOpt: Option[Position])(using er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      checkTypesWellDefined(superT)(using er, posOpt, compilationStep)
      resolveSignature(superT.typeName) match {
        case None | Some(_: InterfaceSignature) => // case None is handled by checkTypesWellDefined
        case Some(_) => er.reportError(s"interface not found: ${superT.typeName}", posOpt)
      }
    }
  }

  private def checkSupertypesOfStructLike(id: TypeIdentifier, superTypes: List[TypeIdentifier], posOpt: Option[Position])(using er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    superTypes.foreach { superT =>
      resolveSignature(superT) match {
        case Some(DatatypeSignature(superTypeId, _, _, subOfSuper)) =>
          if (!subOfSuper.contains(id)) {
            er.reportError(s"$id cannot extend $superTypeId since they are defined in distinct source files", posOpt)
          }
        case _ =>
          er.reportError(s"datatype not found: $superT", posOpt)
      }
    }
  }

  private def checkExists(typeId: TypeIdentifier)(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    resolveSignature(typeId) match {
      case Some(value) => ???
      case None => ???
    }
  }

  def resolveSignature(typeId: TypeIdentifier): Option[TypeSignature] =
    (interfaces.get(typeId)
      orElse classes.get(typeId)
      orElse objects.get(typeId)
      orElse datatypes.get(typeId)
      orElse structs.get(typeId))

  private def checkTypesWellDefined(tpe: Type)(using er: ErrorReporter, posOpt: Option[Position], compilationStep: CompilationStep): Unit = tpe match {
    case Types.RefinedType(baseType, itValue, predicate) =>
      checkTypesWellDefined(baseType)
      checkTypesWellDefined(predicate)
    case typeVar: Types.TypeVar =>
      throw AssertionError("should not happen: unexpected type variable")
    case primitiveType: Types.PrimitiveType => ()
    case NamedType(typeName, typeParams, params, isPure) =>
      resolveSignature(typeName) match {
        case None =>
          er.reportError(s"type not found: $typeName", posOpt)
        case Some(sig) =>
          if (typeParams.size != sig.typeParams.size) {
            er.reportError(s"expected ${sig.typeParams.size} type arguments, found ${typeParams.size}", posOpt)
          }
          if (params.size != sig.params.size) {
            er.reportError(s"expected ${sig.params.size} arguments, found ${typeParams.size}", posOpt)
          }
      }
      typeParams.foreach(checkTypesWellDefined)
      params.foreach(checkTypesWellDefined)
  }

  private def checkTypesWellDefined(formula: Formula)(using er: ErrorReporter, posOpt: Option[Position], compilationStep: CompilationStep): Unit = formula match {
    case _: Values.Value => ()
    case op: Values.BinOp =>
      checkTypesWellDefined(op.lhs)
      checkTypesWellDefined(op.rhs)
    case op: Values.UnaryOp =>
      checkTypesWellDefined(op.operand)
    case Values.Call(receiver, funId, args) =>
      checkTypesWellDefined(receiver)
      args.foreach(checkTypesWellDefined)
    case Values.Select(owner, fieldName) => checkTypesWellDefined(owner)
    case Values.HasType(formula, tpe) =>
      checkTypesWellDefined(formula)
      checkTypesWellDefined(tpe)
  }

  private def checkSubtypingCyclicity()(using er: ErrorReporter, positions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for ((id, sig) <- interfaces ++ classes ++ objects) {
      graphB.addVertex(id)
      graphB.addDescendants(id, sig.directSupertypes.map(_.typeName))
    }
    for ((id, sig) <- datatypes ++ structs) {
      graphB.addVertex(id).addDescendants(id, sig.directSupertypes)
    }
    graphB.build().findShortestCycle().foreach { cycle =>
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

  private def findMentionedTypes(tpe: Type): Set[TypeIdentifier] = tpe match {
    case Types.RefinedType(baseType, itValue, predicate) =>
      findMentionedTypes(baseType) ++ findMentionedTypes(predicate)
    case typeVar: Types.TypeVar =>
      throw AssertionError("should not happen: typeVar in typealias definition")
    case primitiveType: Types.PrimitiveType => Set.empty
    case Types.NamedType(typeName, typeParams, params, isPure) =>
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

object AnalysisContext {

  final class Builder(er: ErrorReporter) {
    private val signatures = mutable.Map.empty[TypeIdentifier, TypeSignature]

    val globalValuesContext: GlobalValuesContext = GlobalValuesContext()

    def saveSignature(sig: TypeSignature, posOpt: Option[Position]): Unit = {
      if (signatures.contains(sig.id)) {
        er.push(Err(SSAGeneration, s"redefinition of type ${sig.id}", posOpt))
      } else {
        signatures(sig.id) = sig
      }
    }

    def build(): AnalysisContext = {
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
      AnalysisContext(
        globalValuesContext,
        interfacesB.result(),
        classesB.result(),
        packagesB.result(),
        datatypes.result(),
        structsB.result(),
        typeAliasesB.result()
      )
    }
  }

}
