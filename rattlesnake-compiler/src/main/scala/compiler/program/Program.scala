package compiler.program

import compiler.datastructures.Graph
import compiler.irs.SSA
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.SubtypeRelation.enforceSubtypingConstraint
import compiler.typechecking.{RefinementConstraint, TypeCheckingContext}
import compiler.valuesconversion.GlobalValuesContext
import identifiers.TypeIdentifier
import lang.*
import lang.Types.*
import lang.Values.{And, Formula, IdValue}
import lang.Variance.*

import java.util
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
                          functions: Map[FunctionSignature, SSA.Function],
                          formulaPositions: util.IdentityHashMap[Formula, Position]
                        ) {
  private val subtypingGraph: Graph[TypeIdentifier] = buildSubtypingGraph()
  private val flattenedSupertypesSubstitutions = mutable.Map.empty[TypeIdentifier, mutable.Map[TypeIdentifier, Map[TypeIdentifier, Type]]]
  
  val constraintsCollector = RefinementConstraint.Collector()

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
    checkOverrides()
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

  def subToSuperSubst(subT: TypeIdentifier, superT: TypeIdentifier): Option[Map[TypeIdentifier, Type]] = {
    if subT == superT then resolveSignatureAs[RuntimeTypeSignature](subT).map {
      _.typeParams.map((tid, _) => tid -> NamedType(tid, List.empty, List.empty)).toMap
    } else for {
      subTSupers <- flattenedSupertypesSubstitutions.get(subT)
      superSubst <- subTSupers.get(superT)
    } yield superSubst
  }

  def desugarType(tpe: Type): Type = {
    val desugaredType = tpe match {
      case RefinedType(baseTypeRaw, itValueRaw, predicateRaw) =>
        desugarType(baseTypeRaw) match {
          case RefinedType(baseTypeDes, itValueDes, predicateDes) =>
            RefinedType(baseTypeDes, itValueRaw, And(predicateRaw, predicateDes.substitute(Map.empty, Map(itValueDes -> itValueRaw))))
          case baseTypeDes: BaseType =>
            RefinedType(baseTypeDes, itValueRaw, predicateRaw)
        }
      case primitiveType: Types.PrimitiveType => primitiveType
      case NamedType(typeName, typeArgsRaw, args) =>
        val typeArgsSubst = typeArgsRaw.map(desugarType)
        typeAliases.get(typeName) match {
          case Some(TypeAliasSignature(id, typeParams, thisValue, params, rhs)) =>
            val typesSubst =
              typeParams.map((id, variance) => id)
                .zipCommons(typeArgsSubst)
                .toMap
            val valsSubst = params.map {
              case (paramId, (paramType, paramVal)) => paramVal
            }.zipCommons(args).toMap
            desugarType(rhs.substitute(typesSubst, valsSubst))
          case None => NamedType(typeName, typeArgsSubst, args)
        }
    }
    if desugaredType == tpe then tpe
    else desugarType(desugaredType)
  }

  extension [T](l: Iterable[T]) private def zipCommons[U](r: Iterable[U]): Iterable[(T, U)] =
    l.take(r.size).zip(r.take(l.size))

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
      val variance = if field.isStable then Covariant else Invariant
      tcCtx.checkTypesWellDefined(field.tpe, Some(variance), posOpt)
    }
  }

  private def checkFunctionSignatures()(using er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for ((funSig@FunctionSignature(ownerName, functionName, funTypeParams, funParamsInclThis, funRetType, funVisibility), SSA.Function(_, funBodyOpt, funPosOpt)) <- functions) {
      val ownerSig = resolveSignatureAs[RuntimeTypeSignature](ownerName).get

      given tcCtx: TypeCheckingContext = TypeCheckingContext(this, ownerSig.typeParams.toMap, funTypeParams.toSet)

      val conflictingTypeParams = funTypeParams.intersect(ownerSig.typeParams)
      if (conflictingTypeParams.nonEmpty) {
        er.reportError(s"type parameters ${conflictingTypeParams.mkString(",")} conflict with type parameters of $ownerName", funPosOpt)
      }
      for ((paramId, paramType) <- funParamsInclThis.tail) {
        tcCtx.checkTypesWellDefined(paramType, Some(Contravariant), funPosOpt)
      }
      tcCtx.checkTypesWellDefined(funRetType, Some(Covariant), funPosOpt)
    }
  }

  private def checkOverrides()(using er: ErrorReporter, typeDefPositions: Map[TypeIdentifier, Position], compilationStep: CompilationStep): Unit = {
    for ((subT, subTSupertypes) <- flattenedSupertypesSubstitutions; (superT, typeTypeParamsSubst) <- subTSupertypes) {
      val subTSig = resolveSignature(subT).get
      val superTSig = resolveSignature(superT).get
      (subTSig, superTSig) match {
        case (subTSig: EncapsulatedTypeSignature, superTSig: EncapsulatedTypeSignature) =>
          for ((funId, superFunSig@FunctionSignature(_, _, superFunTypeParams, superFunParams, superFunRetType, superFunVisibility)) <- superTSig.functions) {
            subTSig.functions.get(funId) match {
              case None =>
                er.reportError(s"$subT does not implement method $funId declared in its supertype $superT", typeDefPositions.get(subT))
              case Some(subFunSig@FunctionSignature(_, _, subFunTypeParams, subFunParams, subFunRetType, subFunVisibility)) =>
                val funPosOpt = functions.get(subFunSig).flatMap(_.posOpt)
                val typeParamsLenMatch = subFunTypeParams.size == superFunTypeParams.size
                val paramsLenMatch = subFunParams.size == superFunParams.size
                if (!typeParamsLenMatch) {
                  er.reportError(s"length of type parameters list in method $funId in $subT does not match its length in its supertype $superT", funPosOpt)
                }
                if (!paramsLenMatch) {
                  er.reportError(s"length of parameters list in method $funId in $subT does not match its length in its supertype $superT", funPosOpt)
                }
                if (typeParamsLenMatch && paramsLenMatch) {
                  val funTypeParamsSubst = superFunTypeParams zip subFunTypeParams.map(NamedType(_, List.empty, List.empty))
                  val typeParamsSubst = typeTypeParamsSubst ++ funTypeParamsSubst
                  val valsSubst = mutable.Map.empty[IdValue, IdValue]
                  // TODO do not forget to check refinements on the receiver (the base type is not checked here)
                  val superTSubst = superTSig.toType(typeParamsSubst, Map.empty)
                  for (((subParamVal, subParamType), (superParamVal, superParamType)) <- subFunParams.tail zip superFunParams.tail) {
                    val expectedSubParamType = superParamType.substitute(typeParamsSubst, valsSubst.toMap)
                    if (subParamType != expectedSubParamType) {
                      val paramNameIfKnown =
                        globalValuesContext.debugInfoOf(subParamVal)
                          .flatMap(_.referencedSourceId)
                          .map(" " + _)
                          .getOrElse("")
                      er.reportError(s"type mismatch on parameter$paramNameIfKnown of method $funId: " +
                        s"type is $subParamType but should be $expectedSubParamType since the method overrides $funId in $superTSubst", funPosOpt)
                    }
                    valsSubst(superParamVal) = subParamVal
                  }
                  val expectedRetType = superFunRetType.substitute(typeParamsSubst, valsSubst.toMap)
                  enforceSubtypingConstraint(subFunRetType, expectedRetType)(using s"return type of method $funId that overrides $funId in $superT", funPosOpt, er, this)
                }
                if (!subFunVisibility.eqOrMorePermissive(superFunVisibility)) {
                  er.reportError(s"$funId in $subT overrides $funId in $superT but has a more restricted visibility", funPosOpt)
                }
            }
          }
        case _ => ()
      }
    }
  }

  private def checkSuperinterfaces(childTypeId: TypeIdentifier, superTypes: List[NamedType], posOpt: Option[Position])
                                  (using tcCtx: TypeCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      tcCtx.checkTypesWellDefined(superT, Some(Covariant), posOpt)
      resolveSignature(superT.typeName).foreach {
        case _: InterfaceSignature => ()
        case _ => er.reportError(s"interface not found: ${superT.typeName}", posOpt)
      }
    }
  }

  private def checkSupertypesOfStructLike(id: TypeIdentifier, superTypes: List[NamedType], posOpt: Option[Position])
                                         (using tcCtx: TypeCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      tcCtx.checkTypesWellDefined(superT, Some(Covariant), posOpt)
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
    case RefinedType(baseType, itValue, predicate) =>
      findMentionedTypes(baseType) ++ findMentionedTypes(predicate)
    case primitiveType: Types.PrimitiveType => Set.empty
    case NamedType(typeName, typeParams, params) =>
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

    def build(allFunctions: Map[FunctionSignature, SSA.Function],
              formulaPositions: util.IdentityHashMap[Formula, Position]): Program = {
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
        allFunctions,
        formulaPositions
      )
    }
  }

}
