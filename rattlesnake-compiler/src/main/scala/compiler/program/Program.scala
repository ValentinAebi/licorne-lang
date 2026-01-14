package compiler.program

import compiler.datastructures.Graph
import compiler.irs.SSA
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.{SSAGeneration, TypeChecking}
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.enforceBaseSubtypingConstraint
import compiler.typechecking.{FunctionContext, TypeStore, Typer}
import compiler.util.zipCommons
import compiler.valuesconversion.GlobalValuesContext
import identifiers.{ThisId, TypeIdentifier}
import lang.*
import lang.Types.*
import lang.Types.PrimitiveType.{NothingType, VoidType}
import lang.Values.{And, Formula, IdValue}
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
  
  export typesReasoningCache.developUnencapsulated

  def runtimeSignatures: Iterable[RuntimeTypeSignature] = (interfaces ++ classes ++ objects ++ datatypes ++ records).values

  def allTypeSignatures: Iterable[TypeSignature] = runtimeSignatures ++ typeAliases.values

  def checkDefinitions()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
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
      _.typeParams.map((tid, _) => tid -> NamedType(tid, List.empty, List.empty)).toMap
    } else for {
      subTSupers <- flattenedSupertypesSubstitutions.get(subT)
      superSubst <- subTSupers.get(superT)
    } yield superSubst
  }
  
  def isEnumCaseOf(subId: TypeIdentifier, superId: TypeIdentifier): Boolean =
    subToSuperSubst(subId, superId).isDefined

  def desugarType(tpe: Type): Type = {
    val desugaredType = tpe match {
      case RefinedType(baseTypeRaw, itValueRaw, predicateRaw) =>
        desugarType(baseTypeRaw) match {
          case RefinedType(baseTypeDes, itValueDes, predicateDes) =>
            RefinedType(baseTypeDes, itValueRaw, And(predicateRaw, predicateDes.substitute(Map.empty, Map(itValueDes -> itValueRaw))))
          case baseTypeDes: NominalType =>
            RefinedType(baseTypeDes, itValueRaw, predicateRaw)
          case closureType: ClosureType => closureType
          case _: (UnionType | BaseUnionType | TypeVariable) => assert(false)
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
      case typeVariable: TypeVariable => typeVariable.substitutedIfResolved
      case UnionType(types) => UnionType(types.map(desugarType))
      case BaseUnionType(types) => UnionType(types.map(desugarType))
      case ClosureType(params, resultType) => ClosureType(params.map(desugarType), desugarType(resultType))
    }
    if desugaredType == tpe then tpe
    else desugarType(desugaredType)
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

  def forceComputeJoins(tpe: BaseType)(using program: Program): Option[NamedType] = tpe match {
    case namedType: NamedType => Some(namedType)
    case _: BaseUnionType => boundary {

      def extractTypeIds(tpe: BaseType): Set[TypeIdentifier] = tpe match {
        case NamedType(tid, _, _) => Set(tid)
        case BaseUnionType(types) => types.flatMap(extractTypeIds)
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
      given FunctionContext = mkTSigCheckingCtx(id, typeParams.toMap)

      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
  }

  private def checkClassSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, ClassSignature(id, typeParams, fields, importedObjects, functions, directSupertypes)) <- classes) {
      given FunctionContext = mkTSigCheckingCtx(id, typeParams.toMap)

      val posOpt = positions.get(id)
      checkFields(fields.values, posOpt)
      checkImportedObjects(importedObjects)
      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
  }

  private def checkObjectSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, ObjectSignature(id, importedObjects, functions, directSupertypes)) <- objects) {
      given FunctionContext = mkTSigCheckingCtx(id, Map.empty)

      checkImportedObjects(importedObjects)
      checkSuperinterfaces(id, directSupertypes, positions.get(id))
    }
  }

  private def checkDatatypeSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, DatatypeSignature(id, typeParams, directSupertypes, directSubtypes)) <- datatypes) {
      given FunctionContext = mkTSigCheckingCtx(id, typeParams.toMap)

      checkSupertypesOfUnencapsulated(id, directSupertypes, positions.get(id))
    }
  }

  private def checkRecordSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, RecordSignature(id, typeParams, fields, directSupertypes)) <- records) {
      given FunctionContext = mkTSigCheckingCtx(id, typeParams.toMap)

      val posOpt = positions.get(id)
      checkFields(fields.values, posOpt)
      checkSupertypesOfUnencapsulated(id, directSupertypes, posOpt)
    }
  }

  private def checkTypeAliasSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter, positions: Map[TypeIdentifier, Position]): Unit = {
    for ((_, TypeAliasSignature(id, typeParams, itValue, params, rhs)) <- typeAliases) {
      given tcCtx: FunctionContext = mkTSigCheckingCtx(id, typeParams.toMap)

      val posOpt = positions.get(id)
      for ((paramId, (paramType, paramVal)) <- params) {
        tcCtx.checkType(paramType, None, posOpt)
        ts(paramVal) = paramType
      }
      tcCtx.checkType(rhs, None, posOpt)
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

  private def checkFields(fields: Iterable[Field], posOpt: Option[Position])
                         (using tcCtx: FunctionContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    fields.foreach { field =>
      val variance = if field.isStable then Covariant else Invariant
      tcCtx.checkType(field.tpe, Some(variance), posOpt)
    }
  }

  private def checkFunctionSignatures()(using typer: Typer, ts: TypeStore, er: ErrorReporter): Unit = {
    for ((funSig@FunctionSignature(ownerName, functionName, funTypeParams, funParamsInclThis, funRetType, funVisibility), SSA.Function(_, funBodyOpt, funPosOpt)) <- functions) {
      val ownerSig = resolveSignatureAs[RuntimeTypeSignature](ownerName).get

      given tcCtx: FunctionContext = FunctionContext(this, ownerSig.typeParams.toMap, funTypeParams.toSet, funSig.receiverVal, ownerName, expectedReturnType = funRetType)

      if (funVisibility == Private && ownerSig.isInstanceOf[InterfaceSignature]) {
        reportError(s"$Private methods are not allowed in interfaces", funPosOpt)
      }
      val conflictingTypeParams = funTypeParams.intersect(ownerSig.typeParams)
      if (conflictingTypeParams.nonEmpty) {
        reportError(s"type parameter(s) ${conflictingTypeParams.mkString(",")} conflict(s) with type parameter(s) of $ownerName that have the same name(s)", funPosOpt)
      }
      ts(funSig.receiverVal) = funSig.receiverType
      for ((paramVal, paramType) <- funParamsInclThis.tail) {
        tcCtx.checkType(paramType, Some(Contravariant), funPosOpt)
        ts(paramVal) = paramType
      }
      tcCtx.checkType(funRetType, Some(Covariant), funPosOpt)
    }
  }

  private def analyzeOverrides()(using er: ErrorReporter, compilationStep: CompilationStep, typeDefPositions: Map[TypeIdentifier, Position]): Unit = {
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
                  val funTypeParamsSubst = superFunTypeParams zip subFunTypeParams.map(NamedType(_, List.empty, List.empty))
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
                  enforceBaseSubtypingConstraint(subFunRetType, expectedRetType)(using s"return type of method $funId that overrides $funId in $superT", funPosOpt, er, this)
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

  private def checkSuperinterfaces(childTypeId: TypeIdentifier, superTypes: List[NamedType], posOpt: Option[Position])
                                  (using tcCtx: FunctionContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      tcCtx.checkType(superT, Some(Covariant), posOpt)
      resolveSignature(superT.typeName).foreach {
        case _: InterfaceSignature => ()
        case _ => reportError(s"interface not found: ${superT.typeName}", posOpt)
      }
    }
  }

  private def checkSupertypesOfUnencapsulated(id: TypeIdentifier, superTypes: List[NamedType], posOpt: Option[Position])
                                             (using tcCtx: FunctionContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    for (superT <- superTypes) {
      tcCtx.checkType(superT, Some(Covariant), posOpt)
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
    case RefinedType(baseType, itValue, predicate) =>
      findMentionedTypes(baseType) ++ findMentionedTypes(predicate)
    case primitiveType: Types.PrimitiveType => Set.empty
    case NamedType(typeName, typeParams, params) =>
      Set(typeName) ++ typeParams.flatMap(findMentionedTypes) ++ params.flatMap(findMentionedTypes)
    case _: TypeVariable => Set.empty
    case UnionType(types) =>
      types.flatMap(findMentionedTypes)
    case BaseUnionType(types) =>
      types.flatMap(findMentionedTypes)
    case ClosureType(params, resultType) =>
      params.flatMap(findMentionedTypes).toSet ++ findMentionedTypes(resultType)
  }

  private def findMentionedTypes(formula: Formula): Set[TypeIdentifier] = formula match {
    case value: Values.Value => Set.empty
    case op: Values.BinOp => findMentionedTypes(op.lhs) ++ findMentionedTypes(op.rhs)
    case op: Values.UnaryOp => findMentionedTypes(op.operand)
    case Values.Call(receiver, funId, typeArgs, args) => findMentionedTypes(receiver) ++ typeArgs.flatMap(findMentionedTypes) ++ args.flatMap(findMentionedTypes)
    case Values.Select(owner, fieldName) => findMentionedTypes(owner)
    case Values.HasType(formula, tpe) => findMentionedTypes(formula) + tpe
  }

  private def mkTSigCheckingCtx(id: TypeIdentifier, typeParamsMap: Map[TypeIdentifier, Variance])(using typer: Typer, ts: TypeStore): FunctionContext = {
    FunctionContext(this, typeParamsMap, Set.empty, globalValuesContext.valuesGen.newValue(ThisId), id, expectedReturnType = VoidType)
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
