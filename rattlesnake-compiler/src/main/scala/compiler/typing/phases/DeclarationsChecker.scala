package compiler.typing.phases

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.irs.SSA
import compiler.lang.Formulas.IdValue
import compiler.lang.Types.Type
import compiler.lang.Variance.{Covariant, Invariant}
import compiler.lang.*
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.TypeStore
import compiler.typing.contexts.SubtypingContext.SupertypesSubst

import scala.collection.mutable

final class DeclarationsChecker(private val er: ErrorReporter) extends CompilerStep[(Program, TypeStore), (Program, TypeStore)] {

  override def apply(input: (Program, TypeStore)): (Program, TypeStore) = {
    val (program, ts) = input

    val flattenedSupertypesSubstitutions: SupertypesSubst = mutable.LinkedHashMap.empty
    val subtypingGraph = buildSubtypingGraph(program)
    
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
    input
  }

  private def buildSubtypingGraph(program: Program): Graph[TypeIdentifier] = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for (sig <- program.runtimeSignatures) {
      val id = sig.id
      graphB.addVertex(id)
      graphB.addDescendants(id, sig.directSupertypes.map(_.typeName))
    }
    graphB.build()
  }

  private def checkInterfaceSignatures(): Unit = {
    for ((_, InterfaceSignature(id, typeParams, functions, directSupertypes)) <- interfaces) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      checkSuperinterfaces(id, directSupertypes)
    }
  }

  private def checkClassSignatures(): Unit = {
    for ((_, ClassSignature(id, typeParams, fields, importedObjects, functions, directSupertypes)) <- classes) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      val posOpt = positions.get(id)
      checkFields(fields.values)
      checkImportedObjects(importedObjects)
      checkSuperinterfaces(id, directSupertypes)
    }
  }

  private def checkObjectSignatures(): Unit = {
    for ((_, ObjectSignature(id, importedObjects, functions, directSupertypes)) <- objects) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, Set.empty)

      checkImportedObjects(importedObjects)
      checkSuperinterfaces(id, directSupertypes)
    }
  }

  private def checkDatatypeSignatures(): Unit = {
    for ((_, DatatypeSignature(id, typeParams, directSupertypes, directSubtypes)) <- datatypes) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      checkSupertypesOfUnencapsulated(id, directSupertypes)
    }
  }

  private def checkRecordSignatures(): Unit = {
    for ((_, RecordSignature(id, typeParams, fields, directSupertypes)) <- records) {
      given Option[Position] = positions.get(id)

      given FunctionContext = checkTypeParamsAndMkTSigCheckingCtx(id, typeParams)

      checkFields(fields.values)
      checkSupertypesOfUnencapsulated(id, directSupertypes)
    }
  }

  private def checkTypeAliasSignatures(): Unit = {
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

  private def checkImportedObjects(importedObjects: mutable.LinkedHashSet[IdValue]): Unit = {
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

  private def checkFunctionSignatures(program: Program): Unit = {
    for ((funSig@FunctionSignature(ownerName, functionName, funTypeParams, funParamsInclThis, funRetType, funVisibility, declPosOpt), SSA.Function(_, funBodyOpt, funPosOpt)) <- program.functions) {
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
  
}
