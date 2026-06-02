package compiler.ssagen

import compiler.identifiers.{FunOrVarId, ItId, ThisId, TypeIdentifier}
import compiler.irs.asts.Asts
import compiler.irs.asts.Asts.{EncapsulatedTypeDefTree, Expr, ImportStat, ObjectDef, Source, VariableRef}
import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.SSA.*
import compiler.irs.ssa.{ClosureTypingTarget, FieldResolutionTarget, FormulasDsl, InvocationTarget, SSA}
import compiler.lang.*
import compiler.lang.Field.{ReassignableField, StableField}
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{BoolType, UnitType}
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.recurrences.Recurrence
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.ssagen.ImportsScanner.PackagesInfo
import compiler.typing.contexts.TypeParamsContext.processTypeParamsAccumulating
import compiler.typing.contexts.{TypeParamsContext, TypeVariablesContext}
import compiler.util.{SeqSet, javaIterToList}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.LocalValuesContext
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized

import java.io.File
import java.nio.file.Path
import scala.collection.{SeqMap, mutable}


// FIXME code following loops and disjunctions should be made a subscope of the current scope
final class SSAGenerator(typeVarsCtx: TypeVariablesContext, proxyStore: ProxyStore, er: ErrorReporter, srcRootsForPkgMismatchCheckOpt: Option[List[Path]]) extends CompilerStep[(List[Asts.Source], PackagesInfo), Program] {

  private type SeqMapBuilder[A, B] = mutable.Builder[(A, B), SeqMap[A, B]]

  private given CompilationStep = CompilationStep.SSAGeneration

  override def apply(input: (List[Asts.Source], PackagesInfo)): Program = {
    val (sources, packagesInfo) = input

    given List[Source] = sources

    given PackagesInfo = packagesInfo

    val programBuilder = Program.Builder(er, proxyStore)
    val globalScope = programBuilder.globalValuesContext.globalScope
    val allFunctionsB = SeqMap.newBuilder[(TypeIdentifier, FunOrVarId), SSA.Function]
    val loopsCollector = mutable.ListBuffer.empty[SSA.Loop]
    for (src <- sources) {
      src.pkgDeclOpt.foreach { pkgDecl =>
        checkPackageAndPosition(pkgDecl)
      }
      for (importStat <- src.imports) {
        checkImport(importStat, packagesInfo)
      }
      val currentPackagePrefix = src.pkgDeclOpt.map(_.nameParts).getOrElse(List.empty)
      val datatypeDefs = mutable.ListBuffer.empty[(List[String], Asts.DataTypeDef)]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        val typeId = TypeIdentifier(currentPackagePrefix, df.name)
        df match {
          case df@Asts.InterfaceDef(_, typeParamTrees, functions, directSupertypes) =>

            given ImportsContext = createImportsCtx(src, Some(df))

            val interfaceSigScope = Scope.nestedInside(globalScope, df)
            val thisValue = interfaceSigScope.newParam(ThisId, df.getPosition)
            interfaceSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, interfaceSigScope, ReassigPermission.Val, None)
            val (typeParams, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamTrees) {
              convertTypeTypeParam(_, interfaceSigScope)
            }

            given TypeParamsContext = fullTypeParamsCtx

            val noFunctionsSig = InterfaceSignature(typeId, typeParams, Map.empty, directSupertypes.map(mkNamedType(_, interfaceSigScope)), interfaceSigScope, df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsB)(using loopsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = true)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)

          case df@Asts.ObjectDef(_, functions, directSupertypes) =>

            given ImportsContext = createImportsCtx(src, Some(df))

            given TypeParamsContext = TypeParamsContext.empty

            val objSigScope = Scope.nestedInside(globalScope, df)
            val thisValue = objSigScope.newParam(ThisId, df.getPosition)
            objSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, objSigScope, ReassigPermission.Val, None)
            val noFunctionsSig = ObjectSignature(typeId, Map.empty, directSupertypes.map(mkNamedType(_, objSigScope)), objSigScope, df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsB)(using loopsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)

          case df@Asts.ClassDef(_, typeParamTrees, params, functions, directSupertypes) =>

            given ImportsContext = createImportsCtx(src, Some(df))

            val classSigScope = Scope.nestedInside(globalScope, df)
            val thisValue = classSigScope.newParam(ThisId, df.getPosition)
            classSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, classSigScope, ReassigPermission.Val, None)
            val (typeParams, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamTrees) {
              convertTypeTypeParam(_, classSigScope)
            }

            given TypeParamsContext = fullTypeParamsCtx

            val fields = mutable.LinkedHashMap.empty[FunOrVarId, Field]

            def saveNonReassigParam(param: Asts.SimpleParam | Asts.PublicParam): Unit = {
              val isPublishedAsMethod = param.isInstanceOf[Asts.PublicParam]
              val paramId = param.paramId
              val paramTypeTree = param.paramTypeTree
              val fieldValue = classSigScope.newParam(paramId, param.getPosition)
              val paramType = mkType(paramTypeTree, classSigScope)
              mustNotBeUnit(paramType, param.getPosition)
              fields(paramId) = StableField(paramId, paramType, fieldValue, isPublishedAsMethod)
              classSigScope.getLocalValuesContextUnsafe.saveNewLocal(paramId, fieldValue, classSigScope, ReassigPermission.Val, Some(paramType))
            }

            params.foreach {
              case param@Asts.VarParam(paramId, paramTypeTree) =>
                val paramType = mkType(paramTypeTree, classSigScope)
                mustNotBeUnit(paramType, param.getPosition)
                fields(paramId) = ReassignableField(paramId, paramType)
              case param: (Asts.SimpleParam | Asts.PublicParam) =>
                saveNonReassigParam(param)
            }
            val noFunctionsSig = ClassSignature(typeId, typeParams, SeqMap.from(fields), Map.empty, directSupertypes.map(mkNamedType(_, classSigScope)), classSigScope, df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsB)(using loopsCollector)
            val targetsToResolve = generatePublicFieldsAccessors(typeId, df, fields, functionsMap, globalScope, computeThisType(noFunctionsSig), allFunctionsB)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val classSig = noFunctionsSig.copy(functions = funcs)
            for ((target, tpe) <- targetsToResolve) {
              target.resolve(classSig, tpe)
            }
            programBuilder.saveSignature(classSig, df.getPosition)

          case df: Asts.DataTypeDef =>
            datatypeDefs.addOne(currentPackagePrefix, df)

          case df@Asts.RecordDef(_, typeParamTrees, fields, directSupertypes) =>

            given importsCtx: ImportsContext = createImportsCtx(src, None)

            val recordSigScope = Scope.nestedInside(globalScope, df)
            val thisValue = recordSigScope.newParam(ThisId, df.getPosition)
            recordSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, recordSigScope, ReassigPermission.Val, None)
            val (typeParams, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamTrees) {
              convertTypeTypeParam(_, recordSigScope)
            }

            given TypeParamsContext = fullTypeParamsCtx

            val stableFields = mutable.LinkedHashMap.empty[FunOrVarId, StableField]
            fields.foreach {
              case param@Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = recordSigScope.newParam(paramId, param.getPosition)
                val fieldType = mkType(paramTypeTree, recordSigScope)
                mustNotBeUnit(fieldType, param.getPosition)
                stableFields(paramId) = StableField(paramId, fieldType, fieldValue, isPublishedAsMethod = false)
                recordSigScope.getLocalValuesContextUnsafe.saveNewLocal(paramId, fieldValue, recordSigScope, ReassigPermission.Val, Some(fieldType))
            }
            val sig = RecordSignature(typeId, typeParams, SeqMap.from(stableFields), directSupertypes.map(mkNamedType(_, recordSigScope)), recordSigScope, df.getPosition)
            programBuilder.saveSignature(sig, df.getPosition)
            for (superT <- directSupertypes) {
              val superTId = importsCtx.applyImports(superT.name)
              datatypeSubtypes.getOrElseUpdate(superTId, mutable.LinkedHashSet.empty).addOne(typeId)
            }
          case df@Asts.TypeAliasDef(_, typeParamTrees, params, rhs) =>

            given ImportsContext = createImportsCtx(src, None)

            val typeAliasSigScope = Scope.nestedInside(globalScope, df)
            val (typeParams, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamTrees) {
              convertTypeTypeParam(_, typeAliasSigScope)
            }

            given TypeParamsContext = fullTypeParamsCtx

            val typeAliasParams = mutable.LinkedHashMap.empty[FunOrVarId, (Type, IdValue)]
            params.foreach {
              case param@Asts.SimpleParam(paramId, paramTypeTree) =>
                val paramValue = typeAliasSigScope.newParam(paramId, param.getPosition)
                val paramType = mkType(paramTypeTree, typeAliasSigScope)
                typeAliasParams(paramId) = (paramType, paramValue)
                typeAliasSigScope.getLocalValuesContextUnsafe.saveNewLocal(paramId, paramValue, typeAliasSigScope, ReassigPermission.Val, Some(paramType))
            }
            val sig = TypeAliasSignature(typeId, typeParams, SeqMap.from(typeAliasParams), mkType(rhs, typeAliasSigScope), typeAliasSigScope, df.getPosition)
            programBuilder.saveSignature(sig, df.getPosition)
        }
      }
      for ((pkgPrefix, df@Asts.DataTypeDef(datatypeName, typeParamTrees, directSupertypes)) <- datatypeDefs) {

        given ImportsContext = createImportsCtx(src, None)

        val id = TypeIdentifier(pkgPrefix, datatypeName)
        val datatypeSigScope = Scope.nestedInside(globalScope, df)
        val thisValue = datatypeSigScope.newParam(ThisId, df.getPosition)
        datatypeSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, datatypeSigScope, ReassigPermission.Val, None)
        val (typeParams, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamTrees) {
          convertTypeTypeParam(_, datatypeSigScope)
        }

        given TypeParamsContext = fullTypeParamsCtx

        val subtypes = SeqSet(datatypeSubtypes.getOrElse(id, mutable.LinkedHashSet.empty))
        val sig = DatatypeSignature(id, typeParams, directSupertypes.map(mkNamedType(_, datatypeSigScope)),
          subtypes, datatypeSigScope, df.getPosition)
        programBuilder.saveSignature(sig, df.getPosition)
      }
    }
    val program = programBuilder.build(allFunctionsB.result(), loopsCollector.toSeq)
    for (tv <- globalScope.globalValuesCtx.getTypeVariables) {
      typeVarsCtx.saveTypeVariable(tv)
    }
    er.displayAndTerminateIfErrors()
    program
  }

  private def createImportsCtx(source: Source, currEncapsulatedTypeOpt: Option[EncapsulatedTypeDefTree])
                              (using allSources: List[Source], packagesInfo: PackagesInfo): ImportsContext = {
    val localFunctions = currEncapsulatedTypeOpt.toSet.flatMap(_.functions.map(_.id))
    val typeImports = mutable.LinkedHashMap.empty[String, TypeIdentifier]
    val funcImports = mutable.LinkedHashMap.empty[FunOrVarId, (TypeIdentifier, FunOrVarId)]
    for (importStat <- source.imports) {
      importStat match {
        case Asts.TypeImportStat(imported, aliasOpt) =>
          val key = aliasOpt.getOrElse(imported.nonPrefixedId)
          if (typeImports.contains(key)) {
            reportError(s"$key conflicts with a previous import", importStat.getPosition)
          } else {
            typeImports.put(key, imported)
          }
        case Asts.FunctionsImportStat(receiverObj, importedFunctionsOrWildcard) =>
          val importedFunctions = importedFunctionsOrWildcard.getOrElse {
            for {
              pkgMap <- packagesInfo.get(receiverObj.prefixes).toList
              (_, df) <- pkgMap
              if df.isInstanceOf[Asts.EncapsulatedTypeDefTree]
              funDef <- df.asInstanceOf[Asts.EncapsulatedTypeDefTree].functions
            } yield funDef.id -> None
          }
          for ((funId, aliasOpt) <- importedFunctions) {
            val key = aliasOpt.getOrElse(funId)
            if (funcImports.contains(key)) {
              reportError(s"$key conflicts with a previous import", importStat.getPosition)
            } else if (!localFunctions.contains(key)) {
              funcImports.put(key, (receiverObj, funId))
            }
          }
      }
    }

    source.pkgDeclOpt.foreach { currPkgDecl =>
      // import types from this package
      val currPkgPrefix = source.pkgDeclOpt.map(_.nameParts).getOrElse(List.empty)
      for {
        // TODO can be optimized (by not traversing the whole list of files)
        s <- allSources
        if s.pkgDeclOpt.contains(currPkgDecl)
        df <- s.defs
      } {
        // prioritize explicit imports
        if (!typeImports.contains(df.name)) {
          typeImports.put(df.name, TypeIdentifier(currPkgPrefix, df.name))
        }
      }
    }

    ImportsContext(SeqMap.from(typeImports), SeqMap.from(funcImports))
  }

  private def checkImport(importStat: ImportStat, packagesInfo: PackagesInfo): Unit = {

    def locateObject(tid: TypeIdentifier, posOpt: Option[Position]): Option[Asts.TopLevelDef] = {
      val TypeIdentifier(prefixes, nonPrefixedId) = tid
      packagesInfo.get(prefixes) match {
        case Some(pkgDefs) =>
          pkgDefs.get(nonPrefixedId) match {
            case someDef@Some(_) => someDef
            case None =>
              reportError(s"type not found: $tid", posOpt)
              None
          }
        case None =>
          reportError(s"package not found: ${prefixes.mkString(".")}", posOpt)
          None
      }
    }

    importStat match {
      case Asts.FunctionsImportStat(tid, funIdsWithAliasOpt) =>
        for {
          funIdsWithAlias <- funIdsWithAliasOpt
          (funId, aliasOpt) <- funIdsWithAlias
        } {
          locateObject(tid, importStat.getPosition) match {
            case Some(df: ObjectDef) =>
              if (!df.functions.exists(_.id == funId)) {
                reportError(s"method $funId not found in type ${df.name}", importStat.getPosition)
              }
            case Some(df) =>
              reportError(s"${df.name} is not an object", importStat.getPosition)
            case None =>
              // already reported
              ()
          }
        }
      case Asts.TypeImportStat(tid, aliasOpt) =>
        locateObject(tid, importStat.getPosition)
    }
  }

  private def checkPackageAndPosition(pkgStat: Asts.PackageDecl): Unit = srcRootsForPkgMismatchCheckOpt.foreach { srcRoots =>
    val pkgPrefix = pkgStat.nameParts.mkString(".")
    pkgStat.getPosition match {
      case Some(pos) =>
        val filePath = new File(pos.srcCodeProviderName).toPath
        srcRoots.find(filePath.startsWith) match {
          case Some(srcRootPath) =>
            val srcRoot = javaIterToList(srcRootPath.iterator())
            val fileLocation = javaIterToList(filePath.iterator())
            val diff = fileLocation.drop(srcRoot.size)
            if (diff != pkgStat.nameParts) {
              warn("file location does not match its declared package", pkgStat.getPosition)
            }
          case None =>
            warn("file is not located in a source directory", pkgStat.getPosition)
        }
      case None =>
        warn(s"missing source file information for file in package $pkgPrefix", None)
    }
  }

  private def generatePublicFieldsAccessors(
                                             classId: TypeIdentifier,
                                             classDef: Asts.ClassDef,
                                             fields: Iterable[(FunOrVarId, Field)],
                                             functionsMap: mutable.SeqMap[FunOrVarId, (FunctionSignature, Function)],
                                             globalScope: Scope,
                                             thisType: Type,
                                             allFunctionsCollector: SeqMapBuilder[(TypeIdentifier, FunOrVarId), SSA.Function]
                                           ): Iterable[(FieldResolutionTarget, Type)] = {
    val targetsToResolve = mutable.ListBuffer.empty[(FieldResolutionTarget, Type)]
    fields.foreach {
      case (_, fld@StableField(fieldId, fieldType, fieldVal, isPublishedAsMethod)) if isPublishedAsMethod =>
        functionsMap.get(fieldId) match {
          case Some(funSig, funScope) =>
            er.reportError(s"method ${funSig.functionName} conflicts with compiler-generated accessor of ${Visibility.Public} field $fieldId", funSig.declPosOpt)
          case None =>
            val syntheticFunSigScope = Scope.nestedInside(globalScope, classDef)
            val thisValue = syntheticFunSigScope.newParam(ThisId, classDef.getPosition)
            val syntheticFunSig = FunctionSignature(classId, fieldId, List.empty, SeqMap(thisValue -> thisType),
              precondOpt = None, fieldType, syntheticFunSigScope, Visibility.Public, Purity.Pure, isMain = false, classDef.getPosition, isSynthetic = true)
            val syntheticFuncBody = Scope.nestedInside(syntheticFunSigScope, classDef)
            val syntheticFunc = SSA.Function(classId, fld.id, Some(syntheticFuncBody))
            val retVal = syntheticFunSigScope.newIntermediate("ret")
            val resolTarget = FieldResolutionTarget(fieldId)
            targetsToResolve.addOne(resolTarget -> fieldType)
            syntheticFuncBody.instructions.addOne(FieldRead(retVal, thisValue, resolTarget))
            syntheticFuncBody.instructions.addOne(Return(retVal))
            functionsMap.put(fld.id, (syntheticFunSig, syntheticFunc))
            allFunctionsCollector.addOne(syntheticFunSig.ownerAndName -> syntheticFunc)
        }
      case _ => ()
    }
    targetsToResolve
  }

  private def collectFunctions(
                                functionsProvider: Asts.EncapsulatedTypeDefTree,
                                functionsProviderIncompleteSig: EncapsulatedTypeSig,
                                globalScope: Scope,
                                allFunctionsB: SeqMapBuilder[(TypeIdentifier, FunOrVarId), SSA.Function]
                              )(using loopsCollector: mutable.ListBuffer[SSA.Loop], outerTypeParamsCtx: TypeParamsContext, importsCtx: ImportsContext): mutable.SeqMap[FunOrVarId, (FunctionSignature, SSA.Function)] = {
    val functions = mutable.LinkedHashMap.empty[FunOrVarId, (FunctionSignature, SSA.Function)]
    for (funDef <- functionsProvider.functions) {
      if (functions.contains(funDef.id)) {
        reportError(s"a function named ${funDef.id} has already been declared in ${functionsProvider.description}", funDef.getPosition)
      } else {
        val funSigScope = Scope.nestedInside(globalScope, funDef)
        val (convertedTypeParams, fullTypeParamsCtx) = processTypeParamsAccumulating(outerTypeParamsCtx, funDef.typeParams) {
          convertFunTypeParam(_, funSigScope)
        }

        given TypeParamsContext = fullTypeParamsCtx

        val paramsInclThis = mutable.LinkedHashMap.empty[NamedIdValue, Type]
        val (thisVal, thisScope) = functionsProvider match {
          case Asts.ObjectDef(_, functions, directSupertypes) =>
            (funSigScope.valuesCtx.resolveObject(functionsProviderIncompleteSig.id), globalScope)
          case _ =>
            (funSigScope.newParam(ThisId, functionsProvider.getPosition), funSigScope)
        }
        val thisParamIsOmitted = funDef.params.headOption.forall(_.paramId != ThisId)
        val isObject = functionsProvider.isInstanceOf[Asts.ObjectDef]
        if (thisParamIsOmitted) {
          val thisType = computeThisType(functionsProviderIncompleteSig)
          paramsInclThis(thisVal) = thisType
          funSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisVal, thisScope, ReassigPermission.Val, Some(thisType))
        }
        if (thisParamIsOmitted && !isObject) {
          reportError(s"parameters list of ${funDef.id} should start with the receiver parameter (syntax: 'this : Type')", funDef.getPosition)
        } else if (!thisParamIsOmitted && isObject) {
          warn("receiver parameter can be omitted inside objects", funDef.getPosition)
        }
        var isFirst = true
        for (paramTree <- funDef.params) {
          if (funSigScope.getLocalValuesContextUnsafe.knows(paramTree.paramId)) {
            reportError(s"redefinition of parameter ${paramTree.paramId}", paramTree.getPosition)
          } else {
            val paramValue = funSigScope.newParam(paramTree.paramId, paramTree.getPosition)
            val paramType = paramTree match {
              case Asts.ThisParam(paramTypeTreeOpt) =>
                if (!isFirst) {
                  reportError("receiver parameter should always be at the beginning of the parameters list", funDef.getPosition)
                }
                val expectedThisType = functionsProviderIncompleteSig.toType(Map.empty)
                paramTypeTreeOpt.map { paramTypeTree =>
                  val actualThisType = mkType(paramTypeTree, funSigScope)
                  // TODO see if we allow refined types on receiver
                  if (actualThisType != expectedThisType) {
                    reportError(s"unexpected type for receiver parameter; expected was $expectedThisType (note that it may be omitted)", funDef.getPosition)
                  }
                  actualThisType
                }.getOrElse(expectedThisType)
              case paramTree: Asts.NonThisFunctionParam =>
                mkType(paramTree.paramTypeTree, funSigScope)
            }
            mustNotBeUnit(paramType, paramTree.getPosition)
            paramsInclThis(paramValue) = paramType
            val reassigPermission = if paramTree.isInstanceOf[Asts.VarParam] then ReassigPermission.Var else ReassigPermission.Val
            funSigScope.getLocalValuesContextUnsafe.saveNewLocal(paramTree.paramId, paramValue, funSigScope, reassigPermission, Some(paramType))
          }
          isFirst = false
        }
        val retType = funDef.optRetType match {
          case Some(retTypeTree) => mkType(retTypeTree, funSigScope)
          case None => PrimitiveType.UnitType
        }
        val ownerId = functionsProviderIncompleteSig.id
        val funId = funDef.id
        val function = generateSSAFunc(ownerId, funId, funDef.bodyOpt, funSigScope, funDef.getPosition)
        val precondFormulaOpt = funDef.optPrecond.flatMap(generateFormula(_, funSigScope))
        val sig = FunctionSignature(ownerId, funId, convertedTypeParams, SeqMap.from(paramsInclThis), precondFormulaOpt, retType,
          funSigScope, funDef.visibility, funDef.purity, funDef.isMain, funDef.getPosition)
        functions(funDef.id) = (sig, function)
        allFunctionsB.addOne(sig.ownerAndName -> function)
        if (funDef.isMain && !functionsProvider.isInstanceOf[ObjectDef]) {
          reportError("main methods are only allowed in objects", funDef.getPosition)
        }
      }
    }
    er.displayAndTerminateIfErrors()
    functions
  }

  private def computeThisType(funOwnerSig: TypeSignature) = {
    val subst = funOwnerSig.typeParams.map(tp => tp.tid -> NamedType(tp.tid, List.empty, List.empty)).toMap
    funOwnerSig.toType(subst)
  }

  private def createIdToSigMapAndCheckBodyExists(functionsMap: SeqMap[FunOrVarId, (FunctionSignature, SSA.Function)],
                                                 funPos: Option[Position], isInterface: Boolean): Map[FunOrVarId, FunctionSignature] = {
    val resultB = Map.newBuilder[FunOrVarId, FunctionSignature]
    for ((id, (sig, optSSA)) <- functionsMap) {
      resultB.addOne(id -> sig)
      if (isInterface && optSSA.bodyOpt.isDefined) {
        reportError("methods declared in interfaces are not allowed to have a body", funPos)
      } else if (!isInterface && optSSA.bodyOpt.isEmpty) {
        reportError("methods declared in classes and objects must have a body", funPos)
      }
    }
    resultB.result()
  }

  private def convertTypeTypeParam(typeParam: Asts.TypeParamWithVariance, scope: Scope)(using TypeParamsContext, ImportsContext): TypeTypeParamInfo = {
    val Asts.TypeParamWithVariance(tParamName, variance, upperBoundOpt, lowerBoundOpt) = typeParam
    TypeTypeParamInfo(TypeIdentifier(List.empty, tParamName), variance, upperBoundOpt.map(mkType(_, scope)), lowerBoundOpt.map(mkType(_, scope)))
  }

  private def convertFunTypeParam(typeParam: Asts.TypeParamWithoutVariance, scope: Scope)(using TypeParamsContext, ImportsContext): FunctionTypeParamInfo = {
    val Asts.TypeParamWithoutVariance(tParamName, upperBoundOpt, lowerBoundOpt) = typeParam
    FunctionTypeParamInfo(TypeIdentifier(List.empty, tParamName), upperBoundOpt.map(mkType(_, scope)), lowerBoundOpt.map(mkType(_, scope)))
  }

  private def generateSSAFunc(
                               owner: TypeIdentifier,
                               funId: FunOrVarId,
                               bodyOpt: Option[Asts.Block],
                               funSigScope: Scope,
                               posOpt: Option[Position]
                             )(using loopsCollector: mutable.ListBuffer[SSA.Loop], importsCtx: ImportsContext, typeParamsCtx: TypeParamsContext): SSA.Function = bodyOpt match {
    case Some(body) =>
      val funScope = Scope.nestedInside(funSigScope, body)
      for (stat <- body.stats) {
        generateSSA(stat, funScope, newScopeIfBlock = false)(using ReturnCollector.doNothingCollector, FunctionInfo(funSigScope))
      }
      SSA.Function(owner, funId, Some(funScope))
    case None =>
      SSA.Function(owner, funId, None)
  }

  private def generateSSA(stat: Asts.Statement, currScope: Scope, newScopeIfBlock: Boolean)
                         (using returnCollector: ReturnCollector, currFuncInfo: FunctionInfo, loopsCollector: mutable.ListBuffer[SSA.Loop],
                          importsCtx: ImportsContext, typeParamsCtx: TypeParamsContext): Unit = {
    currScope.getLocalValuesContextUnsafe.reportHasExitedIfNeeded(er, stat.getPosition)
    stat match {

      case expr: Asts.Expr =>
        val resultValue = currScope.newIntermediate("dummy")
        generateSSAExpr(resultValue, expr, currScope)
        currScope.saveInstr(Drop(resultValue), expr)

      case block@Asts.Block(stats) =>
        val blockScope = if (newScopeIfBlock) {
          val sc = Scope.nestedInside(currScope, block)
          currScope.saveInstr(sc, block)
          sc
        } else currScope
        for (stat <- stats) {
          generateSSA(stat, blockScope, newScopeIfBlock = true)
        }

      case localDef@Asts.LocalDef(localName, typeAnnotTreeOpt, rhsOpt, reassigPermission) =>
        val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, currScope))
        typeAnnotOpt.foreach {
          case UnitType =>
            warn(s"value of type $UnitType", localDef.getPosition)
          case _ => ()
        }
        if (currScope.getLocalValuesContextUnsafe.knows(localName)) {
          reportError(s"$localName is already defined in this scope", stat.getPosition)
        } else rhsOpt match {
          case Some(rhs) =>
            generateSSA(localDef.copy(rhsOpt = None).withDesugaringSource(localDef), currScope, newScopeIfBlock)
            generateSSA(Asts.VarAssig(Asts.VariableRef(localName).withDesugaringSource(localDef), typeAnnotOpt = None, rhs)
              .withDesugaringSource(localDef), currScope, newScopeIfBlock)
          case None =>
            currScope.getLocalValuesContextUnsafe.saveNewLocal(localName, None, currScope, reassigPermission, typeAnnotOpt)
            typeAnnotOpt.foreach { typeAnnot =>
              val localDecl = LocalDecl(localName, typeAnnot)
              currScope.saveInstr(localDecl, localDef)
              currScope.getLocalValuesContextUnsafe.valueOf(localName).setDecl(localDecl)
            }
        }

      case assig@Asts.VarAssig(Asts.VariableRef(lhsLocalId), typeAnnotTreeOpt, rhsTree) =>
        val varIsKnown = currScope.getLocalValuesContextUnsafe.knows(lhsLocalId)
        if (!varIsKnown) {
          reportError(s"unknown variable: $lhsLocalId", stat.getPosition)
        }
        val varIsReassignableOrUnknown = currScope.getLocalValuesContextUnsafe.isReassignableOrUnknown(lhsLocalId)
        if (!varIsReassignableOrUnknown && currScope.getLocalValuesContextUnsafe.valueOf(lhsLocalId).isInstanceOf[KnownAndInitialized]) {
          reportError(s"illegal reassignment of value $lhsLocalId", assig.getPosition)
        }
        val varIsReassignable = varIsKnown && varIsReassignableOrUnknown
        val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, currScope))
        val newValue =
          if varIsReassignable
          then currScope.newVar(lhsLocalId, currScope.getLocalValuesContextUnsafe.valueOf(lhsLocalId).declOpt, None, assig.getPosition)
          else currScope.newVal(lhsLocalId, assig.getPosition)
        generateSSAExpr(newValue, rhsTree, currScope)
        generateTypeCheckForAnnotIfAny(newValue, typeAnnotOpt, currScope, assig)
        currScope.getLocalValuesContextUnsafe.valueOf(lhsLocalId) match {
          case KnownAndInitialized(heapVarAddr: HeapVarIdValue, defScope, reassigStatus, declarationTypeAnnotOpt) =>
            currScope.saveInstr(HeapVarWrite(heapVarAddr, newValue), assig)
          case _ =>
            currScope.getLocalValuesContextUnsafe.remap(lhsLocalId, newValue)
        }

      case assig@Asts.VarAssig(Asts.Select(ownerTree, fieldId), typeAnnotTreeOpt, rhsTree) =>
        val ownerVal = currScope.newIntermediate(s"$fieldId'owner")
        generateSSAExpr(ownerVal, ownerTree, currScope)
        val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, currScope))
        val rhsVal = currScope.newIntermediate(fieldId.stringId)
        generateSSAExpr(rhsVal, rhsTree, currScope)
        generateTypeCheckForAnnotIfAny(rhsVal, typeAnnotOpt, currScope, assig)
        currScope.saveInstr(FieldWrite(ownerVal, FieldResolutionTarget(fieldId), rhsVal), assig)

      case assig@Asts.VarAssig(lhs, typeAnnotOpt, rhs) =>
        reportError("assignment target is not valid", assig.getPosition)

      case Asts.VarModif(lhs@Asts.VariableRef(lhsLocalId), typeAnnot, rhs, op) =>
        generateSSA(Asts.VarAssig(lhs, typeAnnot,
          Asts.BinaryOp(lhs, op, rhs).withDesugaringSource(stat)
        ).withDesugaringSource(stat), currScope, newScopeIfBlock)

      case Asts.VarModif(lhs@Asts.Select(Asts.ThisRef(), selected), typeAnnot, rhs, op) =>
        generateSSA(Asts.VarAssig(lhs, typeAnnot,
          Asts.BinaryOp(lhs, op, rhs).withDesugaringSource(stat)
        ).withDesugaringSource(stat), currScope, newScopeIfBlock)

      case Asts.VarModif(lhs, typeAnnot, rhs, op) =>
        reportError(s"in-place mutation is only allowed on local variables and selects on $ThisId", stat.getPosition)

      case ite@Asts.IfThenElse(condTree, thenTree, elseTreeOpt) =>
        val condVal = currScope.newIntermediate("cond")
        generateSSAExpr(condVal, condTree, currScope)
        val thenBrAssignedVars = externalVarsAssignedIn(thenTree)
        val elseBrAssignedVars = elseTreeOpt.flatMap(externalVarsAssignedIn)
        val allAssignedVars = SeqSet(thenBrAssignedVars ++ elseBrAssignedVars)
        val thenScope = Scope.nestedInside(currScope, thenTree)
        val elseScope = Scope.nestedInside(currScope, elseTreeOpt.getOrElse(ite))
        for (varId <- allAssignedVars) {
          thenScope.getLocalValuesContextUnsafe.createShallowCopy(varId)
          elseScope.getLocalValuesContextUnsafe.createShallowCopy(varId)
        }
        generateSSA(thenTree, thenScope, newScopeIfBlock = false)
        elseTreeOpt.foreach { elseTree =>
          generateSSA(elseTree, elseScope, newScopeIfBlock = false)
        }
        val variablesB = List.newBuilder[DisjunctionVarData]
        for (varId <- allAssignedVars) {
          (thenScope.getLocalValuesContextUnsafe.valueOf(varId), elseScope.getLocalValuesContextUnsafe.valueOf(varId)) match {
            case (KnownAndInitialized(thenEndVal, _, _, _), KnownAndInitialized(elseEndVal, _, _, _)) if !thenScope.hasExited && !elseScope.hasExited =>
              val joinVal = currScope.newVar(varId, currScope.getLocalValuesContextUnsafe.valueOf(varId).declOpt, Some("join"), ite.getPosition)
              variablesB.addOne(DisjunctionVarData(Some(varId), thenEndVal, elseEndVal, joinVal))
              currScope.getLocalValuesContextUnsafe.remap(varId, joinVal)
              proxyStore.saveProxy(joinVal, Phi(thenEndVal, elseEndVal))
            case (KnownAndInitialized(thenEndVal, _, _, _), _) if !thenScope.hasExited =>
              currScope.getLocalValuesContextUnsafe.remap(varId, thenEndVal)
            case (_, KnownAndInitialized(elseEndVal, _, _, _)) if !elseScope.hasExited =>
              currScope.getLocalValuesContextUnsafe.remap(varId, elseEndVal)
            case _ => ()
          }
        }
        currScope.saveInstr(Disjunction(condVal, thenScope, elseScope, variablesB.result()), stat)

      case whileLoop@Asts.WhileLoop(condTree, bodyTree) =>
        val condScope = Scope.nestedInside(currScope, condTree)
        val bodyScope = Scope.nestedInside(condScope, bodyTree)
        val loopUpdatedVars = externalVarsAssignedIn(whileLoop).toList.flatMap { varId =>
          currScope.getLocalValuesContextUnsafe.valueOf(varId) match {
            case KnownAndInitialized(value, defScope, _, _) =>
              val localDeclOpt = currScope.getLocalValuesContextUnsafe.valueOf(varId).declOpt
              Some(LoopVarData(varId, beforeLoopVal = value, condVal = defScope.newVar(varId, localDeclOpt, Some("loop-body-start"), bodyTree.getPosition),
                bodyLastVal = bodyScope.newVar(varId, localDeclOpt, Some("loop-body-end"), bodyTree.getPosition), defScope))
            case _ => None
          }
        }
        for (LoopVarData(id, beforeLoopVal, condVal, _, _) <- loopUpdatedVars) {
          condScope.getLocalValuesContextUnsafe.remap(id, condVal)
        }
        val condVal = currScope.newIntermediate("cond")
        generateSSAExpr(condVal, condTree, condScope)
        if (condScope.hasExited) {
          reportError("condition evaluation cannot terminate", condTree.getPosition)
        }
        generateSSA(bodyTree, bodyScope, newScopeIfBlock = false)
        if (bodyScope.hasExited) {
          warn("loop body always exits, should be an if statement", whileLoop.getPosition)
          // give up and generate a disjunction instead
          generateSSA(
            Asts.IfThenElse(condTree, bodyTree, None).withDesugaringSource(whileLoop),
            currScope,
            newScopeIfBlock
          )
        } else {
          for (varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal, varDefScope) <- loopUpdatedVars) {
            val bodyLastLocalVal = bodyScope.getLocalValuesContextUnsafe.valueOf(varId).asInstanceOf[KnownAndInitialized].value
            varData.recurrenceOpt = for {
              init <- proxyStore.developDeep(beforeLoopVal)
              induct <- proxyStore.developDeep(bodyLastLocalVal, acceptPhis = true)
            } yield Recurrence(init, induct, condVal)
            bodyScope.instructions.addOne(AssignVal(bodyLastVal, bodyLastLocalVal))
            currScope.getLocalValuesContextUnsafe.remap(varId, condVal)
          }
          val loop = Loop(condScope, condVal, bodyScope, loopUpdatedVars)
          currScope.saveInstr(loop, whileLoop)
          loopsCollector.addOne(loop)
        }

      case forLoop@Asts.ForLoop(initStats, cond, stepStats, body) =>
        generateSSA(Asts.Block(
          initStats :+ Asts.WhileLoop(cond, Asts.Block(
            body.stats ++ stepStats
          ).withDesugaringSource(forLoop)).withDesugaringSource(forLoop)
        ).withDesugaringSource(forLoop), currScope, newScopeIfBlock = true)

      case returnStat@Asts.ReturnStat(returnedTreeOpt) =>
        val retVal = currFuncInfo.funSigScope.newIntermediate("ret")
        returnedTreeOpt match {
          case Some(returnedTree) =>
            generateSSAExpr(retVal, returnedTree, currScope)
            proxyStore.developDeep(retVal, bypassPurityChecks = true) match {
              case Some(retValProxy) =>
                returnCollector.offerReturn(retValProxy)
              case None =>
                returnCollector.giveUp()
            }
          case None =>
            val unitVal = currScope.valuesCtx.globalCtx.unitVal
            currScope.saveInstr(AssignVal(retVal, unitVal), returnStat)
            proxyStore.saveProxy(retVal, unitVal)
        }
        currScope.saveInstr(Return(retVal), stat)
        currScope.getLocalValuesContextUnsafe.markHasExited()
    }
  }

  private def generateTypeCheckForAnnotIfAny(
                                              rhsValue: IdValue,
                                              typeAnnotOpt: Option[Type],
                                              scope: Scope,
                                              astNode: Asts.Ast
                                            ): Unit = {
    typeAnnotOpt.foreach { typeAnnot =>
      scope.saveInstr(StaticTypeAssert(rhsValue, typeAnnot), astNode)
    }
  }

  private def generateSSAExpr(
                               resultVal: IdValue,
                               expr: Asts.Expr,
                               currScope: Scope
                             )(using loopsCollector: mutable.ListBuffer[SSA.Loop], importsCtx: ImportsContext, typeParamsCtx: TypeParamsContext): Option[Formula] = {

    def recurseOnDesugared(desugaredExpr: Asts.Expr): Option[Formula] =
      generateSSAExpr(resultVal, desugaredExpr.withDesugaringSource(expr), currScope)

    def generateArgsList(argsTrees: List[Asts.Expr]): List[IdValue] = {
      val argsValsB = List.newBuilder[IdValue]
      for (argTree <- argsTrees) {
        val argVal = currScope.newIntermediate("arg")
        argsValsB.addOne(argVal)
        generateSSAExpr(argVal, argTree, currScope)
      }
      argsValsB.result()
    }

    def generateUnary(operandTree: Asts.Expr, mkInstr: (operand: IdValue) => Instr, mkFormulaOpt: Option[Formula => Formula] = None): Option[Formula] = {
      val operandVal = currScope.newIntermediate("unaryop")
      generateSSAExpr(operandVal, operandTree, currScope)
      currScope.saveInstr(mkInstr(operandVal), expr)
      for {
        mkFormula <- mkFormulaOpt
      } yield mkFormula(operandVal)
    }

    def generateUnaryWithProxy(operandTree: Asts.Expr, mkInstr: (operand: IdValue) => Instr, mkFormula: Formula => Formula): Option[Formula] =
      generateUnary(operandTree, mkInstr, Some(mkFormula))

    def generateBinary(lhs: Asts.Expr, rhs: Asts.Expr, mkInstr: (lhs: IdValue, rhs: IdValue) => Instr, mkFormulaOpt: Option[(Formula, Formula) => Formula] = None, swapOperands: Boolean = false): Option[Formula] = {
      var lhsVal = currScope.newIntermediate("leftop")
      generateSSAExpr(lhsVal, lhs, currScope)
      var rhsVal = currScope.newIntermediate("rightop")
      generateSSAExpr(rhsVal, rhs, currScope)
      if (swapOperands) {
        val lhsBefore = lhsVal
        lhsVal = rhsVal
        rhsVal = lhsBefore
      }
      currScope.saveInstr(mkInstr(lhsVal, rhsVal), expr)
      for {
        mkFormula <- mkFormulaOpt
      } yield mkFormula(lhsVal, rhsVal)
    }

    def generateBinaryWithProxy(lhs: Asts.Expr, rhs: Asts.Expr, mkInstr: (lhs: IdValue, rhs: IdValue) => Instr, mkFormula: (Formula, Formula) => Formula, swapOperands: Boolean = false): Option[Formula] =
      generateBinary(lhs, rhs, mkInstr, Some(mkFormula), swapOperands = swapOperands)

    val proxyOpt = expr match {
      case Asts.UnitLit() =>
        currScope.saveInstr(AssignVal(resultVal, currScope.valuesCtx.globalCtx.unitVal), expr)
        None
      case Asts.IntLit(value) =>
        currScope.saveInstr(AssignIntConst(resultVal, value), expr)
        Some(IntConst(value))
      case Asts.DoubleLit(value) => ???
      case Asts.CharLit(value) => ???
      case Asts.BoolLit(value) =>
        currScope.saveInstr(AssignBoolConst(resultVal, value), expr)
        Some(BoolConst(value))
      case Asts.StringLit(value) =>
        currScope.saveInstr(AssignStringConst(resultVal, value), expr)
        Some(StringConst(value))
      case Asts.NullRef() =>
        val nullVal = currScope.valuesCtx.globalCtx.nullVal
        currScope.saveInstr(AssignVal(resultVal, nullVal), expr)
        Some(nullVal)
      case varRefTree@Asts.VariableRef(name) =>
        currScope.getLocalValuesContextUnsafe.valueOf(name) : @unchecked match {
          case LocalValuesContext.Unknown(id) =>
            reportError(s"not found: $id", varRefTree.getPosition)
            None
          case LocalValuesContext.KnownButUninitialized(id, _, _, _) =>
            reportError(s"$id might not have been initialized", varRefTree.getPosition)
            None
          case KnownAndInitialized(heapAddr: HeapVarIdValue, defScope, reassigStatus, declarationTypeAnnotOpt) =>
            currScope.saveInstr(HeapVarRead(resultVal, heapAddr), expr)
            None
          case KnownAndInitialized(value, _, _, _) =>
            currScope.saveInstr(AssignVal(resultVal, value), expr)
            Some(value)
        }
      case Asts.ThisRef() =>
        recurseOnDesugared(Asts.VariableRef(ThisId))
        None
      case Asts.ItRef() =>
        recurseOnDesugared(Asts.VariableRef(ItId))
        None // TODO update if it gets reintroduced
      case Asts.ObjectRef(objectNameRaw) =>
        val objectName = importsCtx.applyImports(objectNameRaw)
        val objIdVal = currScope.valuesCtx.resolveObject(objectName)
        currScope.saveInstr(AssignVal(resultVal, objIdVal), expr)
        Some(objIdVal)
      case callTree@Asts.Call(Asts.Select(receiverTree, funId), typeArgsTrees, argTrees) =>
        val receiverVal = currScope.newIntermediate("receiver")
        generateSSAExpr(receiverVal, receiverTree, currScope)
        val typeArgs = typeArgsTrees.map(mkType(_, currScope))
        val argVals = generateArgsList(argTrees)
        val invkTarget = InvocationTarget(funId)
        currScope.saveInstr(InvokeFunc(resultVal, receiverVal, invkTarget, typeArgs, argVals), expr)
        Some(FunCall(receiverVal, invkTarget, typeArgs, argVals))
      case callTree@Asts.Call(callee@Asts.VariableRef(rawFunId), typeArgTrees, argTrees)
        if !currScope.getLocalValuesContextUnsafe.knows(rawFunId) =>
        findImplicitReceiverInImports(rawFunId, currScope) match {
          case Some(receiverVal, targetFunId) =>
            val typeArgs = typeArgTrees.map(mkType(_, currScope))
            val argVals = generateArgsList(argTrees)
            val invkTarget = InvocationTarget(targetFunId)
            currScope.saveInstr(InvokeFunc(resultVal, receiverVal, invkTarget, typeArgs, argVals), expr)
            Some(FunCall(receiverVal, invkTarget, typeArgs, argVals))
          case None =>
            reportError(s"no receiver found for call to $rawFunId", callTree.getPosition)
            None
        }
      case callTree@Asts.Call(calleeTree, typeArgTrees, argTrees) =>
        if (typeArgTrees.nonEmpty) {
          reportError("type arguments on closure invocation", callTree.getPosition)
        }
        val calleeVal = currScope.newIntermediate("callee")
        generateSSAExpr(calleeVal, calleeTree, currScope)
        val target = ClosureTypingTarget()
        val args = generateArgsList(argTrees)
        currScope.saveInstr(InvokeClosure(resultVal, calleeVal, target, args), expr)
        Some(ClosureCall(calleeVal, target, args))
      case Asts.UnaryOp(Operator.Minus, operandTree) =>
        generateUnaryWithProxy(operandTree, NumNeg(resultVal, _), Neg(_))
      case Asts.UnaryOp(Operator.ExclamationMark, operandTree) =>
        generateUnaryWithProxy(operandTree, LogicNeg(resultVal, _), LogicalNot(_))
      case Asts.UnaryOp(operator, operand) => throw AssertionError(s"unexpected $operator as unary operator")
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Plus, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Add(resultVal, _, _), Plus(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Minus, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Sub(resultVal, _, _), (a, b) => Plus(a, Neg(b)))
      // TODO for *,/,% see if we keep the proxy or not: non-determinism?
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Times, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Mul(resultVal, _, _), Times(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Div, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Div(resultVal, _, _), DivBy(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Modulo, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Rem(resultVal, _, _), DivBy(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.LessThan, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Lt(resultVal, _, _), LessThan(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.GreaterThan, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Lt(resultVal, _, _), LessThan(_, _), swapOperands = true)
      case binopTree@Asts.BinaryOp(lhsTree, Operator.LessOrEq, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Leq(resultVal, _, _), LessOrEq(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.GreaterOrEq, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Leq(resultVal, _, _), LessOrEq(_, _), swapOperands = true)
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Equality, rhsTree) =>
        // FIXME desugar to invocation of equals method when needed
        generateBinaryWithProxy(lhsTree, rhsTree, Equal(resultVal, _, _), Equality(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Inequality, rhsTree) =>
        recurseOnDesugared(Asts.UnaryOp(Operator.ExclamationMark,
          Asts.BinaryOp(lhsTree, Operator.Equality, rhsTree).withDesugaringSource(binopTree)
        ).withDesugaringSource(binopTree))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.And, rhsTree) =>
        recurseOnDesugared(Asts.Ternary(lhsTree,
          Asts.TypeAscription(rhsTree, Asts.PrimitiveTypeTree(BoolType).withDesugaringSource(binopTree)).withDesugaringSource(binopTree),
          Asts.BoolLit(false).withDesugaringSource(binopTree)
        ).withDesugaringSource(binopTree))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Or, rhsTree) =>
        recurseOnDesugared(Asts.Ternary(lhsTree,
          Asts.BoolLit(true).withDesugaringSource(binopTree),
          Asts.TypeAscription(rhsTree, Asts.PrimitiveTypeTree(BoolType).withDesugaringSource(binopTree)).withDesugaringSource(binopTree)
        ))
      case binopTree@Asts.BinaryOp(lhs, operator, rhs) =>
        throw AssertionError(s"unexpected $operator as binary operator")
      case selectTree@Asts.Select(lhsTree, fieldId) =>
        val lhsVal = currScope.newIntermediate(fieldId.stringId)
        generateSSAExpr(lhsVal, lhsTree, currScope)
        val unresolvedField = FieldResolutionTarget(fieldId)
        currScope.saveInstr(FieldRead(resultVal, lhsVal, unresolvedField), selectTree)
        Some(Select(lhsVal, unresolvedField))
      case typeTestTree@Asts.TypeTest(testedExprTree, Asts.NamedTypeTree(typeNameRaw, Nil, Nil)) =>
        val typeName = importsCtx.applyImports(typeNameRaw)
        generateUnaryWithProxy(testedExprTree, TypeTest(resultVal, _, typeName), TypePredicate(_, typeName))
      case typeTest@Asts.TypeTest(_, tpe) =>
        reportError(s"illegal type for dynamic type test: $tpe", typeTest.getPosition)
        None
      case recordOrClassInstTree@Asts.RecordOrClassInstantiation(typeIdRaw, typeArgTrees, initializers) =>
        val initializationScope = Scope.nestedInside(currScope, recordOrClassInstTree, objInitializedHereOpt = Some(resultVal))
        for (initializer <- initializers) {
          val initializerRhs = rhsOf(initializer)
          val rhsVal = currScope.newIntermediate(initializer.fieldName.stringId)
          generateSSAExpr(rhsVal, initializerRhs, currScope)
          initializationScope.saveInstr(FieldWrite(resultVal, FieldResolutionTarget(initializer.fieldName), rhsVal), initializer)
        }
        val typeId = importsCtx.applyImports(typeIdRaw)
        val typeArgs = typeArgTrees.map(mkType(_, currScope))
        currScope.saveInstr(Instantiate(resultVal, typeId, typeArgs), recordOrClassInstTree)
        currScope.saveInstr(initializationScope, recordOrClassInstTree)
        None
      case ternaryTree@Asts.Ternary(condTree, thenTree, elseTree) =>
        val condVal = currScope.newIntermediate("cond")
        generateSSAExpr(condVal, condTree, currScope)
        val thenVal = currScope.newIntermediate("then")
        val thenScope = Scope.nestedInside(currScope, thenTree)
        generateSSAExpr(thenVal, thenTree, thenScope)
        val elseVal = currScope.newIntermediate("else")
        val elseScope = Scope.nestedInside(currScope, elseTree)
        generateSSAExpr(elseVal, elseTree, elseScope)
        currScope.saveInstr(Disjunction(condVal, thenScope, elseScope,
          List(DisjunctionVarData(None, thenVal, elseVal, resultVal))
        ), ternaryTree)
        // retrieve info from lowering
        proxyStore.developDeep(thenVal) match {
          case Some(BoolConst(true)) => Some(LogicalOr(condVal, elseVal))
          case _ => proxyStore.developDeep(elseVal) match {
            case Some(BoolConst(false)) => Some(LogicalAnd(condVal, thenVal))
            case _ => None
          }
        }
      case castTree@Asts.Cast(castExprTree, Asts.NamedTypeTree(typeNameRaw, Nil, Nil)) =>
        val typeName = importsCtx.applyImports(typeNameRaw)
        generateSSAExpr(resultVal, castExprTree, currScope)
        currScope.saveInstr(Cast(resultVal, typeName), castTree)
        None
      case conversionTree@Asts.Cast(inExprTree, targetTypeTree: Asts.PrimitiveTypeTree) =>
        val inVal = currScope.newIntermediate("convertedval")
        generateSSAExpr(inVal, inExprTree, currScope)
        currScope.saveInstr(Conversion(resultVal, inVal, targetTypeTree.primitiveType), conversionTree)
        None
      case castTree@Asts.Cast(castExpr, tpe) =>
        reportError(s"illegal type for dynamic type test: $tpe", castTree.getPosition)
        None
      case weakcast@Asts.Weakcast(castExpr) =>
        val inVal = currScope.newIntermediate("weakcast$subject")
        generateSSAExpr(inVal, castExpr, currScope)
        currScope.saveInstr(WeakCast(inVal), weakcast)
        None
      case ascriptionTree@Asts.TypeAscription(ascribedExpr, typeTree) =>
        generateSSAExpr(resultVal, ascribedExpr, currScope)
        currScope.saveInstr(StaticTypeAssert(resultVal, mkType(typeTree, currScope)), ascriptionTree)
        None
      case closureDefTree@Asts.ClosureDef(params, bodyTree, declaredPure) =>
        val closureParamsScope = Scope.nestedInside(currScope, bodyTree)
        val paramValsAndTypesB = List.newBuilder[(ParamIdValue, Type)]
        for ((id, typeTreeOpt) <- params) {
          // TODO maybe keep position even when no type is provided
          val posOpt = typeTreeOpt.flatMap(_.getPosition).orElse(closureDefTree.getPosition)
          val paramVal = closureParamsScope.newParam(id, posOpt)
          val givenTypeOpt = typeTreeOpt.map(mkType(_, closureParamsScope))
          val tpe = givenTypeOpt.getOrElse(TypeVariable(id, None, None, typeParamsCtx, closureDefTree.getPosition)(closureParamsScope.valuesCtx.globalCtx.saveTypeVariable))
          paramValsAndTypesB.addOne(paramVal -> tpe)
          closureParamsScope.getLocalValuesContextUnsafe.saveOrRemap(id, paramVal, closureParamsScope, ReassigPermission.Val, givenTypeOpt)
        }
        for (varId <- externalVarsAssignedIn(bodyTree)) {
          val heapAddr = currScope.newHeapVar(varId, closureDefTree.getPosition)
          currScope.saveInstr(MkHeapVar(heapAddr), closureDefTree)
          currScope.getLocalValuesContextUnsafe.valueOf(varId).toOption.foreach { initVal =>
            currScope.saveInstr(HeapVarWrite(heapAddr, initVal), closureDefTree)
          }
          currScope.getLocalValuesContextUnsafe.remap(varId, heapAddr)
        }
        val closureBodyScope = Scope.nestedInside(closureParamsScope, closureDefTree)
        val retValCollector = ReturnCollector.freshUniqueCollector
        generateSSA(bodyTree, closureBodyScope, newScopeIfBlock = false)(using retValCollector, FunctionInfo(closureParamsScope))
        val isPure = declaredPure || isObviouslyPure(closureBodyScope)
        val paramValsAndTypes = paramValsAndTypesB.result()
        currScope.saveInstr(MkClosure(resultVal, paramValsAndTypes, closureBodyScope, isPure), closureDefTree)
        retValCollector.getUniqueRet.flatMap { closureRetVal =>
          val closure = PureClosureValue(paramValsAndTypes.map(_._1), closureRetVal, resultVal)
          if isPure then Some(closure)
          else {
            proxyStore.savePossiblyImpureClosure(resultVal, closure)
            None
          }
        }
      case panicTree@Asts.PanicExpr(msgTree) =>
        val msgVal = currScope.newIntermediate("msg")
        generateSSAExpr(msgVal, msgTree, currScope)
        currScope.saveInstr(Panic(msgVal), panicTree)
        currScope.getLocalValuesContextUnsafe.markHasExited()
        None
    }
    if (!proxyStore.hasProxyFor(resultVal)) {
      // avoid resetting proxy when generateSSAExpr is called recursively
      proxyStore.saveProxy(resultVal, proxyOpt)
    }
    proxyOpt
  }

  private def generateFormula(expr: Expr, currScope: Scope)(using importsCtx: ImportsContext, typeParamsCtx: TypeParamsContext): Option[Formula] = {

    def generateFormula(expr: Expr, currScope: Scope): Option[Formula] = {

      def failIllegalConstruct(constructKindDescr: String): Option[Formula] = {
        er.reportError(s"illegal construct in formula: $constructKindDescr", expr.getPosition)
        None
      }

      expr match {
        case Asts.IntLit(value) => Some(IntConst(value))
        case Asts.DoubleLit(value) => ???
        case Asts.UnitLit() => failIllegalConstruct("unit literal")
        case Asts.CharLit(value) => ???
        case Asts.BoolLit(value) => Some(BoolConst(value))
        case Asts.StringLit(value) => Some(StringConst(value))
        case Asts.NullRef() => Some(currScope.valuesCtx.globalCtx.nullVal)
        case Asts.VariableRef(name) =>
          currScope.getLocalValuesContextOpt.flatMap(_.valueOf(name).toOption) match {
            case someVal@Some(_) => someVal
            case None =>
              er.reportError(s"not found: $name", expr.getPosition)
              None
          }
        case Asts.ThisRef() => generateFormula(VariableRef(ThisId), currScope)
        case Asts.ItRef() => generateFormula(VariableRef(ItId), currScope)
        case Asts.ObjectRef(objectNameRaw) =>
          val objectName = importsCtx.applyImports(objectNameRaw)
          Some(currScope.valuesCtx.resolveObject(objectName))
        case Asts.TypeAscription(expr, tpe) => failIllegalConstruct("type ascription")
        // TODO non-prefixed calls (implicit this)?
        case Asts.Call(callee, typeArgTrees, args) =>
          val receiverAndFunIdOpt = callee match {
            case Asts.VariableRef(funId) if !currScope.getLocalValuesContextUnsafe.knows(funId) =>
              findImplicitReceiverInImports(funId, currScope)
            case Asts.Select(lhs, funId) =>
              generateFormula(lhs, currScope).map(_ -> funId)
            case _ => None
          }
          receiverAndFunIdOpt match {
            case Some((receiverFormula, funId)) =>
              val typeArgs = typeArgTrees.map(mkType(_, currScope))
              val argFormulas = args.flatMap(generateFormula(_, currScope))
              if argFormulas.size == args.size then Some(FunCall(receiverFormula, InvocationTarget(funId), typeArgs, argFormulas))
              else None
            case None => for {
              calleeFormula <- generateFormula(callee, currScope)
              argFormulas <- args.foldRight(Option(List.empty[Formula])) { (arg, following) =>
                for {
                  following <- following
                  argFormula <- generateFormula(arg, currScope)
                } yield argFormula :: following
              }
            } yield ClosureCall(calleeFormula, ClosureTypingTarget(), argFormulas)
          }
        case Asts.RecordOrClassInstantiation(typeId, typeArgs, initializers) => failIllegalConstruct("instantiation")
        case Asts.UnaryOp(Operator.Minus, operand) =>
          for {
            opFormula <- generateFormula(operand, currScope)
          } yield Neg(opFormula)
        case Asts.UnaryOp(Operator.ExclamationMark, operand) =>
          for {
            opFormula <- generateFormula(operand, currScope)
          } yield LogicalNot(opFormula)
        case expr: Asts.UnaryOp => failIllegalConstruct(s"\"${expr.operator}\" operator")
        case Asts.BinaryOp(lhs, Operator.Plus, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield Plus(lhsFormula, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.Minus, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield Plus(lhsFormula, Neg(rhsFormula))
        case Asts.BinaryOp(lhs, Operator.Times, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield Times(lhsFormula, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.Div, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield DivBy(lhsFormula, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.Modulo, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield Modulo(lhsFormula, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.Equality, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield Equality(lhsFormula, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.Inequality, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield LogicalNot(Equality(lhsFormula, rhsFormula))
        case Asts.BinaryOp(lhs, Operator.LessOrEq, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield LessOrEq(lhsFormula, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.GreaterOrEq, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield LessOrEq(rhsFormula, lhsFormula)
        case Asts.BinaryOp(lhs, Operator.LessThan, rhs) =>
          import compiler.irs.ssa.FormulasDsl.*
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
            // TODO check if this yield confusing error messages (desugaring producing the +1)
          } yield LessOrEq(lhsFormula + 1, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.GreaterThan, rhs) =>
          import compiler.irs.ssa.FormulasDsl.*
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
            // TODO check if this yield confusing error messages (desugaring producing the +1)
          } yield LessOrEq(rhsFormula + 1, lhsFormula)
        case Asts.BinaryOp(lhs, Operator.And, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield LogicalAnd(lhsFormula, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.Or, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield LogicalOr(lhsFormula, rhsFormula)
        case expr: Asts.BinaryOp => failIllegalConstruct(s"\"${expr.operator}\" operator")
        case Asts.Select(lhs, field) =>
          for {
            ownerFormula <- generateFormula(lhs, currScope)
          } yield Select(ownerFormula, FieldResolutionTarget(field))
        case Asts.ClosureDef(params, body, declaredPure) => failIllegalConstruct("closure definition")
        case Asts.Ternary(cond, thenBr, elseBr) => failIllegalConstruct("ternary operator")
        case Asts.Cast(expr, tpe) => failIllegalConstruct("dynamic cast or conversion")
        case Asts.Weakcast(expr) => failIllegalConstruct("dynamic weak cast")
        case Asts.TypeTest(expr, Asts.NamedTypeTree(typeNameRaw, Nil, Nil)) =>
          val typeName = importsCtx.applyImports(typeNameRaw)
          for {
            subj <- generateFormula(expr, currScope)
          } yield TypePredicate(subj, typeName)
        case Asts.TypeTest(expr, tpe) => failIllegalConstruct(s"cast to $tpe")
        case Asts.PanicExpr(msg) => failIllegalConstruct("panic expression")
      }
    }

    generateFormula(expr, currScope)
  }

  private def isObviouslyPure(instr: Instr): Boolean = instr match {
    case _: PureInstr => true
    case Loop(cond, condVal, body, variables) =>
      isObviouslyPure(cond) && isObviouslyPure(body)
    case Disjunction(condVal, thenBr, elseBr, variables) =>
      isObviouslyPure(thenBr) && isObviouslyPure(elseBr)
    case scope: Scope =>
      scope.instructions.forall(isObviouslyPure)
    case LocalDecl(localId, tpe) => true
    case Unreachable() => true
    case _ => false
  }

  private def mustNotBeUnit(tpe: Type, posOpt: Option[Position]): Unit = {
    if (tpe == UnitType) {
      reportError(s"$UnitType is not allowed in this position", posOpt)
    }
  }

  private def findImplicitReceiverInImports(rawFunId: FunOrVarId, currScope: Scope)(using importsCtx: ImportsContext): Option[(IdValue, FunOrVarId)] = {
    currScope.getLocalValuesContextOpt.flatMap { localValsCtx =>
      importsCtx.importedFuncFor(rawFunId).map { (objId, funId) =>
        val objVal = localValsCtx.resolveObject(objId)
        objVal -> funId
      } orElse {
        localValsCtx.getThisValue.map(_ -> rawFunId)
      }
    }
  }

  private def mkType(typeTree: Asts.TypeTree, scope: Scope)(using typeParamsCtx: TypeParamsContext, importsCtx: ImportsContext): Type = {

    extension (optFormula: Option[Formula]) def required(errorMsg: String, posOpt: Option[Position]): Option[Formula] = optFormula match {
      case s@Some(_) => s
      case None =>
        er.reportError(errorMsg, posOpt)
        None
    }

    typeTree match {
      case Asts.PrimitiveTypeTree(primitiveType) => primitiveType
      case namedTypeTree: Asts.NamedTypeTree => mkNamedType(namedTypeTree, scope)
      case Asts.ClosureTypeTree(paramTypes, resultType, enforcedPure) =>
        ClosureType(paramTypes.map(mkType(_, scope)), mkType(resultType, scope), enforcedPure)
      case Asts.RefinedTypeTree(baseTypeTree, predicateTree) =>
        val baseType = mkType(baseTypeTree, scope)
        generateFormula(predicateTree, scope) match {
          case Some(predicate) => RefinedType(baseType, predicate)
          case None =>
            er.reportError("invalid predicate", predicateTree.getPosition)
            baseType
        }
      case rangeTypeTree@Asts.IntRangeTypeTree(lowerBoundOpt, upperBoundOpt, upperIncluded) =>
        import FormulasDsl.*
        IntRangeType(
          lowerBoundOpt.flatMap(lb => generateFormula(lb, scope).required("invalid lower bound", lb.getPosition)),
          upperBoundOpt.flatMap(ub => generateFormula(ub, scope).required("invalid upper bound", ub.getPosition)).map { ub =>
            if upperIncluded then ub else ub - 1
          }
        )
      case Asts.NullableTypeTree(wrappedType) =>
        NullableType(mkType(wrappedType, scope))
      case Asts.UnionTypeTree(types) =>
        UnionType(SeqSet(types.map(mkType(_, scope))))
      case Asts.IntersectionTypeTree(types) =>
        IntersectionType(SeqSet(types.map(mkType(_, scope))))
    }
  }

  private def mkNamedType(namedTypeTree: Asts.NamedTypeTree, scope: Scope)(using typeParamsCtx: TypeParamsContext, importsCtx: ImportsContext): NamedType = namedTypeTree match {
    case Asts.NamedTypeTree(rawTId@TypeIdentifier(Nil, typeName), typeParams, params) =>
      typeParamsCtx.resolve(rawTId) match {
        // TODO use separate case class for type parameters
        case Some(tpe) => NamedType(rawTId, List.empty, List.empty)
        case None =>
          val tid = importsCtx.importedTypeFor(typeName).getOrElse(rawTId)
          NamedType(tid, typeParams.map(mkType(_, scope)), params.flatMap(generateFormula(_, scope)))
      }
    case Asts.NamedTypeTree(name, typeParams, params) =>
      NamedType(name, typeParams.map(mkType(_, scope)), params.flatMap(generateFormula(_, scope)))
  }

  private def externalVarsAssignedIn(ast: Asts.Ast): Set[FunOrVarId] = {
    val assigned = mutable.Set.empty[FunOrVarId]
    val defined = mutable.Set.empty[FunOrVarId]
    ast.preorderWalk {
      case localDef: Asts.LocalDef =>
        defined.addOne(localDef.localName)
      case assignment: Asts.Assignment => assignment.lhs match {
        case Asts.VariableRef(varId) =>
          assigned.addOne(varId)
        case _ => ()
      }
      case _ => ()
    }
    val assignedVars = assigned.toSet -- defined
    assignedVars
  }

  private def rhsOf(initializer: Asts.FieldInitializer): Asts.Expr = initializer match {
    case Asts.FullFieldInitializer(fieldName, rhs) => rhs
    case Asts.ShorthandFieldInitializer(fieldName) =>
      Asts.VariableRef(fieldName).withDesugaringSource(initializer)
  }

  extension (scope: Scope) private def saveInstr(instr: SSA.Instr, node: Asts.Ast): Unit = {
    instr match {
      case _: Scope => ()
      case _ =>
        instr.setAstNode(node.originalAst)
    }
    scope.instructions.addOne(instr)
  }

  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Err(SSAGeneration, msg, posOpt))
  }

  private def warn(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Warning(SSAGeneration, msg, posOpt))
  }

  private case class FunctionInfo(funSigScope: Scope)

}
