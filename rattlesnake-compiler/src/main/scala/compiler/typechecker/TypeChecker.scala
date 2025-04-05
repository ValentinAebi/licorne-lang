package compiler.typechecker

import compiler.analysisctx.AnalysisContext
import compiler.analysisctx.AnalysisContext.{FunctionFound, FunctionNotFound, ModuleNotFound}
import compiler.gennames.ClassesAndDirectoriesNames.constantsClassName
import compiler.irs.Asts.*
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.typechecker.CapturablesConverter.convertToCapturable
import compiler.typechecker.ExprPosition.{Captured, Executable}
import compiler.typechecker.ShapeAnnotPosition.{InTypeTest, InsideCapturingType, OutsideCapturingType}
import compiler.typechecker.SubcaptureRelation.isCoveredBy
import compiler.typechecker.SubtypeRelation.subtypeOf
import compiler.typechecker.TypeCheckingContext.{ConstantInfo, LocalInfo}
import identifiers.*
import lang.*
import lang.Capturables.*
import lang.CaptureDescriptors.{CaptureDescriptor, CaptureSet, Mark}
import lang.LanguageMode.*
import lang.Operator.{Equality, Inequality, Len, Sharp}
import lang.Operators.{BinaryOpSignature, UnaryOpSignature, binaryOperators, unaryOperators}
import lang.Types.*
import lang.Types.PrimitiveTypeShape.*

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

final class TypeChecker(errorReporter: ErrorReporter)
  extends CompilerStep[(List[Source], AnalysisContext), (List[Source], AnalysisContext)] {

  override def apply(input: (List[Source], AnalysisContext)): (List[Source], AnalysisContext) = {
    val (sources, analysisContext) = input
    for src <- sources do {
      checkSource(src, analysisContext)
    }
    errorReporter.displayAndTerminateIfErrors()
    sources.foreach(_.assertAllTypesAreSet())
    input
  }

  private def checkSource(src: Source, analysisContext: AnalysisContext): Unit = {
    val Source(defs, languageMode) = src
    for (df <- defs) {
      checkTopLevelDef(df, analysisContext)(using languageMode)
    }
  }

  private def checkTopLevelDef(topLevelDef: TopLevelDef, analysisContext: AnalysisContext)
                              (using langMode: LanguageMode): Unit = topLevelDef match {

    case PackageDef(packageName, functions) =>
      val packageSig = analysisContext.resolveTypeAs[PackageSignature](packageName).get
      val environment = packageSig.getNonSubstitutedCaptureDescr
      val mainFunctionsCollector = ListBuffer.empty[FunDef]
      for func <- functions do {
        checkFunction(func, analysisContext, packageName, packageSig.getNonSubstitutedCaptureDescr, langMode,
          packageSig.globalCapturesAsCs, Some(mainFunctionsCollector))
      }
      if (mainFunctionsCollector.size > 1) {
        for (mainFun <- mainFunctionsCollector) {
          reportError("more than one main function in the current package", mainFun.getPosition)
        }
      }

    case ModuleDef(moduleName, imports, functions) =>
      val moduleSig = analysisContext.resolveTypeAs[ModuleSignature](moduleName).get
      val importsCtx = TypeCheckingContext(
        analysisContext,
        meTypeId = moduleName,
        meCaptureDescr = moduleSig.getNonSubstitutedCaptureDescr,
        currFunIdOpt = None,

        insideEnclosure = false,
        currentRestriction = CaptureSet.singletonOfRoot
      )
      for imp <- imports do {
        checkImport(imp, importsCtx, langMode)
      }
      val environment = moduleSig.getNonSubstitutedCaptureDescr
      for func <- functions do {
        checkFunction(func, analysisContext, moduleName, moduleSig.getNonSubstitutedCaptureDescr, langMode,
          moduleSig.globalCapturesAsCs, None)
      }

    case structDef@StructDef(structName, isShallowMutable, fields, _, _) =>
      val structSig = analysisContext.resolveTypeAs[StructSignature](structName).get
      val tcCtx = TypeCheckingContext(
        analysisContext,
        meTypeId = structName,
        meCaptureDescr = structSig.getNonSubstitutedCaptureDescr,
        currFunIdOpt = None,
        insideEnclosure = false,
        currentRestriction = CaptureSet.singletonOfRoot
      )
      if (langMode.isOcapEnabled && isShallowMutable) {
        tcCtx.addLocal(SpecialFields.regFieldId, RegionType ^ CaptureSet.singletonOfRoot, structDef.getPosition,
          isReassignable = false, declHasTypeAnnot = false, () => (), () => ())
      }
      for (param@Param(paramNameOpt, typeTree, isReassignable) <- fields) {
        val tpe = checkType(typeTree, idsAreFields = true)(using tcCtx, Environment.root, langMode)
        if (isReassignable) {
          forbidRootCapture(tpe, "reassignable field", param.getPosition)
        }
        paramNameOpt.foreach { paramName =>
          tcCtx.addLocal(paramName, tpe, param.getPosition, isReassignable, declHasTypeAnnot = true,
            duplicateVarCallback = { () =>
              reportError(s"duplicate field: $paramName", param.getPosition)
            },
            forbiddenTypeCallback = { () =>
              reportError(s"field $paramName has type $tpe, which is forbidden", param.getPosition)
            }
          )
        }
        if (isReassignable && !isShallowMutable) {
          reportError("reassignable field in immutable struct", param.getPosition)
        }
      }

    case constDef@ConstDef(constName, tpeOpt, value) =>
      val inferredType = checkLiteralExpr(value)
      tpeOpt.foreach { expType =>
        val placeholderMeId = NormalTypeId(constantsClassName)
        val tcCtx = TypeCheckingContext(
          analysisContext,
          currFunIdOpt = None,
          meTypeId = placeholderMeId,
          meCaptureDescr = CaptureSet.empty,
          insideEnclosure = false,
          currentRestriction = CaptureSet.singletonOfRoot
        )
        val checkedType = checkType(expType, idsAreFields = false)(using tcCtx, Environment.root, OcapDisabled)
        checkSubtypingConstraint(
          checkedType,
          inferredType,
          constDef.getPosition,
          "constant definition"
        )(using tcCtx, langMode)
      }
  }

  private def forbidRootCapture(tpe: Type, typePosDescr: String, posOpt: Option[Position]): Unit = tpe match {
    case CapturingType(shape, captureDescriptor) if captureDescriptor.coversRoot =>
      reportError(s"type $tpe is forbidden in $typePosDescr position, as it captures the root capability", posOpt)
    case _ => ()
  }

  private def checkFunction(
                             funDef: FunDef,
                             analysisContext: AnalysisContext,
                             meId: TypeIdentifier,
                             meCaptureDescr: CaptureDescriptor,
                             langMode: LanguageMode,
                             globalCapSet: CaptureSet,
                             mainFunctionsCollectorOpt: Option[ListBuffer[FunDef]]
                           ): Unit = {
    val FunDef(funName, params, optRetTypeTree, body, visibility, isMain) = funDef
    if (isMain) {
      checkIsEligibleAsMain(funDef)
      mainFunctionsCollectorOpt.foreach(_.addOne(funDef))
    }
    if (isMain && mainFunctionsCollectorOpt.isEmpty) {
      reportError("only packages can contain a main function", funDef.getPosition)
    }
    val tcCtx = TypeCheckingContext(analysisContext, meId, meCaptureDescr, Some(funName),
      insideEnclosure = false, currentRestriction = CaptureSet.singletonOfRoot)
    val bodyEnvir = Environment(globalCapSet)
    bodyEnvir.allow(MePath)
    for param <- params do {
      val paramType = checkType(param.tpe, idsAreFields = false)(using tcCtx, Environment.root, langMode)
      param.paramNameOpt.foreach { paramName =>
        tcCtx.addLocal(paramName, paramType, param.getPosition, param.isReassignable, declHasTypeAnnot = true,
          duplicateVarCallback = { () =>
            reportError(s"identifier '${param.paramNameOpt}' is already used by another parameter of function '$funName'", param.getPosition)
          }, forbiddenTypeCallback = { () =>
            reportError(s"parameter '${param.paramNameOpt}' of function '$funName' has type '$paramType', which is forbidden", param.getPosition)
          })
        bodyEnvir.allow(IdPath(paramName))
      }
      if (param.isReassignable && param.paramNameOpt.isEmpty) {
        reportError("unnamed reassignable parameter", param.getPosition, isWarning = true)
      }
      if (param.isReassignable && paramType.captureDescriptor.coversRoot) {
        reportError("reassignable parameters are not allowed to capture the root capability", param.getPosition)
      }
    }
    val optRetType = optRetTypeTree.map(checkType(_, idsAreFields = false)(using tcCtx, Environment.root, langMode))
    val expRetType = optRetType.getOrElse(VoidType)
    checkStat(body)(using tcCtx, bodyEnvir, langMode, expRetType)
    tcCtx.writeLocalsRelatedWarnings(errorReporter)
  }

  private def checkIsEligibleAsMain(funDef: FunDef): Unit = {
    import ArrayTypeShapeTree as ArrSh
    import PrimitiveTypeShapeTree as PrimSh
    funDef match {
      case FunDef(_, List(Param(_, ArrSh(PrimSh(StringType)), _)), _, _, Visibility.Public, _) => ()
      case _ =>
        val funSig = funDef.getSignatureOpt.get
        val expectedHeader =
          s"${Keyword.Main} ${Keyword.Fn} ${funDef.funName}(${ArrayTypeShape(StringType)}) -> ${funSig.retType}"
        reportError(s"main function should have the following header: $expectedHeader", funDef.getPosition)
    }
  }

  private def checkImport(imp: Import, tcCtx: TypeCheckingContext, langMode: LanguageMode): Unit = imp match {
    case modImp@ParamImport(paramName, paramType) =>
      val tpe = checkType(paramType, idsAreFields = true)(using tcCtx, Environment.root, langMode)
      tcCtx.addLocal(paramName, tpe, modImp.getPosition, isReassignable = false, declHasTypeAnnot = true,
        duplicateVarCallback = { () =>
          reportError(s"duplicate parameter: $paramName", modImp.getPosition)
        },
        forbiddenTypeCallback = { () =>
          reportError(s"module $paramName has type $paramType, which is forbidden", modImp.getPosition)
        }
      )
    case pkgImp@PackageImport(packageId, isMarked) =>
      if (langMode.isOcapEnabled) {
        tcCtx.resolveTypeAs[PackageSignature](packageId) match {
          case None =>
            reportError(s"unknown package: $packageId", imp.getPosition)
          case Some(PackageSignature(id, importedPackages, importedDevices, functions, languageMode))
            if languageMode.isOcapDisabled && !isMarked =>
            reportError(s"imported nocap packages must be marked: $Sharp${Keyword.Package} $id", pkgImp.getPosition)
          case _ => ()
        }
      } else {
        reportError("package import in non-ocap module", pkgImp.getPosition)
      }
    case devImp@DeviceImport(device) =>
      if (langMode.isOcapDisabled) {
        reportError("device import in non-ocap module", devImp.getPosition)
      }
  }

  private def checkType(typeTree: TypeTree, idsAreFields: Boolean)
                       (using tcCtx: TypeCheckingContext, envir: Environment, langMode: LanguageMode): Type = {
    val rawType = typeTree match {
      case capTypeTree@CapturingTypeTree(typeShapeTree, captureDescrTree) =>
        featureIsNotAllowedIfOcapDisabled("capturing types", capTypeTree.getPosition)

        given ShapeAnnotPosition = InsideCapturingType

        val shape = checkTypeShape(typeShapeTree, idsAreFields)
        val descriptor = checkCaptureDescr(captureDescrTree, idsAreFields)
        if (langMode.isOcapEnabled) {
          warnOnNonCapAndRedundantCaptures(captureDescrTree)
        }
        CapturingType(shape, descriptor)
      case typeShapeTree: TypeShapeTree =>
        given ShapeAnnotPosition = OutsideCapturingType

        checkTypeShape(typeShapeTree, idsAreFields)
      case WrapperTypeTree(tpe) => tpe
    }
    rawType.maybeMarked(langMode)
  }

  private def warnOnNonCapAndRedundantCaptures(captureDescrTree: CaptureDescrTree)
                                              (using tcCtx: TypeCheckingContext): Unit = {
    captureDescrTree match {
      case ExplicitCaptureSetTree(capturedExpressions) =>
        var foundNotCap = false
        capturedExpressions.foreach { captExpr =>
          if (captExpr.getType.isPure) {
            reportError("captured expression is not a capability", captExpr.getPosition, isWarning = true)
            foundNotCap = true
          }
        }
        if (!foundNotCap) {
          // do not try to find redundant capabilities if we have already found a problem on this capture set
          captureDescrTree.getResolvedDescrOpt.foreach {
            case CaptureSet(set) =>
              set.find(c => c.isCoveredBy(CaptureSet(set - c)))
                .foreach { capability =>
                  reportError(
                    s"redundant capability: $capability is already covered by the rest of the capture set",
                    captureDescrTree.getPosition,
                    isWarning = true
                  )
                }
            case _ => ()
          }
        }
      case _ => ()
    }
  }

  private def checkTypeShape(typeShapeTree: TypeShapeTree, idsAreFields: Boolean)
                            (using tcCtx: TypeCheckingContext, envir: Environment, langMode: LanguageMode,
                             shapePos: ShapeAnnotPosition): TypeShape = typeShapeTree match {
    case ArrayTypeShapeTree(elemTypeTree) =>
      val elemType = checkType(elemTypeTree, idsAreFields)
      if (elemType.captureDescriptor.coversRoot) {
        reportError("array elements are not allowed to capture the root capability", typeShapeTree.getPosition)
      }
      ArrayTypeShape(elemType)
    case castTargetTypeShapeTree: CastTargetTypeShapeTree =>
      checkCastTargetTypeShape(castTargetTypeShapeTree)
  }

  private def checkCastTargetTypeShape(castTargetTypeShapeTree: CastTargetTypeShapeTree)
                                      (using tcCtx: TypeCheckingContext, langMode: LanguageMode,
                                       shapePos: ShapeAnnotPosition): CastTargetTypeShape = {
    val shape = castTargetTypeShapeTree match {
      case PrimitiveTypeShapeTree(primitiveType) =>
        if (primitiveType == RegionType && langMode.isOcapDisabled) {
          featureIsNotAllowedIfOcapDisabled("region type", castTargetTypeShapeTree.getPosition)
        }
        primitiveType
      case NamedTypeShapeTree(name) =>
        if (!tcCtx.knowsUserDefType(name)) {
          reportError(s"unknown: $name", castTargetTypeShapeTree.getPosition)
        }
        NamedTypeShape(name)
    }
    if (shapePos == OutsideCapturingType && langMode.isOcapEnabled && tcCtx.isUninhabitedForSureWhenNoCaptureDescr(shape)) {
      reportError(s"type is not inhabited: $shape should have a capture descriptor",
        castTargetTypeShapeTree.getPosition, isWarning = true)
    } else if (shapePos == InsideCapturingType && langMode.isOcapEnabled && tcCtx.neverNeedsCapDescr(shape)) {
      reportError(s"unnecessary capture descriptor for $shape", castTargetTypeShapeTree.getPosition, isWarning = true)
    }
    shape
  }

  private def checkCaptureDescr(captureDescrTree: CaptureDescrTree, idsAreFields: Boolean)
                               (using tcCtx: TypeCheckingContext, envir: Environment, langMode: LanguageMode): CaptureDescriptor = {
    val captureDescr = captureDescrTree match {
      case explicitCaptureSetTree: ExplicitCaptureSetTree =>
        given ExprPosition = Captured
        checkCaptureSet(explicitCaptureSetTree, idsAreFields)
      case ImplicitRootCaptureSetTree() => CaptureSet.singletonOfRoot
      case MarkTree() => Mark
    }
    captureDescrTree.setResolvedDescr(captureDescr)
    captureDescr
  }

  private def checkCaptureSet(explicitCaptureSetTree: ExplicitCaptureSetTree, idsAreFields: Boolean)
                             (using tcCtx: TypeCheckingContext, envir: Environment,
                              langMode: LanguageMode, exprPosition: ExprPosition): CaptureSet = {
    CaptureSet(explicitCaptureSetTree.capturedExpressions.flatMap { expr =>
      val exprType = checkExpr(expr)
      if exprType.isPure then None
      else convertToCapturable(expr, Some(errorReporter), idsAreFields)(using tcCtx)
    }.toSet)
  }

  private def checkStat(statement: Statement)
                       (using tcCtx: TypeCheckingContext, envir: Environment,
                        ambientLangMode: LanguageMode, expRetType: Type): Unit = statement match {

    case expr: Expr => checkExpr(expr)

    case Block(stats) =>
      val newCtx = tcCtx.copyForSubScope
      val newEnvir = envir.copyForSubScope
      for stat <- stats do {
        checkStat(stat)(using newCtx, newEnvir)
      }
      newCtx.writeLocalsRelatedWarnings(errorReporter)

    case localDef@LocalDef(localName, optTypeAnnotTree, rhsOpt, isReassignable) =>
      checkNoNameClashWithConstants(localName, localDef.getPosition)
      val inferredTypeOpt = rhsOpt.map(checkExpr)
      val optAnnotType = optTypeAnnotTree.map { typeAnnotTree =>
        val annotType = checkType(typeAnnotTree, idsAreFields = false)(using tcCtx)
        inferredTypeOpt.foreach { inferredType =>
          checkSubtypingConstraint(annotType, inferredType, localDef.getPosition, "local definition")
        }
        annotType
      }
      val isUnionWithoutAnnot = optTypeAnnotTree.isEmpty && inferredTypeOpt.exists(_.isInstanceOf[UnionTypeShape])
      if (isUnionWithoutAnnot) {
        reportError(s"Please provide an explicit type for $localName", localDef.getPosition)
      }
      val actualType =
        if isUnionWithoutAnnot then UndefinedTypeShape
        else optAnnotType.orElse(inferredTypeOpt).getOrElse {
          reportError(s"Please provide a type for uninitialized local $localName", localDef.getPosition)
        }
      if (isReassignable || rhsOpt.isEmpty) {
        forbidRootCapture(actualType, if isReassignable then "var" else "uninitialized val",
          localDef.getPosition)
      }
      localDef.setVarType(actualType)
      tcCtx.addLocal(localName, actualType, localDef.getPosition, isReassignable,
        declHasTypeAnnot = optTypeAnnotTree.isDefined,
        duplicateVarCallback = { () =>
          reportError(s"'$localName' is already defined in this scope", localDef.getPosition)
        }, forbiddenTypeCallback = { () =>
          reportError(s"${localDef.keyword} '$localName' has type '$actualType', which is forbidden", localDef.getPosition)
        })
      envir.allow(IdPath(localName))

    case varAssig@VarAssig(lhs, rhs) =>
      val rhsType = checkExpr(rhs)
      lhs match {
        case varRef@VariableRef(name) =>
          tcCtx.varIsAssigned(name)
          val varType = typeOfLocalOrConst(name, tcCtx, varAssig.getPosition)
          checkSubtypingConstraint(varType, rhsType, varAssig.getPosition, "")
          varRef.setType(varType)
        case indexing@Indexing(indexed, _) =>
          checkExpr(indexing)
          val lhsType = exprMustBeIndexable(indexed.getType, tcCtx, varAssig.getPosition, allowString = false)
          checkSubtypingConstraint(lhsType, rhsType, varAssig.getPosition, "")
        case select@Select(structExpr, selected) =>
          val structType = checkExpr(structExpr)
          val fieldType = checkFieldAccess(structExpr, selected, varAssig.getPosition, mustUpdateField = true)
          checkSubtypingConstraint(fieldType, rhsType, varAssig.getPosition, "")
          select.setType(fieldType)
        case _ =>
          reportError("syntax error: only variables, struct fields and array elements can be assigned", varAssig.getPosition)
      }

    case varModif@VarModif(lhs, rhs, op) =>
      val rhsType = checkExpr(rhs)
      lhs match {
        case varRef@VariableRef(name) =>
          tcCtx.varIsAssigned(name)
          val inPlaceModifiedType = typeOfLocalOrConst(name, tcCtx, varModif.getPosition)
          val operatorRetType = mustExistOperator(inPlaceModifiedType.shape, op, rhsType.shape, varModif.getPosition)
          checkSubtypingConstraint(inPlaceModifiedType, operatorRetType, varModif.getPosition, "")
          varRef.setType(inPlaceModifiedType)
        case indexing@Indexing(indexed, _) =>
          checkExpr(indexing)
          val inPlaceModifiedElemType = exprMustBeIndexable(indexed.getType, tcCtx, varModif.getPosition, allowString = false)
          val operatorRetType = mustExistOperator(inPlaceModifiedElemType.shape, op, rhsType.shape, varModif.getPosition)
          checkSubtypingConstraint(inPlaceModifiedElemType, operatorRetType, varModif.getPosition, "")
        case select@Select(structExpr, selected) =>
          val structType = checkExpr(structExpr)
          val inPlaceModifiedFieldType = checkFieldAccess(structExpr, selected, varModif.getPosition, mustUpdateField = true)
          val operatorRetType = mustExistOperator(inPlaceModifiedFieldType.shape, op, rhsType.shape, varModif.getPosition)
          checkSubtypingConstraint(inPlaceModifiedFieldType, operatorRetType, varModif.getPosition, "")
          select.setType(inPlaceModifiedFieldType)
        case _ =>
          reportError("syntax error: only variables, struct fields and array elements can be assigned", varModif.getPosition)
      }

    case ifThenElse@IfThenElse(cond, thenBr, elseBrOpt) =>
      val condType = checkExpr(cond)
      checkSubtypingConstraint(BoolType, condType.shape, ifThenElse.getPosition, "if condition")
      val smartCasts = detectSmartCasts(cond, tcCtx)
      ifThenElse.setSmartCasts(smartCasts)
      checkStat(thenBr)(using tcCtx.copyWithSmartCasts(smartCasts))
      elseBrOpt.foreach(checkStat)

    case whileLoop@WhileLoop(cond, body) =>
      val condType = checkExpr(cond)
      checkSubtypingConstraint(BoolType, condType.shape, whileLoop.getPosition, "while condition")
      val smartCasts = detectSmartCasts(cond, tcCtx)
      checkStat(body)(using tcCtx.copyWithSmartCasts(smartCasts))

    case forLoop@ForLoop(initStats, cond, stepStats, body) =>
      val newCtx = tcCtx.copyForSubScope
      initStats.foreach(checkStat(_)(using newCtx))
      val condType = checkExpr(cond)(using newCtx)
      checkSubtypingConstraint(BoolType, condType.shape, forLoop.getPosition, "for loop condition")
      val smartCasts = detectSmartCasts(cond, tcCtx)
      val smartCastsAwareCtx = newCtx.copyWithSmartCasts(smartCasts)
      stepStats.foreach(checkStat(_)(using smartCastsAwareCtx))
      checkStat(body)(using smartCastsAwareCtx)
      newCtx.writeLocalsRelatedWarnings(errorReporter)

    case retStat@ReturnStat(valueOpt) =>
      if (tcCtx.insideEnclosure) {
        reportError("return statements are not allowed inside enclosures", retStat.getPosition)
      }
      valueOpt.foreach { value =>
        val retType = checkExpr(value)
        checkSubtypingConstraint(expRetType, retType, retStat.getPosition, "returned value")
      }
      if (expRetType == NothingType) {
        reportError(s"unexpected return in function returning $NothingType", retStat.getPosition)
      } else if (expRetType != VoidType && valueOpt.isEmpty) {
        reportError("expected an expression after return", retStat.getPosition)
      } else if (expRetType == VoidType && valueOpt.isDefined) {
        reportError("unexpected expression after return", valueOpt.get.getPosition)
      }

    case panicStat@PanicStat(msg) =>
      val msgType = checkExpr(msg)
      checkSubtypingConstraint(StringType, msgType, panicStat.getPosition, "panic")

    case restr@RestrictedStat(captureSetTree, body) =>
      featureIsNotAllowedIfOcapDisabled("restricted", restr.getPosition)
      given ExprPosition = Captured
      val captureSet = checkCaptureSet(captureSetTree, idsAreFields = false)
      val innerCtx = tcCtx.copyWithRestriction(captureSet)
      checkStat(body)(using innerCtx, Environment(captureSet, allowEverything = false))

    case encl@EnclosedStat(captureSetTree, body) =>
      featureIsNotAllowedIfOcapDisabled("enclosures", encl.getPosition)
      given ExprPosition = Executable
      val captureSet = checkCaptureSet(captureSetTree, idsAreFields = false)
      for (capability <- captureSetTree.capturedExpressions) {
        val isRegion = capability.getTypeShape == RegionType
        val isDevice = capability.isInstanceOf[DeviceRef]
        val isAllowed = isRegion || isDevice
        if (!isAllowed) {
          reportError(
            s"only regions and devices may appear in the capture set of an enclosed block",
            capability.getPosition
          )
        }
      }
      checkStat(body)(using tcCtx.copyForEnclosure)
  }

  private def checkNoNameClashWithConstants(localName: FunOrVarId, posOpt: Option[Position])
                                           (using tcCtx: TypeCheckingContext): Unit = {
    if (tcCtx.constants.contains(localName)) {
      reportError(s"illegal name for local: $localName is already defined as a constant", posOpt)
    }
  }

  private def checkLiteralExpr(literal: Literal): Type = literal match {
    case _: IntLit => IntType
    case _: DoubleLit => DoubleType
    case _: CharLit => CharType
    case _: BoolLit => BoolType
    case _: StringLit => StringType
  }

  private def checkExpr(expr: Expr)(using tcCtx: TypeCheckingContext, envir: Environment,
                                    ambientLangMode: LanguageMode, exprPos: ExprPosition = Executable): Type = {
    val rawType = expr match {

      case literal: Literal =>
        checkLiteralExpr(literal)

      case regCreation@RegionCreation() =>
        featureIsNotAllowedIfOcapDisabled("regions", regCreation.getPosition)
        RegionType ^ CaptureSet.singletonOfRoot

      case varRef@VariableRef(name) =>
        tcCtx.localIsQueried(name)
        tcCtx.getLocalOrConst(name) match
          case None =>
            reportError(s"unknown: $name", varRef.getPosition)
          case Some(localInfo: LocalInfo) =>
            localInfo.tpe
          case Some(constInfo: ConstantInfo) =>
            varRef.markAsRefToConst()
            constInfo.tpe

      case MeRef() =>
        tcCtx.meType

      case pkg@PackageRef(packageName) =>
        tcCtx.resolveType(packageName) match {
          case Some(packageSignature: PackageSignature) => packageSignature.asType
          case Some(_) => reportError(s"$packageName is not a package and is thus not allowed here", pkg.getPosition)
          case None => reportError(s"not found: $packageName", pkg.getPosition)
        }

      case devRef@DeviceRef(device) =>
        device.tpe

      case call@Call(None, funName, args, isTailrec) =>
        checkFunCall(call, tcCtx.meTypeId, tcCtx.meCaptureDescr, isTailrec)

      case call@Call(Some(receiver), funName, args, isTailrec) =>
        val receiverType = checkExpr(receiver)
        receiverType.shape match {
          case namedType: NamedTypeShape =>
            checkFunCall(call, namedType.typeName, receiverType.captureDescriptor, isTailrec)
          case recType =>
            reportError(s"expected a module or package type, found $recType", receiver.getPosition)
        }

      case indexing@Indexing(indexed, arg) =>
        val indexedType = checkExpr(indexed)
        val argType = checkExpr(arg)
        checkSubtypingConstraint(IntType, argType.shape, indexing.getPosition, "array index")
        val elemType = exprMustBeIndexable(indexed.getType, tcCtx, indexed.getPosition, allowString = true)
        elemType

      case arrayInit@ArrayInit(regionOpt, elemTypeTree, size) =>
        if (elemTypeTree == VoidType || elemTypeTree == NothingType) {
          reportError(s"array cannot have element type $elemTypeTree", arrayInit.getPosition)
        }
        val sizeType = checkExpr(size)
        checkSubtypingConstraint(IntType, sizeType.shape, size.getPosition, "array size")
        size match {
          case IntLit(value) if value < 0 =>
            reportError("array size should be nonnegative", size.getPosition)
          case _ => ()
        }
        val elemType = checkType(elemTypeTree, idsAreFields = false)
        requireAndCheckRegionIffOcapEnabled(regionOpt, arrayInit.getPosition)
        ArrayTypeShape(elemType) ^ regionOpt.map(minimalCaptureSetFor)

      case filledArrayInit@FilledArrayInit(Nil, regionOpt) =>
        reportError("cannot infer type of empty array, use 'arr <type>[0]' instead", filledArrayInit.getPosition)

      case filledArrayInit@FilledArrayInit(arrayElems, regionOpt) =>
        requireAndCheckRegionIffOcapEnabled(regionOpt, filledArrayInit.getPosition)
        val types = arrayElems.map(checkExpr)
        computeJoinOf(types.toSet, tcCtx) match {
          case Some(elemsJoin) =>
            if (elemsJoin.captureDescriptor.coversRoot){
              reportError(s"inferred type $elemsJoin of array elements captures the root capability, which is forbidden", filledArrayInit.getPosition)
            }
            ArrayTypeShape(elemsJoin) ^ regionOpt.map(minimalCaptureSetFor)
          case None =>
            reportError("cannot infer array type", filledArrayInit.getPosition)
        }

      case instantiation@StructOrModuleInstantiation(regionOpt, tid, args) =>
        regionOpt.foreach(checkExpr)
        tcCtx.resolveType(tid) match {
          case Some(sig) if sig.isAbstract =>
            reportError(
              s"$tid is abstract, hence it cannot be instantiated",
              instantiation.getPosition
            )
          case Some(structSig: StructSignature) =>
            if (ambientLangMode.isOcapEnabled && structSig.isShallowMutable && regionOpt.isEmpty) {
              reportError(
                s"cannot instantiate '$tid' without providing a region, since it is a mutable struct",
                instantiation.getPosition
              )
            } else if (ambientLangMode.isOcapEnabled && !structSig.isShallowMutable && regionOpt.isDefined) {
              reportError(
                s"${structSig.id} is not a mutable struct, hence it should not be associated with a region",
                regionOpt.get.getPosition
              )
            }
            checkCallArgs(structSig, structSig.voidInitMethodSig, receiverOpt = None, regionOpt, args,
              isInstantiation = true, instantiation.getPosition)
            NamedTypeShape(tid) ^ computeCaptures(args, regionOpt, structSig)
          case Some(moduleSig: ModuleSignature) =>
            checkCallArgs(moduleSig, moduleSig.voidInitMethodSig, receiverOpt = None, regionOpt = None, args,
              isInstantiation = true, instantiation.getPosition)
            if (ambientLangMode.isOcapEnabled) {
              if (moduleSig.languageMode.isOcapDisabled && !tcCtx.insideEnclosure) {
                reportError("cannot instantiate a non-ocap module outside of an enclosure", instantiation.getPosition)
              }
              for imp <- moduleSig.globalCaptures do {
                if (!envir.allows(imp)) {
                  reportError(s"$imp (imported by ${moduleSig.id}) is not allowed in the current module or restricted block", instantiation.getPosition)
                }
              }
            }
            val cd =
              if moduleSig.languageMode.isOcapEnabled
              then computeCaptures(args, regionOpt, moduleSig)
              else Mark
            NamedTypeShape(tid) ^ cd
          case _ => reportError(s"not found: structure or module '$tid'", instantiation.getPosition)
        }

      case unaryOp@UnaryOp(operator, operand) =>
        val operandType = checkExpr(operand)
        val operandTypeShape = operandType.shape
        if (operator == Len) {
          if (operandTypeShape.isInstanceOf[ArrayTypeShape] || operandTypeShape.subtypeOf(StringType)) {
            IntType
          } else {
            reportError(s"length operator can only be applied to arrays and strings, found '$operandType'", unaryOp.getPosition)
          }
        } else if (operator == Sharp) {
          featureIsNotAllowedIfOcapDisabled("marking operator", unaryOp.getPosition)
          if (ambientLangMode.isOcapEnabled && !tcCtx.insideEnclosure) {
            reportError("marking operator is only allowed inside enclosures", unaryOp.getPosition)
          }
          operandTypeShape ^ Mark
        } else {
          unaryOperatorSignatureFor(operator, operandTypeShape) match {
            case Some(sig) => sig.retType
            case None =>
              reportError(s"no definition of operator '$operator' found for operand '$operandTypeShape'", unaryOp.getPosition)
          }
        }

      case binOp@BinaryOp(lhs, operator, rhs) =>
        val lhsTypeShape = checkExpr(lhs).shape
        val smartCasts = if operator == Operator.And then detectSmartCasts(lhs, tcCtx) else Map.empty
        val rhsTypeShape = checkExpr(rhs)(using tcCtx.copyWithSmartCasts(smartCasts)).shape
        binOp.setSmartCasts(smartCasts)
        if (operator == Equality || operator == Inequality) {
          val isSubOrSupertype = lhsTypeShape.subtypeOf(rhsTypeShape) || rhsTypeShape.subtypeOf(lhsTypeShape)
          if (!isSubOrSupertype) {
            reportError(s"cannot compare '$lhsTypeShape' and '$rhsTypeShape' using ${Equality.str} or ${Inequality.str}", binOp.getPosition)
          }
          BoolType
        } else {
          mustExistOperator(lhsTypeShape, operator, rhsTypeShape, binOp.getPosition)
        }

      case select@Select(lhs, selected) =>
        if (selected == SpecialFields.regFieldId && exprPos == Executable){
          reportError(s"${SpecialFields.regFieldId} field can only be used inside a capturing type, it cannot appear in executable position", select.getPosition)
        }
        val lhsEnvir =
          // if select corresponds to a path, check restrictions only on it, not on its prefixes
          if convertToCapturable(select, erOpt = None, idsAreFields = false).isDefined
          then envir.withEverythingAllowed
          else envir
        val lhsType = checkExpr(lhs)(using tcCtx, lhsEnvir)
        checkFieldAccess(lhs, selected, select.getPosition, mustUpdateField = false)

      case ternary@Ternary(cond, thenBr, elseBr) =>
        val condType = checkExpr(cond)
        checkSubtypingConstraint(BoolType, condType.shape, ternary.getPosition, "ternary operator condition")
        val smartCasts = detectSmartCasts(cond, tcCtx)
        ternary.setSmartCasts(smartCasts)
        val thenType = checkExpr(thenBr)(using tcCtx.copyWithSmartCasts(smartCasts))
        val elseType = checkExpr(elseBr)
        computeJoinOf(Set(thenType, elseType), tcCtx) match {
          case Some(ternaryType) =>
            ternaryType
          case None =>
            reportError(s"cannot infer type of ternary operator: then branch has type '$thenType', " +
              s"else branch has type '$elseType'", ternary.getPosition)
        }

      case cast@Cast(expr, typeTree) =>
        val exprType = checkExpr(expr)

        given ShapeAnnotPosition = InTypeTest

        val srcShape = exprType.shape
        val targetShape = checkCastTargetTypeShape(typeTree)
        if (srcShape.subtypeOf(targetShape)) {
          reportError(s"useless conversion: '$srcShape' --> '$targetShape'", cast.getPosition, isWarning = true)
          cast.markTransparent()
        } else if (TypeConversion.conversionFor(srcShape, targetShape).isEmpty
          && !canPerformNominalCast(srcShape, targetShape, cast.getPosition)) {
          reportError(s"cannot cast '$srcShape' to '$targetShape'", cast.getPosition)
        }
        targetShape ^ exprType.captureDescriptor

      case typeTest@TypeTest(expr, typeTree) =>
        val exprType = checkExpr(expr)

        given ShapeAnnotPosition = InTypeTest

        val srcShape = exprType.shape
        val targetShape = checkCastTargetTypeShape(typeTree)
        if (srcShape.subtypeOf(targetShape)) {
          reportError(s"test will always be true, as '$srcShape' is a subtype of '$targetShape'",
            typeTest.getPosition, isWarning = true)
        } else if (!canPerformNominalCast(srcShape, targetShape, typeTest.getPosition)) {
          reportError(s"cannot check expression of type '$srcShape' against type '$targetShape'", typeTest.getPosition)
        }
        BoolType

      case _: Sequence => throw AssertionError("should not happen, as Sequences are produced by the desugaring phase")
    }
    val tpe = rawType.maybeMarked(ambientLangMode)
    expr.setType(tpe)
    if (ambientLangMode.isOcapEnabled) {
      convertToCapturable(expr, erOpt = None, idsAreFields = false).foreach { exprAsCap =>
        if (!envir.allows(exprAsCap)) {
          reportError(s"$exprAsCap is not allowed in the current module or restricted block", expr.getPosition)
        }
      }
    }
    tpe
  }

  private def requireAndCheckRegionIffOcapEnabled(regionOpt: Option[Expr], posOpt: Option[Position])
                                                 (using ctx: TypeCheckingContext, envir: Environment, langMode: LanguageMode): Unit = {
    regionOpt.foreach(checkExpr)
    (regionOpt, langMode) match {
      case (None, OcapDisabled) => ()
      case (None, OcapEnabled) =>
        reportError("expected a region", posOpt)
      case (Some(_), OcapDisabled) =>
        reportError("unexpected region, as ocap is disabled for this file", posOpt)
      case (Some(region), OcapEnabled) =>
        val regType = region.getType
        checkSubtypingConstraint(PrimitiveTypeShape.RegionType ^ CaptureSet.singletonOfRoot, regType, region.getPosition, "region")
    }
  }

  private def unaryOperatorSignatureFor(operator: Operator, operand: TypeShape)
                                       (using TypeCheckingContext, LanguageMode): Option[UnaryOpSignature] = {
    unaryOperators.find {
      case UnaryOpSignature(op, operandType, _) =>
        operator == op && operand.subtypeOf(operandType)
    }
  }

  private def binaryOperatorSigFor(left: TypeShape, operator: Operator, right: TypeShape)
                                  (using TypeCheckingContext, LanguageMode): Option[BinaryOpSignature] = {
    binaryOperators.find {
      case BinaryOpSignature(leftOperandType, op, rightOperandType, _) =>
        left.subtypeOf(leftOperandType) && op == operator && right.subtypeOf(rightOperandType)
    }
  }

  private def checkFunCall(call: Call, owner: TypeIdentifier, ownerCd: CaptureDescriptor, isTailrec: Boolean)
                          (using tcCtx: TypeCheckingContext, envir: Environment, langMode: LanguageMode): Type = {
    val funName = call.function
    val args = call.args
    val posOpt = call.getPosition
    if (langMode.isOcapEnabled && ownerCd == Mark && !tcCtx.insideEnclosure) {
      reportError(s"cannot invoke function $funName, as its receiver is marked and the invocation occurs outside of an enclosure", posOpt)
    }
    tcCtx.resolveFunc(owner, funName) match {
      case FunctionFound(ownerSig, funSig) =>
        if (funSig.visibility.isPrivate && owner != tcCtx.meTypeId) {
          reportError(s"function $funName is private in $owner", call.getPosition)
        }
        if (isTailrec && !tcCtx.isCurrentFunc(ownerSig.id, funName)) {
          reportError("tail calls can only be used to invoke the enclosing function", call.getPosition)
        }
        call.setResolvedSig(funSig)
        call.cacheMeType(tcCtx.meType)
        val receiver = call.receiverOpt.getOrElse(MeRef().setType(tcCtx.meType))
        checkCallArgs(ownerSig, funSig, Some(receiver), regionOpt = None, args, isInstantiation = false, posOpt)
      case ModuleNotFound =>
        args.foreach(checkExpr)
        reportError(s"not found: package or module $owner", posOpt)
      case FunctionNotFound(typeSig) =>
        args.foreach(checkExpr)
        reportError(s"function not found: '$funName' in '${typeSig.id}'", posOpt)
    }
  }

  private def canPerformNominalCast(srcShape: TypeShape, destShape: TypeShape, posOpt: Option[Position])
                                   (using TypeCheckingContext): Boolean = {
    (srcShape, destShape) match {
      case (srcType: NamedTypeShape, destType: NamedTypeShape) =>
        destType.subtypeOf(srcType) || srcType.subtypeOf(destType)
      case _ => false
    }
  }

  private def checkCallArgs(
                             funOwnerSig: TypeSignature,
                             funSig: FunctionSignature,
                             receiverOpt: Option[Expr],
                             regionOpt: Option[Expr],
                             args: List[Expr],
                             isInstantiation: Boolean,
                             callPos: Option[Position]
                           )(using callerCtx: TypeCheckingContext, envir: Environment, callerLangMode: LanguageMode): Type = {
    val expTypesIter = funSig.args.iterator
    val argsIter = args.iterator
    val calleeCtx = TypeCheckingContext(
      callerCtx.analysisContext,
      meTypeId = funOwnerSig.id,
      meCaptureDescr = funOwnerSig.getNonSubstitutedCaptureDescr,
      currFunIdOpt = Some(funSig.name),
      insideEnclosure = false,
      currentRestriction = CaptureSet.singletonOfRoot
    )
    regionOpt.foreach { region =>
      calleeCtx.addLocal(SpecialFields.regFieldId, RegionType ^ CaptureSet.singletonOfRoot,
        defPos = None, isReassignable = false, declHasTypeAnnot = false, () => (), () => ())
    }
    val substitutor = PathsSubstitutor(calleeCtx, errorReporter)
    for {
      receiver <- receiverOpt
      receiverPath <- convertToCapturable(receiver, erOpt = None, idsAreFields = false)
    } do {
      substitutor(MePath) = receiverPath
    }
    for {
      region <- regionOpt
      regionPath <- convertToCapturable(region, erOpt = None, idsAreFields = false)
    } do {
      substitutor(MePath.dot(SpecialFields.regFieldId)) = regionPath
    }
    var errorFound = false
    while (expTypesIter.hasNext && argsIter.hasNext && !errorFound) {
      val (paramNameOpt, expTypeRaw) = expTypesIter.next()
      val arg = argsIter.next()
      val expTypeSubst = substitutor.subst(expTypeRaw, arg.getPosition)
      val actType = checkExpr(arg)
      errorFound |= !checkSubtypingConstraint(expTypeSubst, actType, arg.getPosition, "")
      paramNameOpt.foreach { paramName =>
        calleeCtx.addLocal(paramName, expTypeSubst, defPos = None, isReassignable = false,
          declHasTypeAnnot = true, () => (), () => ())
      }
      for {
        paramName <- paramNameOpt
        argPath <- convertToCapturable(arg, erOpt = None, idsAreFields = false)
      } do {
        val target = if isInstantiation then MePath.dot(paramName) else IdPath(paramName)
        substitutor(target) = argPath
      }
    }
    if (expTypesIter.hasNext && !errorFound) {
      reportError(s"expected argument of type '${expTypesIter.next()._2}', found end of arguments list", callPos)
    }
    if (argsIter.hasNext && !errorFound) {
      val arg = argsIter.next()
      reportError(s"expected end of arguments list, found argument of type '${checkExpr(arg)}'", arg.getPosition)
    }
    for arg <- argsIter do {
      checkExpr(arg)
    }
    substitutor.subst(funSig.retType, callPos)
  }

  private def computeCaptures(args: List[Expr], regionOpt: Option[Expr], sig: ConstructibleSig)
                             (using TypeCheckingContext): CaptureDescriptor = {
    val paramsIter = sig.regularParams.iterator
    args.foldLeft[CaptureDescriptor](CaptureSet(sig.globalCaptures.toSet: Set[Capturable])) { (cd, arg) =>
      cd.union(
        paramsIter.nextOption().map { (fieldId, fieldInfo) =>
          if fieldInfo.isReassignable
          then fieldInfo.tpe.captureDescriptor.mapSet(_.filter(_.isInstanceOf[GlobalCapturable]))
          else minimalCaptureSetFor(arg)
        }.getOrElse(minimalCaptureSetFor(arg))
      )
    }.union(regionOpt.map(minimalCaptureSetFor))
  }

  private def detectSmartCasts(expr: Expr, ctx: TypeCheckingContext): Map[FunOrVarId, Type] = {
    expr match {
      case BinaryOp(lhs, Operator.And, rhs) =>
        // concat order is reversed because we want to keep the leftmost type test in case of conflict
        detectSmartCasts(rhs, ctx) ++ detectSmartCasts(lhs, ctx)
      case TypeTest(varRef@VariableRef(varName), typeTree) if ctx.getLocalOnly(varName).exists(!_.isReassignable) =>
        typeTree.getResolvedTypeOpt.map { tpe =>
          Map(varName -> (tpe ^ varRef.getType.captureDescriptor))
        }.getOrElse(Map.empty)
      case _ => Map.empty
    }
  }

  private def typeOfLocalOrConst(name: FunOrVarId, ctx: TypeCheckingContext, posOpt: Option[Position]): Type = {
    ctx.getLocalOrConst(name) match
      case None =>
        reportError(s"unknown: $name", posOpt)
      case Some(info) => info.tpe
  }

  private def exprMustBeIndexable(
                                   exprType: Type,
                                   ctx: TypeCheckingContext,
                                   posOpt: Option[Position],
                                   allowString: Boolean
                                 ): Type = {
    exprType.shape match
      case ArrayTypeShape(elemType) => elemType
      case StringType if allowString => CharType
      case _ =>
        val expectedDescr = if allowString then "an array or a string" else "an array"
        reportError(s"expected $expectedDescr, found '$exprType'", posOpt)
  }

  private def mustExistOperator(lhsTypeShape: TypeShape, operator: Operator, rhsTypeShape: TypeShape, position: Option[Position])
                               (using TypeCheckingContext, LanguageMode): Type = {
    binaryOperatorSigFor(lhsTypeShape, operator, rhsTypeShape) match {
      case Some(sig) => sig.retType
      case None =>
        reportError(s"no definition of operator '$operator' found for operands '$lhsTypeShape' and '$rhsTypeShape'", position)
    }
  }

  private def checkFieldAccess(
                                receiver: Expr,
                                fieldName: FunOrVarId,
                                posOpt: Option[Position],
                                mustUpdateField: Boolean
                              )(using callerCtx: TypeCheckingContext, langMode: LanguageMode): Type = {

    val receiverCaptOpt = convertToCapturable(receiver, erOpt = None, idsAreFields = false)

    def performSubstIfApplicable(rawType: Type, structOrModuleSignature: ConstructibleSig): Type = {
      val calleeCtx = TypeCheckingContext(
        callerCtx.analysisContext,
        meTypeId = structOrModuleSignature.id,
        meCaptureDescr = structOrModuleSignature.getNonSubstitutedCaptureDescr,
        currFunIdOpt = None,
        insideEnclosure = false,
        currentRestriction = CaptureSet.singletonOfRoot
      )
      for ((paramName, fieldInfo) <- structOrModuleSignature.params) {
        calleeCtx.addLocal(paramName, fieldInfo.tpe, None, false, true, () => (), () => ())
      }
      val substitutor = PathsSubstitutor(calleeCtx, errorReporter)
      receiverCaptOpt.foreach { recvCapt =>
        substitutor(MePath) = recvCapt
      }
      substitutor.subst(rawType, receiver.getPosition)
    }

    val exprType = receiver.getType
    exprType.shape match {
      case NamedTypeShape(typeName) =>
        callerCtx.resolveType(typeName) match {
          case Some(structSig@StructSignature(_, isShallowMutable, fields, _, _, structLangMode)) if fields.contains(fieldName) =>
            val FieldInfo(fieldType, fieldIsReassig, _) = fields.apply(fieldName)
            val missingFieldMutability = mustUpdateField && !fieldIsReassig
            if (missingFieldMutability) {
              reportError(s"cannot update immutable field '$fieldName'", posOpt)
            }
            performSubstIfApplicable(fieldType, structSig)
          case Some(modSig: ModuleSignature) if modSig.paramImports.contains(fieldName) =>
            if (!receiver.isInstanceOf[MeRef]) {
              reportError(s"references to module imports are only allowed when using the '${Keyword.Me}' keyword", posOpt)
            }
            if (mustUpdateField) {
              reportError("cannot update module field", posOpt)
            }
            performSubstIfApplicable(modSig.paramImports.apply(fieldName), modSig)
          case _ =>
            reportError(s"'$exprType' has no field named '$fieldName'", posOpt)
        }
      case _ =>
        reportError(s"'$exprType' has no field named '$fieldName'", posOpt)
    }
  }

  private def checkSubtypingConstraint(
                                        expected: Type,
                                        actual: Type,
                                        posOpt: Option[Position],
                                        msgPrefix: String
                                      )(using ctx: TypeCheckingContext, langMode: LanguageMode): Boolean = {

    def reportWithPrefix(expected: Type, actual: Type): Unit = {
      val fullprefix = if msgPrefix == "" then "" else (msgPrefix ++ ": ")
      reportError(fullprefix ++ s"expected '$expected', found '$actual'", posOpt)
    }

    if (expected.shape != UndefinedTypeShape && actual.shape != UndefinedTypeShape) {
      if (langMode.isOcapDisabled && !actual.shape.subtypeOf(expected.shape)) {
        // in nocap mode, display only shapes if marks are not necessary to understand the error
        reportWithPrefix(expected.shape, actual.shape)
        false
      } else if (!actual.subtypeOf(expected)) {
        reportWithPrefix(expected, actual)
        false
      } else true
    } else true
  }

  private def computeJoinOf(types: Set[Type], ctx: TypeCheckingContext)(using LanguageMode): Option[Type] = {
    computeJoinOfShapes(types.map(_.shape), ctx).map { joinShape =>
      val cd = CaptureDescriptors.unionOf(types.map(_.captureDescriptor))
      joinShape ^ cd
    }
  }

  private def computeJoinOfShapes(types: Set[TypeShape], ctx: TypeCheckingContext)(using LanguageMode): Option[TypeShape] = {
    require(types.nonEmpty)
    if types.size == 1 then Some(types.head)
    else if (areAllStructs(types, ctx)) {
      val structs = ctx.structs
      // if the structs have exactly 1 direct supertype in common, infer it as the result type
      val directSupertypesSets = types.map { tpe =>
        structs.apply(tpe.shape.asInstanceOf[NamedTypeShape].typeName).directSupertypes.toSet
      }
      val commonDirectSupertypes = directSupertypesSets.reduceLeft(_.intersect(_))
      Some(
        if commonDirectSupertypes.size == 1
        then {
          val superT = commonDirectSupertypes.head
          NamedTypeShape(superT)
        } else {
          UnionTypeShape(types.map(_.shape))
        }
      )
    } else {
      // type Nothing should be accepted
      // e.g. in 'when ... then 0 else (panic "")'
      types.find { commonSuper =>
        types.forall(_.subtypeOf(commonSuper)(using ctx))
      }
    }
  }

  private def areAllStructs(types: Set[TypeShape], ctx: TypeCheckingContext): Boolean = {
    types.forall {
      case NamedTypeShape(typeName) => ctx.resolveType(typeName).exists(_.isInstanceOf[StructSignature])
      case _ => false
    }
  }

  private def minimalCaptureSetFor(expr: Expr)(using TypeCheckingContext): CaptureDescriptor = {
    if expr.getType.isPure then CaptureSet.empty
    else convertToCapturable(expr, erOpt = None, idsAreFields = false) map { path =>
      CaptureSet(path)
    } getOrElse {
      expr.getType.captureDescriptor
    }
  }

  private def featureIsNotAllowedIfOcapDisabled(featureDescr: String, posOpt: Option[Position])(using langMode: LanguageMode): Unit = {
    if (langMode.isOcapDisabled) {
      reportError(featureDescr + " should not be used, as ocap is disabled in the current file", posOpt)
    }
  }

  private def reportError(msg: String, pos: Option[Position], isWarning: Boolean = false): UndefinedTypeShape.type = {
    errorReporter.push(if isWarning then Warning(TypeChecking, msg, pos) else Err(TypeChecking, msg, pos))
    UndefinedTypeShape
  }

}
