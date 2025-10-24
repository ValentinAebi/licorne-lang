package compiler.analysisctx

import compiler.importscanner.ModuleImports
import compiler.irs.Asts.*
import compiler.pipeline.CompilationStep.ContextCreation
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecker.SubtypeRelation.subtypeOf
import compiler.typechecker.TypeCheckingContext
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.*
import lang.Capturables.*
import lang.CaptureDescriptors.CaptureSet
import lang.Types.*
import lang.Types.PrimitiveTypeShape.{NothingType, VoidType}

import scala.collection.mutable

final class AnalysisContextBuilder(errorReporter: ErrorReporter) {
  private val modules: mutable.Map[TypeIdentifier, ModuleSignature] = mutable.Map.empty
  private val packages: mutable.Map[TypeIdentifier, (PackageSignature, Option[Position])] =
    mutable.Map.from(Device.values.map { device =>
      device.typeName -> (PackageSignature(
        id = device.typeName,
        importedPackages = mutable.LinkedHashSet.empty,
        importedDevices = mutable.LinkedHashSet.empty,
        functions = device.api.functions
      ), None)
    })
  private val structs: mutable.Map[TypeIdentifier, (StructSignature, Option[Position])] = mutable.Map.empty
  private val constants: mutable.Map[FunOrVarId, Type] = mutable.Map.empty

  def addModule(moduleDef: ModuleDef): Unit = {
    val moduleName = moduleDef.moduleName
    if (checkTypeNotAlreadyDefined(moduleName, moduleDef.getPosition)) {
      val (importedModules, importedPackages, importedDevices) = analyzeImports(moduleDef)
      val functions = extractFunctions(moduleDef)
      val moduleSig = ModuleSignature(moduleName, importedModules, importedPackages, importedDevices, functions)
      modules.put(moduleName, moduleSig)
    }
  }

  def addPackage(packageDef: PackageDef)(using imports: Map[TypeIdentifier, ModuleImports]): Unit = {
    val packageName = packageDef.packageName
    if (checkTypeNotAlreadyDefined(packageName, packageDef.getPosition)) {
      val functions = extractFunctions(packageDef)
      val (implicitlyImportedPackages, implicitlyImportedDevices) = trackPackagesAndDevices(packageDef)
      val sig = PackageSignature(packageName, implicitlyImportedPackages, implicitlyImportedDevices, functions)
      packages.put(packageName, (sig, packageDef.getPosition))
    }
  }

  def addStruct(structDef: StructDef): Unit = {
    val name = structDef.structName
    if (checkTypeNotAlreadyDefined(name, structDef.getPosition)) {
      val fieldsMap = buildStructFieldsMap(structDef)
      val directSubtypesOpt =
        if structDef.isAbstract
        then Some(mutable.LinkedHashSet.empty[TypeIdentifier])
        else None
      val sig = StructSignature(name, fieldsMap, structDef.directSupertypes, directSubtypesOpt)
      structs.put(name, (sig, structDef.getPosition))
    }
  }

  def addConstant(constDef: ConstDef): Unit = {
    import constDef.constName
    if (constants.contains(constName)) {
      reportError(s"redefinition of constant $constName", constDef.getPosition)
    } else {
      // type is already known since value is a Literal
      constants(constName) = constDef.value.getType
    }
  }

  def build(): AnalysisContext = {
    val builtCtx = new AnalysisContext(
      modules.toMap,
      packages.map((tid, sigAndPos) => (tid, sigAndPos._1)).toMap,
      structs.map((tid, sigAndPos) => (tid, sigAndPos._1)).toMap,
      constants.toMap
    )
    checkAndResolveSubstructuring(builtCtx)
    checkSubtypingCycles(builtCtx.structs)
    checkPackageCycles(builtCtx.packages)
    builtCtx
  }

  private def extractFunctions(modOrMkg: ModuleOrPackageDefTree): Map[FunOrVarId, FunctionSignature] = {
    val functions = mutable.Map.empty[FunOrVarId, FunctionSignature]
    for funDef <- modOrMkg.functions do {
      val name = funDef.funName
      if (functions.contains(name)) {
        reportError(s"redefinition of function '$name'", funDef.getPosition)
      } else {
        val funSig = computeFunctionSig(funDef)
        functions.put(name, funSig)
        funDef.setSignature(funSig)
      }
    }
    functions.toMap
  }

  private def computeFunctionSig(funDef: FunDef): FunctionSignature = {
    val argsTypesB = List.newBuilder[(Option[FunOrVarId], Type)]
    for (Param(paramNameOpt, tpe, isReassignable) <- funDef.params) {
      argsTypesB.addOne(paramNameOpt, computeType(tpe, idsAreFields = false))
    }
    val retType = funDef.optRetType.map(computeType(_, idsAreFields = false)).getOrElse(VoidType)
    FunctionSignature(funDef.funName, argsTypesB.result(), retType, funDef.visibility)
  }

  private def computeType(typeTree: TypeTree, idsAreFields: Boolean): Type = {
    typeTree match {
      case CapturingTypeTree(typeShapeTree, captureDescr) =>
        CapturingType(computeTypeShape(typeShapeTree, idsAreFields), computeCaptureDescr(captureDescr, idsAreFields))
      case typeShapeTree: TypeShapeTree =>
        computeTypeShape(typeShapeTree, idsAreFields)
      case WrapperTypeTree(tpe) => tpe
    }
  }

  private def computeTypeShape(typeShapeTree: TypeShapeTree, idsAreFields: Boolean)
                              : TypeShape = typeShapeTree match {
    case ArrayTypeShapeTree(elemType) => ArrayTypeShape(computeType(elemType, idsAreFields))
    case castTargetTypeShapeTree: CastTargetTypeShapeTree => computeCastTargetTypeShape(castTargetTypeShapeTree)
  }

  private def computeCastTargetTypeShape(castTargetTypeShapeTree: CastTargetTypeShapeTree)
                                        : CastTargetTypeShape = {
    castTargetTypeShapeTree match
      case PrimitiveTypeShapeTree(primitiveType) => primitiveType
      case NamedTypeShapeTree(name) => NamedTypeShape(name)
  }

  private def computeCaptureDescr(cdTree: CaptureSetTree, idsAreFields: Boolean): CaptureSet = cdTree match {
    case ExplicitCaptureSetTree(capturedExpressions) =>
      // checks that the expression is indeed capturable are delayed to the type-checker
      CaptureSet(capturedExpressions.flatMap(mkCapturableOrFailSilently(_, idsAreFields)).toSet)
    case ImplicitRootCaptureSetTree() =>
      CaptureSet.singletonOfRoot
  }

  private def analyzeImports(moduleDef: ModuleDef) = {
    val importsMap = new mutable.LinkedHashMap[FunOrVarId, Type]()
    val packagesSet = new mutable.LinkedHashSet[TypeIdentifier]()
    val devicesSet = new mutable.LinkedHashSet[Device]()
    moduleDef.imports.foreach {
      case ParamImport(instanceId, moduleType) =>
        importsMap.put(instanceId, computeType(moduleType, idsAreFields = true))
      case PackageImport(packageId) =>
        packagesSet.add(packageId)
      case DeviceImport(device) =>
        devicesSet.add(device)
    }
    (importsMap, packagesSet, devicesSet)
  }

  private def trackPackagesAndDevices(pkg: PackageDef)(using imports: Map[TypeIdentifier, ModuleImports]) = {
    val packages = mutable.LinkedHashSet[TypeIdentifier]()
    val devices = mutable.LinkedHashSet[Device]()
    pkg.collect {
      case PackageRef(packageName) if packageName != pkg.packageName =>
        packages.add(packageName)
      case DeviceRef(device) =>
        devices.add(device)
      case StructOrModuleInstantiation(typeId, args) =>
        imports.get(typeId).foreach { modImport =>
          packages.addAll(modImport.packages)
          devices.addAll(modImport.devices)
        }
      case _ => ()
    }
    (packages, devices)
  }

  private def buildStructFieldsMap(structDef: StructDef)
                                  : mutable.LinkedHashMap[FunOrVarId, FieldInfo] = {
    val fieldsMap = new mutable.LinkedHashMap[FunOrVarId, FieldInfo]()
    for param <- structDef.fields do {
      param.paramNameOpt match {
        case None =>
          reportError("struct fields must be named", param.getPosition)
        case Some(paramName) =>
          val tpe = computeType(param.tpe, idsAreFields = true)
          if (checkIsNotVoidOrNothing(tpe, param.getPosition)) {
            if (!fieldsMap.contains(paramName)) {
              // the presence of duplicate fields will be reported by the type-checker
              fieldsMap.put(paramName, FieldInfo(tpe, param.isReassignable))
            }
          }
      }
    }
    fieldsMap
  }

  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    errorReporter.push(Err(ContextCreation, msg, posOpt))
  }

  private def checkTypeNotAlreadyDefined(tid: TypeIdentifier, posOpt: Option[Position]): Boolean = {
    val alreadyDefined = structs.contains(tid) || modules.contains(tid) || packages.contains(tid)
    if (alreadyDefined) {
      reportError(s"$tid is already defined", posOpt)
    }
    !alreadyDefined
  }

  private def checkIsNotVoidOrNothing(tpe: Type, posOpt: Option[Position]): Boolean = {
    val isVoidOrNothing = tpe == VoidType || tpe == NothingType
    if (isVoidOrNothing) {
      reportError(s"type $tpe is illegal at this place", posOpt)
    }
    !isVoidOrNothing
  }

  /**
   * Create a capturable for the given expression, without performing any check
   * (e.g. it won't reject a capture of a variable). These checks should be performed by the type-checker instead.
   * If the expression is obviously not capturable (e.g. a call), return None
   */
  private def mkCapturableOrFailSilently(expr: Expr, idsAreFields: Boolean): Option[Capturable] = expr match {
    case VariableRef(name) => Some(if idsAreFields then MePath.dot(name) else IdPath(name))
    case MeRef() => Some(MePath)
    case PackageRef(pkgName) => Some(CapPackage(pkgName))
    case DeviceRef(device) => Some(CapDevice(device))
    case Select(lhs, selected) =>
      mkCapturableOrFailSilently(lhs, idsAreFields).flatMap {
        case p: Path => Some(SelectPath(p, selected))
        case _ => None
      }
    case _ => None
  }

  private def checkAndResolveSubstructuring(builtCtx: AnalysisContext): Unit = {
    for {
      (structId, (structSig, structDefPosOpt)) <- structs
      directSupertypeId <- structSig.directSupertypes
    } {
      structs.get(directSupertypeId) match {
        case Some((directSupertypeSig, supertypeDefPosOpt)) => {
          if (structDefPosOpt.get.srcCodeProviderName != supertypeDefPosOpt.get.srcCodeProviderName) {
            reportError("only datatypes defined in the same source file can be used as supertypes", structDefPosOpt)
          } else {
            directSupertypeSig.directSubtypesOpt.foreach(_.add(structId))
          }
          if (directSupertypeSig.isAbstract) {
            // TODO carefully check what happens here
            // i.e. what elements each field is allowed to capture (fields of the super-/subtype)
            // and what me refers to
            val tcCtx = TypeCheckingContext(
              analysisContext = builtCtx,
              meTypeId = structId,
              meCaptureDescr = structSig.getNonSubstitutedCaptureDescr,
              currFunIdOpt = None,
              insideEnclosure = false,
              currentRestriction = CaptureSet.singletonOfRoot
            )
            for ((fldName, superFldInfo) <- directSupertypeSig.fields) {
              structSig.fields.get(fldName) match {
                case Some(subFieldInfo) =>
                  if (subFieldInfo.isReassignable != superFldInfo.isReassignable) {
                    reportError(s"'$fldName' should be reassignable in '$structId' if and only if it is " +
                      s"reassignable in its supertype '$directSupertypeId'", structDefPosOpt)
                  } else if (subFieldInfo.isReassignable && subFieldInfo.tpe != superFldInfo.tpe) {
                    reportError(s"reassignable field '$fldName' should have the same type in '$structId' as in its " +
                      s"supertype '$directSupertypeId'", structDefPosOpt)
                  } else if (
                    !subFieldInfo.isReassignable
                      && !subFieldInfo.tpe.subtypeOf(superFldInfo.tpe)(using tcCtx)
                  ) {
                    reportError(s"type '${subFieldInfo.tpe}' of field '$fldName' does not conform to its type " +
                      s"'${superFldInfo.tpe}' in its supertype '$directSupertypeId'", structDefPosOpt)
                  }
                case None =>
                  reportError(s"$structId cannot subtype '$directSupertypeId': missing field '$fldName'", structDefPosOpt)
              }
              tcCtx.addLocal(fldName, superFldInfo.tpe, None, superFldInfo.isReassignable, true, () => (), () => ())
            }
          } else {
            reportError(
              s"struct '$directSupertypeId' is not an abstract datatype, hence it cannot be used as a supertype",
              structDefPosOpt
            )
          }
        }
        case None =>
          reportError(s"datatype '$directSupertypeId' is unknown", structDefPosOpt)
      }
    }
  }

  private def checkPackageCycles(builtPackagesMap: Map[TypeIdentifier, PackageSignature]): Unit = {
    findCycle(builtPackagesMap.keys.toSeq.sortBy(_.stringId),
      tid =>
        builtPackagesMap.get(tid).toList.flatMap(_.importedPackages)
        .filter(imp => builtPackagesMap.contains(imp))
    ).foreach { cycle =>
      val posOpt = packages.get(cycle.head).flatMap(_._2)
      reportError("ocap packages do not compose in an ocap-compliant manner: cyclic dependency found that involves " +
        "the following packages: " + cycle.init.mkString(", "), posOpt)
    }
  }

  private def checkSubtypingCycles(builtStructMap: Map[TypeIdentifier, StructSignature]): Unit = {
    findCycle(builtStructMap.keys.toSeq.sortBy(_.stringId),
      tid => builtStructMap.get(tid).toList.flatMap(_.directSupertypes).sortBy(_.stringId)
    ).foreach { cycle =>
      val posOpt = structs.get(cycle.head).flatMap(_._2)
      reportError("cycle found in datastruct subtyping: " + cycle.mkString(" <: "), posOpt)
    }
  }

  private def findCycle[V](roots: Iterable[V], getAdjSet: V => Iterable[V]): Option[Seq[V]] = {
    val alreadyFound = mutable.Set.empty[V]
    val cycleStack = mutable.Stack.empty[V]
    val inStack = mutable.Set.empty[V]

    var found = false

    def exploreFrom(v: V): Unit = {
      if (!found && inStack(v)){
        found = true
        cycleStack.push(v)
      } else if (!found && !alreadyFound(v)){
        alreadyFound.add(v)
        cycleStack.push(v)
        inStack.add(v)
        for u <- getAdjSet(v) do {
          exploreFrom(u)
        }
        if (!found){
          inStack.remove(v)
          cycleStack.pop()
        }
      }
    }

    val iter = roots.iterator
    while (!found && iter.hasNext){
      val root = iter.next()
      exploreFrom(root)
    }
    if (found){
      val origin = cycleStack.head
      val reversedBackPathFromOrigin = origin :: cycleStack.tail.takeWhile(_ != origin).toList
      Some(origin :: reversedBackPathFromOrigin.reverse)
    } else None
  }

}