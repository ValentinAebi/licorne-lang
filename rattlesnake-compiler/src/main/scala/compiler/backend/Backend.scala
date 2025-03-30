package compiler.backend

import compiler.analysisctx.AnalysisContext
import compiler.backend.DescriptorsCreator.{descriptorForFunc, descriptorForType}
import compiler.backend.TypesConverter.{convertToAsmType, convertToAsmTypeCode, internalNameOf, numSlotsFor, opcodeFor}
import compiler.gennames.ClassesAndDirectoriesNames.{agentSubdirName, packageInstanceName}
import compiler.gennames.{ClassesAndDirectoriesNames, FileExtensions}
import compiler.irs.Asts.*
import compiler.pipeline.CompilationStep.CodeGeneration
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.*
import compiler.reporting.Position
import identifiers.*
import lang.*
import lang.CaptureDescriptors.CaptureSet
import lang.Operator.*
import lang.Types.PrimitiveTypeShape.*
import lang.Types.{ArrayTypeShape, NamedTypeShape, PrimitiveTypeShape, TypeShape, UnionTypeShape}
import org.objectweb.asm
import org.objectweb.asm.*
import org.objectweb.asm.Opcodes.*
import org.objectweb.asm.util.TraceClassVisitor

import java.io.{File, FileInputStream, FileOutputStream, PrintWriter}
import java.nio.file.{Files, Path}
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.util.{Failure, Success, Using}

/**
 * Generates the output files: 1 core file, containing the program, and 1 file per struct
 *
 * @param mode          cf nested class [[Backend.Mode]]
 * @param outputDirBase output directory path (will be extended with `/out`)
 * @tparam V depends on the mode
 */
final class Backend[V <: ClassVisitor](
                                        mode: Backend.Mode[V],
                                        errorReporter: ErrorReporter,
                                        outputDirBase: Path,
                                        javaVersionCode: Int,
                                        runtimeDirPath: Path,
                                        agentDirPath: Path
                                      ) extends CompilerStep[(List[Source], AnalysisContext), List[TypeIdentifier]] {

  private val javaTypesMapping: Map[PrimitiveTypeShape, String] = Map(
    IntType -> "Integer",
    DoubleType -> "Double",
    CharType -> "Character",
    BoolType -> "Boolean"
  )
  
  private var lastWrittenLine = -1

  import Backend.*

  override def apply(input: (List[Source], AnalysisContext)): List[TypeIdentifier] = {
    val (sources, analysisContext) = input
    if (sources.isEmpty) {
      errorReporter.pushFatal(Fatal(CodeGeneration, "nothing to write: no sources", None))
    } else {
      val modulesAndPackagesBuilder = List.newBuilder[TypeDefTree]
      val structsBuilder = List.newBuilder[StructDef]
      val constsBuilder = List.newBuilder[ConstDef]
      for src <- sources; df <- src.defs do {
        df match
          case modOrPkg: ModuleOrPackageDefTree => modulesAndPackagesBuilder.addOne(modOrPkg)
          case structDef: StructDef => structsBuilder.addOne(structDef)
          case constDef: ConstDef => constsBuilder.addOne(constDef)
      }

      // sort the structs so that no class is loaded before its super-interfaces
      val modulesAndPackages = modulesAndPackagesBuilder.result()
      val structs = sortStructs(structsBuilder.result())
      val consts = constsBuilder.result()

      // create output directory if it does not already exist
      val outputDirPath = outputDirBase.resolve("out")
      val outputDirFile = outputDirPath.toFile
      if (outputDirFile.exists()) {
        deleteDirTree(outputDirFile)
      }
      Files.createDirectories(outputDirPath)

      given AnalysisContext = analysisContext

      val mainClassNames = mutable.ListBuffer.empty[TypeIdentifier]

      generateTypes(modulesAndPackages, outputDirPath, mainClassNames)
      generateTypes(structs, outputDirPath, mainClassNames)

      if (consts.nonEmpty) {
        val constantsFilePath = outputDirPath.resolve(mode.withExtension(ClassesAndDirectoriesNames.constantsClassName))
        generateConstantsFile(consts, constantsFilePath)
      }

      if (mode.generateRuntime) {
        copyJar(runtimeDirPath, "rattlesnake-runtime", outputDirPath)
        copyJar(agentDirPath, "rattlesnake-agent", outputDirPath.resolve(agentSubdirName))
      }

      errorReporter.displayAndTerminateIfErrors()
      mainClassNames.toList
    }

  }

  private def deleteDirTree(root: File): Unit = {
    if (root.isDirectory){
      for (subFile <- root.listFiles()){
        deleteDirTree(subFile)
      }
    } else {
      Files.delete(root.toPath)
    }
  }

  private def copyJar(srcDirPath: Path, jarNamePrefix: String, destDirPath: Path): Unit = try {
    val jarFileName = JarFinder.findNameOfJarInDir(srcDirPath.toFile, jarNamePrefix).get
    val jarSrcFilePath = srcDirPath.resolve(jarFileName)
    val jarDestFilePath = destDirPath.resolve(jarFileName)
    Files.createDirectories(destDirPath)
    Using(new FileInputStream(jarSrcFilePath.toFile)) { srcStream =>
      Using(new FileOutputStream(jarDestFilePath.toFile)) { destStream =>
        srcStream.transferTo(destStream)
      }.get
    }.get
  } catch {
    case thr: Throwable =>
      throw new Error(s"Could not copy jar (name starting with $jarNamePrefix). ", thr)
  }

  /**
   * Topological sort on the subtyping relation: each supertype appears before its subtypes
   */
  private def sortStructs(structs: List[StructDef]): List[StructDef] = {
    val remStructs = mutable.Queue.from(structs)
    val sortedList = new mutable.LinkedHashMap[TypeIdentifier, StructDef]
    while (remStructs.nonEmpty) {
      // get is safe here because the subtyping relation admits no cycles (checked by ContextCreation phase)
      val curr = remStructs.removeFirst(_.directSupertypes.forall(sortedList.contains)).get
      sortedList.addOne(curr.structName -> curr)
    }
    sortedList.toList.map(_._2)
  }

  private def generateConstantsFile(consts: List[ConstDef], constantsFilePath: Path)
                                   (using AnalysisContext): Unit = {
    val ccv: V = mode.createVisitor(constantsFilePath)
    addSourceName(ccv, "<auto-gen-constants-file>")
    ccv.visit(javaVersionCode, ACC_PUBLIC, ClassesAndDirectoriesNames.constantsClassName, null, objectTypeStr, null)
    for const <- consts do {
      ccv.visitField(
        ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
        const.constName.stringId,
        descriptorForType(const.value.getTypeShape),
        null,
        const.value.value
      )
    }
    ccv.visitEnd()
    mode.terminate(ccv, constantsFilePath, errorReporter)
  }

  private def generateModuleOrPackageFile(modOrPkg: ModuleOrPackageDefTree, path: Path)(using ctx: AnalysisContext): Boolean = {
    val modOrPkgSig = ctx.resolveTypeAs[ConstructibleSig](modOrPkg.name).get
    val cv: V = mode.createVisitor(path)
    addSourceNameIfKnown(cv, modOrPkg.getPosition)
    cv.visit(javaVersionCode, ACC_PUBLIC | ACC_FINAL, modOrPkg.name.stringId, null, objectTypeStr, null)
    val constructorVisibility = if modOrPkg.isPackage then ACC_PRIVATE else ACC_PUBLIC
    addConstructor(cv, constructorVisibility, modOrPkgSig)
    val pkgTypeDescr = descriptorForType(NamedTypeShape(modOrPkg.name))
    if (modOrPkg.isInstanceOf[PackageDef]) {
      addInstanceFieldAndInitializer(modOrPkg, cv, pkgTypeDescr)
    }
    for (varId, moduleType) <- modOrPkgSig.asInstanceOf[ImporterSig].paramImports do {
      cv.visitField(ACC_PRIVATE, varId.stringId, descriptorForType(moduleType.shape), null, null)
    }
    var isMainClass = false
    for func <- modOrPkg.functions do {
      val funSig = func.getSignatureOpt.get
      val desc = descriptorForFunc(funSig)
      val visibility = if func.visibility.isPrivate then ACC_PRIVATE else ACC_PUBLIC
      val mv = cv.visitMethod(visibility, func.funName.stringId, desc, null, null)
      addFunction(modOrPkg.name, func, mv, ctx)
      if (func.isMain) {
        isMainClass = true
        val staticMv = cv.visitMethod(ACC_PUBLIC | ACC_STATIC, "main", desc, null, null)
        generateStaticMainFunction(staticMv, modOrPkg.name, funSig)
      }
    }
    cv.visitEnd()
    mode.terminate(cv, path, errorReporter)
    isMainClass
  }

  private def generateStaticMainFunction(mv: MethodVisitor, pkgName: TypeIdentifier, delegateFunSig: FunctionSignature)(using AnalysisContext): Unit = {
    mv.visitCode()
    mv.visitFieldInsn(Opcodes.GETSTATIC, pkgName.stringId, packageInstanceName, descriptorForType(NamedTypeShape(pkgName)))
    mv.visitVarInsn(Opcodes.ALOAD, 0)
    mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, pkgName.stringId, delegateFunSig.name.stringId,
      descriptorForFunc(delegateFunSig), false)
    val retType = delegateFunSig.retType
    if (retType != VoidType && retType != NothingType){
      mv.visitInsn(if TypesConverter.numSlotsFor(retType.shape) == 1 then Opcodes.POP else Opcodes.POP2)
    }
    mv.visitInsn(Opcodes.RETURN)
    mv.visitMaxs(0, 0)
    mv.visitEnd()
  }

  private def addInstanceFieldAndInitializer(modOrPkg: ModuleOrPackageDefTree, cv: V, pkgTypeDescr: String): Unit = {
    val pkgName = modOrPkg.name.stringId
    cv.visitField(
      ACC_PUBLIC | ACC_STATIC,
      packageInstanceName,
      pkgTypeDescr,
      null,
      null
    )
    val mv = cv.visitMethod(
      ACC_PRIVATE | ACC_STATIC,
      "<clinit>",
      "()V",
      null,
      null
    )
    mv.visitCode()
    mv.visitTypeInsn(Opcodes.NEW, pkgName)
    mv.visitInsn(Opcodes.DUP)
    mv.visitMethodInsn(Opcodes.INVOKESPECIAL, pkgName, ConstructorFunId.stringId, "()V", false)
    mv.visitFieldInsn(Opcodes.PUTSTATIC, pkgName, packageInstanceName, pkgTypeDescr)
    mv.visitInsn(Opcodes.RETURN)
    mv.visitMaxs(0, 0)
    mv.visitEnd()
  }

  private def addFunction(owner: TypeIdentifier, funDef: FunDef, mv: MethodVisitor, analysisContext: AnalysisContext): Unit = {
    val funStartLabel = new Label()
    val ctx = CodeGenerationContext.from(analysisContext, owner, funStartLabel)
    ctx.addLocal(MeVarId, NamedTypeShape(owner))
    val unnamedParamIdx = new AtomicInteger(0)
    for param <- funDef.params do {
      param.paramNameOpt match {
        case None =>
          ctx.addLocal(BackendGeneratedVarId(unnamedParamIdx.incrementAndGet()), param.tpe.getResolvedType)
        case Some(paramName) =>
          ctx.addLocal(paramName, param.tpe.getResolvedType)
      }
    }
    lastWrittenLine = -1
    mv.visitCode()
    mv.visitLabel(funStartLabel)
    generateCode(funDef.body, ctx)(using mv)
    if (ctx.resolveFunc(owner, funDef.funName).getFunSigOrThrow().retType == VoidType) {
      mv.visitInsn(Opcodes.RETURN)
    }
    mv.visitMaxs(0, 0) // arguments are ignored because mode is COMPUTE_FRAMES
    mv.visitEnd()
  }

  private def generateTypes(
                             types: List[TypeDefTree],
                             outputDir: Path,
                             mainClassesList: mutable.ListBuffer[TypeIdentifier]
                           )(using AnalysisContext): Unit = {
    for tpe <- types do {
      val classFilePath = outputDir.resolve(mode.withExtension(tpe.name.stringId))
      tpe match {
        case struct: StructDef =>
          val datatypes = struct.directSupertypes.map(_.stringId).toArray
          generateStruct(struct, datatypes, classFilePath)
        case modOrPkg: ModuleOrPackageDefTree =>
          val isMain = generateModuleOrPackageFile(modOrPkg, classFilePath)
          if (isMain){
            mainClassesList.addOne(tpe.name)
          }
      }
    }
  }

  private def generateStruct(structDef: StructDef, superDatatypes: Array[String],
                             structFilePath: Path)(using ctx: AnalysisContext): Unit = {
    val structName = structDef.structName
    val structSig = ctx.structs.apply(structName)
    val isAbstract = structSig.isAbstract
    val cv = mode.createVisitor(structFilePath)
    addSourceNameIfKnown(cv, structDef.getPosition)
    var classMods = ACC_PUBLIC
    if (isAbstract) {
      classMods |= ACC_INTERFACE
      classMods |= ACC_ABSTRACT
    } else {
      classMods |= ACC_FINAL
    }
    cv.visit(javaVersionCode, classMods, structDef.structName.stringId, null, objectTypeStr, superDatatypes)
    if (!isAbstract) {
      addFields(structDef, cv)
      addConstructor(cv, Opcodes.ACC_PUBLIC, structSig)
    }
    val fieldsWithAccessors =
      if isAbstract
      then structSig.fields.keySet
      else getInheritedFieldsForStruct(structName, ctx.structs)
    for (fld <- fieldsWithAccessors) {
      val fldType = structSig.fields.apply(fld).tpe
      val fieldDescr = descriptorForType(fldType.shape)
      generateGetter(structName, fld, fldType, fieldDescr, cv, genImplementation = !isAbstract)
      if (structSig.fields.apply(fld).isReassignable) {
        generateSetter(structName, fld, fldType, fieldDescr, cv, genImplementation = !isAbstract)
      }
    }
    cv.visitEnd()
    mode.terminate(cv, structFilePath, errorReporter)
  }

  private def generateGetter(structName: TypeIdentifier, fld: FunOrVarId, fldType: Types.Type,
                             fieldDescr: String, cv: ClassVisitor, genImplementation: Boolean)
                            (using AnalysisContext): Unit = {
    val getterDescriptor = descriptorForFunc(List.empty, fldType)
    var modifiers = ACC_PUBLIC
    if (!genImplementation) {
      modifiers |= ACC_ABSTRACT
    }
    val getterVisitor = cv.visitMethod(modifiers, fld.stringId,
      getterDescriptor, null, null)
    if (genImplementation) {
      getterVisitor.visitCode()
      getterVisitor.visitVarInsn(Opcodes.ALOAD, 0)
      getterVisitor.visitFieldInsn(Opcodes.GETFIELD, structName.stringId, fld.stringId, fieldDescr)
      getterVisitor.visitInsn(opcodeFor(fldType.shape, Opcodes.IRETURN, Opcodes.ARETURN))
      getterVisitor.visitMaxs(0, 0) // parameters are ignored because mode is COMPUTE_FRAMES
    }
    getterVisitor.visitEnd()
  }

  private def generateSetter(structName: TypeIdentifier, fld: FunOrVarId, fldType: Types.Type,
                             fieldDescr: String, cv: ClassVisitor, genImplementation: Boolean)
                            (using AnalysisContext): Unit = {
    val setterDescriptor = descriptorForFunc(List(None -> fldType), PrimitiveTypeShape.VoidType)
    var modifiers = ACC_PUBLIC
    if (!genImplementation) {
      modifiers |= ACC_ABSTRACT
    }
    val setterVisitor = cv.visitMethod(modifiers, fld.stringId, setterDescriptor, null, null)
    if (genImplementation) {
      setterVisitor.visitCode()
      setterVisitor.visitVarInsn(Opcodes.ALOAD, 0)
      setterVisitor.visitVarInsn(opcodeFor(fldType.shape, Opcodes.ILOAD, Opcodes.ALOAD), 1)
      setterVisitor.visitFieldInsn(Opcodes.PUTFIELD, structName.stringId, fld.stringId, fieldDescr)
      setterVisitor.visitInsn(Opcodes.RETURN)
      setterVisitor.visitMaxs(0, 0) // parameters are ignored because mode is COMPUTE_FRAMES
    }
    setterVisitor.visitEnd()
  }

  private def addConstructor(
                              cv: ClassVisitor,
                              visibility: Int,
                              typeSig: ConstructibleSig
                            )(using AnalysisContext): Unit = {
    val constructorDescr = descriptorForFunc(typeSig.voidInitMethodSig)
    val constructorVisitor = cv.visitMethod(visibility, ConstructorFunId.stringId, constructorDescr, null, null)
    constructorVisitor.visitCode()
    constructorVisitor.visitVarInsn(Opcodes.ALOAD, 0)
    constructorVisitor.visitMethodInsn(Opcodes.INVOKESPECIAL, "java/lang/Object", ConstructorFunId.stringId, "()V", false)
    var varIdx = 1
    for ((fldName, fldInfo) <- typeSig.regularParams) do {
      val tpe = fldInfo.tpe
      val descr = descriptorForType(tpe.shape)
      constructorVisitor.visitVarInsn(Opcodes.ALOAD, 0)
      constructorVisitor.visitIntInsn(opcodeFor(tpe.shape, Opcodes.ILOAD, Opcodes.ALOAD), varIdx)
      constructorVisitor.visitFieldInsn(Opcodes.PUTFIELD, typeSig.id.stringId, fldName.stringId, descr)
      varIdx += numSlotsFor(tpe.shape)
    }
    constructorVisitor.visitInsn(Opcodes.RETURN)
    constructorVisitor.visitMaxs(0, 0) // parameters are ignored because mode is COMPUTE_FRAMES
    constructorVisitor.visitEnd()
  }

  private def addFields(structDef: StructDef, cv: ClassVisitor)
                       (using AnalysisContext): Unit = {
    for field <- structDef.fields do {
      val fieldVisitor = cv.visitField(
        Opcodes.ACC_PUBLIC,
        field.paramNameOpt.get.stringId,
        descriptorForType(field.tpe.getResolvedType.shape),
        null,
        null
      )
      fieldVisitor.visitEnd()
    }
  }

  private def getInheritedFieldsForStruct(structId: TypeIdentifier, structs: Map[TypeIdentifier, StructSignature]): Set[FunOrVarId] = {
    // BFS

    val fields = mutable.Set.empty[FunOrVarId]
    val workList = mutable.Queue.empty[TypeIdentifier]
    val alreadyAdded = mutable.Set.empty[TypeIdentifier]

    workList.addAll(structs.apply(structId).directSupertypes)
    while (workList.nonEmpty) {
      val curr = structs(workList.dequeue())
      fields.addAll(curr.fields.keys)
      val toAdd = curr.directSupertypes.filterNot(alreadyAdded.contains)
      workList.addAll(toAdd)
      alreadyAdded.addAll(toAdd)
    }
    fields.toSet
  }

  private def generateCode(ast: Ast, ctx: CodeGenerationContext)
                          (using mv: MethodVisitor): Unit = {

    val analysisContext = ctx.analysisContext

    given AnalysisContext = analysisContext

    ast.getPosition.map(_.line).foreach { currentLine =>
      if (currentLine != lastWrittenLine) {
        val label = new Label()
        mv.visitLabel(label)
        mv.visitLineNumber(currentLine, label)
        lastWrittenLine = currentLine
      }
    }

    ast match {

      case Block(stats) => generateSequence(ctx, stats, optFinalExpr = None)
      case Sequence(stats, expr) => generateSequence(ctx, stats, Some(expr))

      case localDef@LocalDef(varName, tpeOpt, rhsOpt, _) =>
        rhsOpt.foreach { rhs =>
          generateCode(rhs, ctx)
          val opcode = opcodeFor(rhs.getTypeShape, Opcodes.ISTORE, Opcodes.ASTORE)
          mv.visitVarInsn(opcode, ctx.currLocalIdx)
        }
        ctx.addLocal(varName, localDef.getVarTypeOpt.get)

      case IntLit(value) => mv.visitLdcInsn(value)
      case DoubleLit(value) => mv.visitLdcInsn(value)
      case CharLit(value) => mv.visitLdcInsn(value)
      case BoolLit(value) => mv.visitLdcInsn(if value then 1 else 0)
      case StringLit(value) => mv.visitLdcInsn(value)

      case regionCreation: RegionCreation =>
        RuntimeMethod.NewRegion.generateCall(mv)

      case varRef@VariableRef(name) => {
        ctx.getLocal(name) match
          case Some((tpe, localIdx)) =>
            val opCode = opcodeFor(tpe.shape, Opcodes.ILOAD, Opcodes.ALOAD)
            mv.visitVarInsn(opCode, localIdx)
          case None =>
            mv.visitFieldInsn(
              Opcodes.GETSTATIC,
              ClassesAndDirectoriesNames.constantsClassName,
              name.stringId,
              descriptorForType(varRef.getTypeShape)
            )
      }

      case MeRef() =>
        mv.visitIntInsn(opcodeFor(NamedTypeShape(ctx.currentModule), Opcodes.ILOAD, Opcodes.ALOAD), 0)

      case PackageRef(name) =>
        val packageShapeType = NamedTypeShape(name)
        val internalName = internalNameOf(packageShapeType)
        val descr = descriptorForType(packageShapeType)
        mv.visitFieldInsn(Opcodes.GETSTATIC, internalName, packageInstanceName, descr)

      case DeviceRef(device) =>
        val className = device.typeName.stringId
        val classDescr = s"L$className;"
        mv.visitFieldInsn(Opcodes.GETSTATIC, className, "$INSTANCE", classDescr)

      case Call(_, funName, args, isTailrec) if isTailrec => {
        for (arg <- args) {
          generateCode(arg, ctx)
        }
        val argsIndices = 1 to args.size
        for ((arg, idx) <- args.zip(argsIndices).reverse) {
          val opcode = opcodeFor(arg.getTypeShape, Opcodes.ISTORE, Opcodes.ASTORE)
          mv.visitIntInsn(opcode, idx)
        }
        mv.visitJumpInsn(Opcodes.GOTO, ctx.functionStartLabel)
      }

      case Call(None, funName, args, isTailrec) => shouldNotHappen()

      case call@Call(Some(receiver), funName, args, isTailrec) => {
        generateCode(receiver, ctx)
        for arg <- args do {
          generateCode(arg, ctx)
        }
        val receiverShape = receiver.getTypeShape
        val recvInternalName = internalNameOf(receiverShape)
        val receiverTypeName = receiverShape.asInstanceOf[NamedTypeShape].typeName
        val funDescr = descriptorForFunc(ctx.resolveFunc(receiverTypeName, funName).getFunSigOrThrow())
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, recvInternalName, funName.stringId, funDescr, false)
        if (call.getSignatureOpt.get.retType == NothingType) {
          mv.visitInsn(Opcodes.ACONST_NULL)
          mv.visitInsn(Opcodes.ATHROW)
        }
      }

      case Indexing(indexed, arg) if indexed.getTypeShape == StringType =>
        generateCode(indexed, ctx)
        generateCode(arg, ctx)
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/lang/String", "charAt", "(I)C", false)

      case Indexing(indexed, arg) =>
        generateCode(indexed, ctx)
        generateCode(arg, ctx)
        val elemType = indexed.getTypeShape.asInstanceOf[ArrayTypeShape].elemType
        val opcode = opcodeFor(elemType.shape, Opcodes.IALOAD, Opcodes.AALOAD)
        mv.visitInsn(opcode)
        if (isObjectShape(elemType.shape)) {
          // detect loading of null value from array
          val afterCheckLabel = new Label()
          mv.visitInsn(Opcodes.DUP)
          mv.visitJumpInsn(Opcodes.IFNONNULL, afterCheckLabel)
          mv.visitTypeInsn(NEW, "java/lang/RuntimeException")
          mv.visitInsn(DUP)
          mv.visitLdcInsn("array cell has not been initialized")
          mv.visitMethodInsn(Opcodes.INVOKESPECIAL, "java/lang/RuntimeException",
            ConstructorFunId.stringId, s"(L$stringTypeStr;)V", false)
          mv.visitInsn(Opcodes.ATHROW)
          mv.visitLabel(afterCheckLabel)
        }

      case arrayInit@ArrayInit(regionOpt, elemTypeTree, size) =>
        val elemType = elemTypeTree.getResolvedType
        regionOpt.foreach(generateCode(_, ctx))
        generateCode(size, ctx)
        elemType.shape match {
          case _: (PrimitiveTypeShape.StringType.type | NamedTypeShape | ArrayTypeShape | UnionTypeShape) =>
            mv.visitTypeInsn(Opcodes.ANEWARRAY, internalNameOf(elemType.shape))
          case _: Types.PrimitiveTypeShape =>
            val elemTypeCode = convertToAsmTypeCode(elemType.shape).get
            mv.visitIntInsn(Opcodes.NEWARRAY, elemTypeCode)
          case Types.UndefinedTypeShape => shouldNotHappen()
        }
        regionOpt.foreach { _ =>
          mv.visitInsn(Opcodes.DUP_X1)
          mv.visitInsn(Opcodes.SWAP)
          RuntimeMethod.SaveObjectInRegion.generateCall(mv)
        }

      case StructOrModuleInstantiation(regionOpt, tid, args) =>
        val constructorSig = ctx.resolveTypeAs[ConstructibleSig](tid).get.voidInitMethodSig
        val constructorDescr = descriptorForFunc(constructorSig)
        mv.visitTypeInsn(Opcodes.NEW, tid.stringId)
        mv.visitInsn(Opcodes.DUP)
        for (arg <- args) {
          generateCode(arg, ctx)
        }
        mv.visitMethodInsn(Opcodes.INVOKESPECIAL, tid.stringId, ConstructorFunId.stringId, constructorDescr, false)
        regionOpt.foreach { region =>
          mv.visitInsn(Opcodes.DUP)
          generateCode(region, ctx)
          RuntimeMethod.SaveObjectInRegion.generateCall(mv)
        }

      case UnaryOp(operator, operand) =>
        generateCode(operand, ctx)
        operator match {
          case Minus if operand.getTypeShape == IntType =>
            mv.visitInsn(Opcodes.INEG)
          case Minus if operand.getTypeShape == DoubleType =>
            mv.visitInsn(Opcodes.DNEG)
          case Len if operand.getTypeShape.isInstanceOf[ArrayTypeShape] =>
            mv.visitInsn(Opcodes.ARRAYLENGTH)
          case Len if operand.getTypeShape == StringType =>
            mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, stringTypeStr, "length", "()I", false)
          case Sharp => ()
          case _ => throw new AssertionError(s"unexpected $operator in code generation")
        }

      case BinaryOp(lhs, operator, rhs) => {
        generateCode(lhs, ctx)
        generateCode(rhs, ctx)
        val tpe = lhs.getTypeShape
        if (operator == Equality && tpe == StringType) {
          mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, stringTypeStr, "equals", "(Ljava/lang/Object;)Z", false)
        } else if (operator == Equality && tpe == DoubleType) {
          /*
           *   if (lhs compare rhs) == 0 goto trueLabel:
           *   push false
           *   goto endLabel
           * trueLabel:
           *   push true
           * endLabel:
           */
          val trueLabel = new Label()
          val endLabel = new Label()
          mv.visitInsn(Opcodes.DCMPL)
          mv.visitJumpInsn(Opcodes.IFEQ, trueLabel)
          mv.visitInsn(Opcodes.ICONST_0)
          mv.visitJumpInsn(Opcodes.GOTO, endLabel)
          mv.visitLabel(trueLabel)
          mv.visitInsn(Opcodes.ICONST_1)
          mv.visitLabel(endLabel)
        } else if (operator == Equality) {
          /*
           *   if lhs == rhs goto trueLabel:
           *   push false
           *   goto endLabel
           * trueLabel:
           *   push true
           * endLabel:
           */
          val trueLabel = new Label()
          val endLabel = new Label()
          val opcode = if tpe.isInstanceOf[NamedTypeShape] then Opcodes.IF_ACMPEQ else Opcodes.IF_ICMPEQ
          mv.visitJumpInsn(opcode, trueLabel)
          mv.visitInsn(Opcodes.ICONST_0)
          mv.visitJumpInsn(Opcodes.GOTO, endLabel)
          mv.visitLabel(trueLabel)
          mv.visitInsn(Opcodes.ICONST_1)
          mv.visitLabel(endLabel)
        } else if ((operator == LessThan || operator == LessOrEq) && tpe == IntType) {
          /*
           *   if_icmplt/e trueLabel  (goto trueLabel if lhs <(=) rhs)
           *   push false
           *   goto endLabel
           * trueLabel:
           *   push true
           * endLabel:
           */
          val trueLabel = new Label()
          val endLabel = new Label()
          val cmpInsn = if operator == LessThan then Opcodes.IF_ICMPLT else Opcodes.IF_ICMPLE
          mv.visitJumpInsn(cmpInsn, trueLabel)
          mv.visitInsn(Opcodes.ICONST_0)
          mv.visitJumpInsn(Opcodes.GOTO, endLabel)
          mv.visitLabel(trueLabel)
          mv.visitInsn(Opcodes.ICONST_1)
          mv.visitLabel(endLabel)
        } else if ((operator == LessThan || operator == LessOrEq) && tpe == DoubleType) {
          /*
           *   dcmpg  (returns -1 if lhs < rhs, 0 if lhs == rhs)
           *   if < 0 goto trueLabel
           *   push false
           *   goto endLabel
           * trueLabel:
           *   push true
           * endLabel:
           */
          mv.visitInsn(Opcodes.DCMPG)
          val trueLabel = new Label()
          val endLabel = new Label()
          val cmpInsn = if operator == LessThan then Opcodes.IFLT else Opcodes.IFLE
          mv.visitJumpInsn(cmpInsn, trueLabel)
          mv.visitInsn(Opcodes.ICONST_0)
          mv.visitJumpInsn(Opcodes.GOTO, endLabel)
          mv.visitLabel(trueLabel)
          mv.visitInsn(Opcodes.ICONST_1)
          mv.visitLabel(endLabel)
        } else if (operator == Plus && tpe == StringType) {
          mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/lang/String", "concat",
            "(Ljava/lang/String;)Ljava/lang/String;", false)
        } else {
          val intOpcode = operator match {
            case Plus => Opcodes.IADD
            case Minus => Opcodes.ISUB
            case Times => Opcodes.IMUL
            case Div => Opcodes.IDIV
            case Modulo => Opcodes.IREM
            case _ => throw new AssertionError(s"unexpected $operator in backend")
          }
          val opcode = opcodeFor(tpe.shape, intOpcode, shouldNotHappen())
          mv.visitInsn(opcode)
        }
      }

      case Select(lhs, SpecialFields.regFieldId) =>
        shouldNotHappen()

      case Select(lhs, selected) =>
        generateCode(lhs, ctx)
        val typeName = lhs.getTypeShape.asInstanceOf[NamedTypeShape].typeName
        val fieldType =
          analysisContext.structs.get(typeName).map(_.fields.apply(selected).tpe)
            .getOrElse(analysisContext.modules.apply(typeName).paramImports.apply(selected))
        if (ctx.structs.get(typeName).exists(_.isAbstract)) {
          val getterDescriptor = descriptorForFunc(List.empty, fieldType)
          mv.visitMethodInsn(Opcodes.INVOKEINTERFACE, typeName.stringId, selected.stringId, getterDescriptor, true)
        } else {
          mv.visitFieldInsn(Opcodes.GETFIELD, typeName.stringId, selected.stringId, descriptorForType(fieldType.shape))
        }

      case VarAssig(lhs, rhs) =>
        lhs match {

          // x = ...
          case VariableRef(name) =>
            generateCode(rhs, ctx)
            val (varType, varIdx) = ctx.getLocal(name).get // cannot be a constant since it is an assignment
            val opcode = opcodeFor(varType.shape, Opcodes.ISTORE, Opcodes.ASTORE)
            mv.visitVarInsn(opcode, varIdx)

          // x[y] = ...
          case Indexing(indexed, arg) =>
            generateCode(indexed, ctx)
            generateCode(arg, ctx)
            generateCode(rhs, ctx)
            val elemType = indexed.getTypeShape.asInstanceOf[ArrayTypeShape].elemType
            mv.visitInsn(opcodeFor(elemType.shape, Opcodes.IASTORE, Opcodes.AASTORE))

          // x.y = ...
          case Select(ownerStruct, fieldName) =>
            generateCode(ownerStruct, ctx)
            generateCode(rhs, ctx)
            val ownerTypeName = ownerStruct.getTypeShape.asInstanceOf[NamedTypeShape].typeName
            val structSig = ctx.structs.apply(ownerTypeName)
            val fieldType = structSig.fields.apply(fieldName).tpe
            if (structSig.isAbstract) {
              val setterDescriptor = descriptorForFunc(List(None -> fieldType), PrimitiveTypeShape.VoidType)
              mv.visitMethodInsn(Opcodes.INVOKEINTERFACE, ownerTypeName.stringId, fieldName.stringId, setterDescriptor, true)
            } else {
              mv.visitFieldInsn(
                Opcodes.PUTFIELD,
                ownerTypeName.stringId,
                fieldName.stringId,
                descriptorForType(fieldType.shape)
              )
            }

          case _ => shouldNotHappen()
        }

      case ite@IfThenElse(cond, thenBr, elseBrOpt) =>
        /*
         *   if !cond goto falseLabel
         *   <thenBr>
         *   goto endLabel
         * falseLabel:
         *   <elseBr>
         * endLabel:
         */
        generateIfThenElse(ite, ctx)

      case ternary@Ternary(cond, thenBr, elseBr) =>
        generateIfThenElse(ternary, ctx)

      case whileLoop@WhileLoop(BoolLit(true), body) =>
        /*
         * loopLabel:
         *   <body>
         *   goto loopLabel
         */
        val loopLabel = new Label()
        mv.visitLabel(loopLabel)
        generateCode(body, ctx)
        mv.visitJumpInsn(Opcodes.GOTO, loopLabel)

      case whileLoop@WhileLoop(cond, body) =>
        /*
         * loopLabel:
         *   if !cond goto endLabel
         *   <body>
         *   goto loopLabel
         * endLabel:
         */
        val loopLabel = new Label()
        val endLabel = new Label()
        mv.visitLabel(loopLabel)
        generateCode(cond, ctx)
        mv.visitJumpInsn(Opcodes.IFLE, endLabel)
        generateCode(body, ctx)
        mv.visitJumpInsn(Opcodes.GOTO, loopLabel)
        mv.visitLabel(endLabel)

      case ReturnStat(Some(value)) =>
        generateCode(value, ctx)
        val opcode = opcodeFor(value.getTypeShape, Opcodes.IRETURN, Opcodes.ARETURN)
        mv.visitInsn(opcode)

      case ReturnStat(None) =>
        mv.visitInsn(Opcodes.RETURN)

      case cast@Cast(expr, tpe) => {
        generateCode(expr, ctx)
        if (!cast.isTransparentCast) {
          val resolvedType = tpe.getResolvedType
          TypeConversion.conversionFor(expr.getTypeShape, resolvedType) match
            case Some(TypeConversion.Int2Double) => mv.visitInsn(Opcodes.I2D)
            case Some(TypeConversion.Double2Int) => mv.visitInsn(Opcodes.D2I)
            case Some(TypeConversion.IntToChar) => mv.visitInsn(Opcodes.I2C)
            case Some(TypeConversion.CharToInt) => ()
            case Some(conv) =>
              val javaType = javaTypesMapping.apply(conv.from)
              val typeDescriptor = descriptorForType(conv.from)
              mv.visitMethodInsn(Opcodes.INVOKESTATIC, s"java/lang/$javaType", "toString",
                s"($typeDescriptor)Ljava/lang/String;", false)
            case None => mv.visitTypeInsn(Opcodes.CHECKCAST, internalNameOf(resolvedType.shape))
        }
      }

      case TypeTest(expr, tpe) => {
        generateCode(expr, ctx)
        mv.visitTypeInsn(Opcodes.INSTANCEOF, internalNameOf(tpe.getResolvedType.shape))
      }

      case PanicStat(msg) =>
        // throw an exception
        mv.visitTypeInsn(NEW, "java/lang/RuntimeException")
        mv.visitInsn(DUP)
        generateCode(msg, ctx)
        mv.visitMethodInsn(Opcodes.INVOKESPECIAL, "java/lang/RuntimeException",
          ConstructorFunId.stringId, s"(L$stringTypeStr;)V", false)
        mv.visitInsn(Opcodes.ATHROW)

      case RestrictedStat(capabilities, body) =>
        generateCode(body, ctx)

      case EnclosedStat(ExplicitCaptureSetTree(capturedExpressions), body) =>
        RuntimeMethod.StartPreparingEnvir.generateCall(mv)
        capturedExpressions.foreach {
          case DeviceRef(Device.Console) =>
            RuntimeMethod.AllowConsole.generateCall(mv)
          case DeviceRef(Device.FileSystem) =>
            RuntimeMethod.AllowFilesystem.generateCall(mv)
          case capExpr =>
            generateCode(capExpr, ctx)
            RuntimeMethod.AllowRegion.generateCall(mv)
        }
        RuntimeMethod.PushEnvir.generateCall(mv)
        generateCode(body, ctx)
        RuntimeMethod.PopEnvir.generateCall(mv)


      case other => throw new AssertionError(s"unexpected in backend: ${other.getClass}")
    }
  }

  private def generateSequence(ctx: CodeGenerationContext, stats: List[Statement], optFinalExpr: Option[Expr])
                              (using mv: MethodVisitor): Unit = {
    val newCtx = ctx.withNewLocalsFrame
    for stat <- stats do {
      generateCode(stat, newCtx)
      // if unused value put on the stack then drop it
      stat match {
        case expr: Expr if expr.getTypeShape != VoidType => mv.visitInsn(Opcodes.POP)
        case _ => ()
      }
    }
    optFinalExpr.foreach { finalExpr =>
      generateCode(finalExpr, newCtx)
      // do not drop that value since it is the resulting value of the sequence
    }
  }

  private def generateIfThenElse(
                                  conditional: Conditional,
                                  ctx: CodeGenerationContext
                                )(using mv: MethodVisitor): Unit = {
    /*
    * if !cond then goto falseLabel
    *    <then branch>
    *    goto endLabel
    * falseLabel:
    *    <else branch>
    * endLabel:
    */
    generateCode(conditional.cond, ctx)
    val falseLabel = new Label()
    val endLabel = new Label()
    mv.visitJumpInsn(Opcodes.IFLE, falseLabel)
    generateSmartCasts(conditional.getSmartCasts, ctx)
    generateCode(conditional.thenBr, ctx)
    mv.visitJumpInsn(Opcodes.GOTO, endLabel)
    mv.visitLabel(falseLabel)
    conditional.elseBrOpt.foreach(generateCode(_, ctx))
    mv.visitLabel(endLabel)
  }

  private def generateSmartCasts(smartCasts: Map[FunOrVarId, Types.Type], ctx: CodeGenerationContext)
                                (using mv: MethodVisitor): Unit = {
    for (varId, destType) <- smartCasts do {
      // typechecker has already checked that varId is not a constant
      val (originType, varIdx) = ctx.getLocal(varId).get
      mv.visitIntInsn(Opcodes.ALOAD, varIdx)
      mv.visitTypeInsn(Opcodes.CHECKCAST, internalNameOf(destType.shape)(using ctx.analysisContext))
      mv.visitIntInsn(Opcodes.ASTORE, varIdx)
    }
  }

  private def isObjectShape(shape: TypeShape): Boolean = convertToAsmTypeCode(shape).isEmpty

  private def addSourceNameIfKnown(cv: ClassVisitor, posOpt: Option[Position]): Unit = {
    posOpt.foreach { pos =>
      addSourceName(cv, pos.srcCodeProviderName)
    }
  }

  private def addSourceName(cv: ClassVisitor, srcName: String): Unit = {
    cv.visitSource(srcName, null)
  }

  private def shouldNotHappen(): Nothing = assert(false)

}

object Backend {

  private val objectTypeStr = "java/lang/Object"
  private val stringTypeStr = "java/lang/String"

  /**
   * Each mode injects specific behavior into the Backend where it differs between binary generation and textual bytecode generation
   */
  sealed trait Mode[V <: ClassVisitor] {
    val extension: String

    def generateRuntime: Boolean

    def createVisitor(path: Path): V

    def terminate(visitor: V, path: Path, errorReporter: ErrorReporter): Unit

    final def withExtension(filename: String): String = s"$filename.$extension"
  }

  /**
   * Use this mode to generate JVM binaries (.class)
   */
  case object BinaryMode extends Mode[ClassWriter] {

    override val extension: String = FileExtensions.binary

    override def generateRuntime: Boolean = true

    override def createVisitor(path: Path): ClassWriter = {
      new ClassWriter(ClassWriter.COMPUTE_FRAMES) {
        override def getCommonSuperClass(type1: String, type2: String): String = objectTypeStr
      }
    }

    override def terminate(visitor: ClassWriter, path: Path, errorReporter: ErrorReporter): Unit = {
      val file = path.toFile
      file.createNewFile()
      val status = Using(new FileOutputStream(file)) { fileOutputStream =>
        fileOutputStream.write(visitor.toByteArray)
        fileOutputStream.flush()
      }
      status match
        case Success(_) => ()
        case Failure(exception) =>
          errorReporter.push(Err(CodeGeneration, exception.getMessage, None))
    }
  }

  /**
   * Use this mode to generate textual JVM bytecode files
   */
  case object AssemblyMode extends Mode[TraceClassVisitor] {

    override val extension: String = FileExtensions.assembly

    override def generateRuntime: Boolean = false

    override def createVisitor(path: Path): TraceClassVisitor = {
      val file = path.toFile
      file.createNewFile()
      new TraceClassVisitor(new PrintWriter(file))
    }

    override def terminate(visitor: TraceClassVisitor, path: Path, errorReporter: ErrorReporter): Unit = {
      // nothing to do
    }
  }

}
