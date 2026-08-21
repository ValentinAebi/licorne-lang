package compiler.backend

import compiler.backend.Boxing.boxDesc
import compiler.gennames.FileExtensions
import compiler.identifiers.TypeIdentifier
import compiler.irs.ssa.Formulas.{Formula, IdValue, IntermediateIdValue, NamedIdValue}
import compiler.irs.ssa.SSA.*
import compiler.irs.ssa.{Formulas, SSA}
import compiler.lang
import compiler.lang.*
import compiler.lang.Types.PrimitiveType.{AnyType, NothingType}
import compiler.lang.Types.{NamedType, Type}
import compiler.pipeline.CompilationStep.CodeGen
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.typing.SubtypingInfo
import compiler.typing.contexts.{DealiasingContext, ResolutionContext}
import compiler.util.toJavaUtilList

import java.lang
import java.lang.classfile.*
import java.lang.classfile.TypeKind.*
import java.lang.constant.ConstantDescs.*
import java.lang.constant.{ClassDesc, MethodTypeDesc}
import java.nio.file.{Files, Path}
import scala.collection.mutable

// TODO make sure that main functions have input type Array[String] (or possibly take no argument)
final class Backend(outputDirectoryPath: Path, er: ErrorReporter) extends CompilerStep[(Program, SubtypingInfo), List[String]] {

  // TODO see if lower JVM versions can be supported
  private val javaVersionCode = (ClassFile.JAVA_25_VERSION, 0)

  private val objectInstanceFieldName = "INSTANCE"
  private val mainFuncName = "main"

  private val unreachablePathMessage = "Licorne: UNREACHABLE PATH ERROR\n" +
    "This path has been marked unreachable by the Licorne compiler. This code should never been executed.\n" +
    "If this message appears as an AssertionError thrown during program execution, this means that the compiler made a mistake and the code is corrupted (unless you used reflection)."

  private val equalsMethodName = "equals"
  private val assertionErrorInternalName = "java/lang/AssertionError"

  override def apply(input: (Program, SubtypingInfo)): List[String] = {
    val (program, subtypingInfo) = input

    given Program = program

    given DealiasingContext = DealiasingContext(program.typeAliases)

    given SimplifiedSubtypingContext = SimplifiedSubtypingContext(subtypingInfo.subtypingGraph)

    given ResolutionContext = ResolutionContext(program, er)(using CodeGen)

    val mainClasses = mutable.LinkedHashSet.empty[String]
    for (tSig <- program.runtimeSignatures) {
      if (tSig.functions.exists(_._2.isMain)) {
        mainClasses.add(tSig.id.stringId)
      }
      generateTypeDecl(tSig, program)
    }
    mainClasses.toList
  }

  private def generateTypeDecl(tSig: RuntimeTypeSignature, program: Program)
                              (using DealiasingContext, SimplifiedSubtypingContext, ResolutionContext): Unit = {
    val tid = tSig.id
    val path = mkPathToClass(tid)
    Files.createDirectories(path.getParent)
    ClassFile.of().buildTo(
      path,
      ClassDesc.of(tid.stringId),
      cb => {
        val (majorVersion, minorVersion) = javaVersionCode
        var flags = ClassFile.ACC_PUBLIC
        if (tSig.isInstanceOf[AbstractTypeSig]) {
          flags |= ClassFile.ACC_INTERFACE | ClassFile.ACC_ABSTRACT
        } else {
          flags |= ClassFile.ACC_FINAL
        }
        cb.withFlags(flags)
        cb.withVersion(majorVersion, minorVersion)
        tSig match {
          case tSig: ObjectSignature =>
            generateInstanceFieldAndInitializer(tSig, cb)
          case _ => ()
        }
        tSig match {
          case tSig: ConcreteTypeSig =>
            generateConstructor(tSig, cb, isPrivate = tSig.isInstanceOf[ObjectSignature])
          case _ => ()
        }
        generateFields(tid, tSig.fields.values, cb)
        generateFunctions(tid, tSig.functions.values, cb)(using program)
        generateInterfacesList(tSig.directSupertypes.map(_.typeName), cb)
      }
    )
  }

  private def generateInstanceFieldAndInitializer(objSig: ObjectSignature, cb: ClassBuilder)(using DealiasingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tid = objSig.id
    val tDesc = tConv.descriptorFor(tid)
    cb.withField(objectInstanceFieldName, tDesc, ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC | ClassFile.ACC_FINAL)
    cb.withMethod(CLASS_INIT_NAME, MethodTypeDesc.of(CD_void), ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC, mb => mb.withCode(cb => {
      cb.new_(tDesc)
      cb.dup()
      cb.invokespecial(tDesc, INIT_NAME, MethodTypeDesc.of(CD_void))
      cb.putstatic(tDesc, objectInstanceFieldName, tDesc)
      cb.return_()
    }))
  }

  private def generateInterfacesList(interfaces: Iterable[TypeIdentifier], cb: ClassBuilder)(using DealiasingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    cb.withInterfaceSymbols(interfaces.map(tConv.descriptorFor).toJavaUtilList)
  }

  private def generateFields(ownerId: TypeIdentifier, fields: Iterable[Field], cb: ClassBuilder)(using DealiasingContext): Unit = {
    // we ignore accessors: the SSA generator already added them to the list of functions
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    for (fld <- fields) {
      var flags = ClassFile.ACC_PRIVATE
      if (fld.isStable) {
        flags |= ClassFile.ACC_FINAL
      }
      cb.withField(fld.id.stringId, tConv.descriptorFor(fld.tpe), flags)
    }
  }

  private def generateConstructor(tSig: ConcreteTypeSig, cb: ClassBuilder, isPrivate: Boolean)(using DealiasingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val constrDesc = mkConstrDesc(tSig)
    val flags = if isPrivate then ClassFile.ACC_PRIVATE else ClassFile.ACC_PUBLIC
    cb.withMethod(INIT_NAME, constrDesc, flags, mb => mb.withCode(cb => {
      cb.aload(cb.receiverSlot())
      cb.dup()
      cb.invokespecial(CD_Object, INIT_NAME, MethodTypeDesc.of(CD_void))
      var paramSlotIdx = 1
      for (fld <- tSig.fields.values) {
        cb.aload(paramSlotIdx)
        val fldId = fld.id.stringId
        val fldTypeDesc = tConv.descriptorFor(fld.tpe)
        cb.putfield(tConv.descriptorFor(tSig.id), fldId, fldTypeDesc)
        cb.localVariable(paramSlotIdx, fldId, fldTypeDesc, cb.startLabel(), cb.endLabel())
        paramSlotIdx += tConv.kindFor(fld.tpe).slotSize()
      }
      cb.return_()
    }))
  }

  private def generateFunctions(ownerId: TypeIdentifier, functions: Iterable[FunctionSignature], cb: ClassBuilder)
                               (using program: Program, dealiasingCtx: DealiasingContext,
                                simplifiedSubtypingCtx: SimplifiedSubtypingContext, resolCtx: ResolutionContext): Unit = {
    for (funSig <- functions) {
      val bodyOpt = program.functions.apply(ownerId, funSig.functionName).bodyOpt
      generateFunc(funSig, bodyOpt, cb)
      if (funSig.isMain) {
        generateMainFunc(ownerId, funSig, cb)
      }
    }
  }

  private def generateMainFunc(ownerId: TypeIdentifier, mainFunSig: FunctionSignature, cb: ClassBuilder)(using DealiasingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val ownerTypeDesc = tConv.descriptorFor(ownerId)
    cb.withMethod(mainFuncName, MethodTypeDesc.of(CD_void, CD_String.arrayType()), ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC, mb => mb.withCode(cb => {
      cb.getstatic(ownerTypeDesc, objectInstanceFieldName, ownerTypeDesc)
      if (mainFunSig.paramsWithoutThis.nonEmpty) {
        // this has to be an array of Strings
        cb.aload(1)
      }
      cb.invokevirtual(ownerTypeDesc, mainFunSig.functionName.stringId, mkFunDesc(mainFunSig))
      cb.return_()
    }))
  }

  private def generateFunc(funSig: FunctionSignature, bodyOpt: Option[SSA.Scope], cb: ClassBuilder)
                          (using DealiasingContext, SimplifiedSubtypingContext, ResolutionContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val funDesc = mkFunDesc(funSig)
    cb.withMethod(funSig.functionName.stringId, funDesc, mkFunFlags(funSig), mb => {
      bodyOpt.foreach { body =>
        mb.withCode(cb => {
          given funGenCtx: FunctionGenerationContext = FunctionGenerationContext(funSig)

          for ((idVal, tpe) <- funSig.paramsInclThis) {
            allocateAndDeclare(idVal, cb, body)
          }
          generateScope(body, cb)
          if (!body.hasExited) {
            cb.return_()
          }
        })
      }
    })
  }

  private def mkFunDesc(funSig: FunctionSignature)(using DealiasingContext): MethodTypeDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    MethodTypeDesc.of(tConv.descriptorFor(funSig.retType),
      funSig.paramsWithoutThis.map((_, tpe) => tConv.descriptorFor(tpe)).toJavaUtilList)
  }

  private def mkConstrDesc(tSig: ConcreteTypeSig)(using DealiasingContext): MethodTypeDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    MethodTypeDesc.of(CD_void, tSig.fields.values.map(f => tConv.descriptorFor(f.tpe)).toArray *)
  }

  private def mkFunFlags(funSig: FunctionSignature): Int = {
    var flags = funSig.visibility match {
      case Visibility.Private => ClassFile.ACC_PRIVATE
      case Visibility.Public => ClassFile.ACC_PUBLIC
    }
    funSig.overridability match {
      case Overridability.Abstract =>
        flags |= ClassFile.ACC_ABSTRACT
      case Overridability.Final =>
        flags |= ClassFile.ACC_FINAL
      case Overridability.Open => ()
    }
    flags
  }

  private def mkPathToClass(typeId: TypeIdentifier): Path = {
    typeId.prefixes
      .foldLeft(outputDirectoryPath)(_.resolve(_))
      .resolve(typeId.nonPrefixedId + FileExtensions.dot(_.clazz))
  }

  private def generateScope(scope: SSA.Scope, cb: CodeBuilder)
                           (using funGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext,
                            simplifiedSubtypingCtx: SimplifiedSubtypingContext, resolCtx: ResolutionContext): Unit = {
    scope.writeInstrIndices()
    try {
      for (instr <- scope.instructions) {
        funGenCtx.onNewLineNumber(instr.getPosition) { l =>
          cb.lineNumber(l)
        }
        generateInstr(instr, cb, scope)
      }
    } catch {
      case TerminateScopeSignal => ()
    }
  }

  private def generateInstr(instr: SSA.Instr, cb: CodeBuilder, currScope: SSA.Scope)
                           (using funGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext,
                            simplifiedSubtypingCtx: SimplifiedSubtypingContext, resolCtx: ResolutionContext): Unit = instr match {

    case scope: SSA.Scope => generateScope(scope, cb)

    case SSA.Loop(cond, condEvalResultVal, body, variables) =>
      // FIXME tests for on jump value move mechanism
      for (loopVarData@LoopVarData(varId, beforeLoopVal, inCondVal, bodyLastVal, varDefScope) <- variables) {
        val beforeLoopValTypeKind = typeKindOf(beforeLoopVal, currScope)
        val inCondValTypeKind = typeKindOf(inCondVal, currScope)
        val bodyLastValTypeKind = typeKindOf(bodyLastVal, body)
        if (inCondValTypeKind == beforeLoopValTypeKind) {
          funGenCtx.coalesce(beforeLoopVal, inCondVal)
        } else {
          allocateAndDeclare(inCondVal, cb, currScope)
        }
        if (bodyLastValTypeKind == inCondValTypeKind) {
          funGenCtx.coalesce(inCondVal, bodyLastVal)
        } else {
          allocateAndDeclare(bodyLastVal, cb, currScope)
        }
      }
      for (LoopVarData(varId, beforeLoopVal, inCondVal, bodyLastVal, varDefScope) <- variables) {
        genValueMove(inCondVal, beforeLoopVal, currScope, cb)
      }
      val beforeCondLabel = cb.newBoundLabel()
      val afterLoopLabel = cb.newLabel()
      generateScope(cond, cb)
      genValueLoad(condEvalResultVal, currScope, cb)
      cb.ifeq(afterLoopLabel)
      generateScope(body, cb)
      for (LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal, varDefScope) <- variables) {
        genValueMove(condVal, bodyLastVal, body, cb)
      }
      cb.goto_(beforeCondLabel)
      cb.labelBinding(afterLoopLabel)

    case SSA.Disjunction(condEvalResultVal, thenBr, elseBr, variables) =>
      for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
        val afterThenValTypeKind = typeKindOf(afterThenVal, currScope)
        val afterElseValTypeKind = typeKindOf(afterElseVal, currScope)
        val joinedValTypeKind = typeKindOf(joinedVal, currScope)
        if (!funGenCtx.hasSlotFor(joinedVal) && joinedValTypeKind == afterThenValTypeKind && funGenCtx.hasSlotFor(afterThenVal)) {
          funGenCtx.coalesce(afterThenVal, joinedVal)
        } else if (!funGenCtx.hasSlotFor(joinedVal) && joinedValTypeKind == afterElseValTypeKind && funGenCtx.hasSlotFor(afterElseVal)) {
          funGenCtx.coalesce(afterElseVal, joinedVal)
        }
        allocateAndDeclareIfNew(joinedVal, currScope, cb)
        if (!funGenCtx.hasSlotFor(afterThenVal) && afterThenValTypeKind == joinedValTypeKind) {
          funGenCtx.coalesce(joinedVal, afterThenVal)
        } else if (!funGenCtx.hasSlotFor(afterElseVal) && afterElseValTypeKind == joinedValTypeKind) {
          funGenCtx.coalesce(joinedVal, afterElseVal)
        }
        allocateAndDeclareIfNew(afterThenVal, currScope, cb)
        allocateAndDeclareIfNew(afterElseVal, currScope, cb)
      }
      val elseBrLabel = cb.newLabel()
      val afterDisjLabel = cb.newLabel()
      genValueLoad(condEvalResultVal, currScope, cb)
      cb.ifeq(elseBrLabel)
      generateScope(thenBr, cb)
      for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
        genValueMove(joinedVal, afterThenVal, currScope, cb)
      }
      cb.goto_(afterDisjLabel)
      cb.labelBinding(elseBrLabel)
      generateScope(elseBr, cb)
      for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
        genValueMove(joinedVal, afterElseVal, currScope, cb)
      }
      cb.labelBinding(afterDisjLabel)
      cb.nop()

    case SSA.StaticTypeAssert(value, tpe) => ()

    // FIXME collapse assignments when rhs is an IdValue or a constant

    case SSA.AssignVal(assigned, src) =>
      if (assigned.isInstanceOf[IntermediateIdValue] && typeKindOf(assigned, currScope) == typeKindOf(src, currScope) && !funGenCtx.hasSlotFor(assigned)) {
        funGenCtx.saveSubst(assigned, src)
      } else {
        genValueMove(assigned, src, currScope, cb)
      }

    case SSA.AssignIntConst(assigned, src) =>
      if (assigned.isInstanceOf[IntermediateIdValue] && typeKindOf(assigned, currScope) == INT) {
        funGenCtx.saveIntSubst(assigned, src)
      } else {
        cb.loadConstant(src)
        genValueStore(assigned, currScope, cb)
      }

    case SSA.AssignBoolConst(assigned, src) =>
      val srcAsInt = if src then 1 else 0
      if (assigned.isInstanceOf[IntermediateIdValue] && typeKindOf(assigned, currScope) == INT) {
        funGenCtx.saveIntSubst(assigned, srcAsInt)
      } else {
        cb.loadConstant(srcAsInt)
        genValueStore(assigned, currScope, cb)
      }

    case SSA.AssignStringConst(assigned, src) =>
      val cstEntry = cb.constantPool().stringEntry(src)
      cb.ldc(cstEntry)
      genValueStore(assigned, currScope, cb)

    case SSA.NumNeg(assigned, operand) =>
      genValueLoad(operand, currScope, cb)
      dispatchArithOnVal(operand, currScope, whenInt = {
        cb.ineg()
      }, whenDouble = {
        cb.dneg()
      })
      genValueStore(assigned, currScope, cb)

    case SSA.Add(assigned, lhs, rhs) => genArithBinop(assigned, lhs, rhs, currScope, cb, _.iadd(), _.dadd())
    case SSA.Sub(assigned, lhs, rhs) => genArithBinop(assigned, lhs, rhs, currScope, cb, _.isub(), _.dsub())
    case SSA.Mul(assigned, lhs, rhs) => genArithBinop(assigned, lhs, rhs, currScope, cb, _.imul(), _.dmul())
    case SSA.Div(assigned, lhs, rhs) => genArithBinop(assigned, lhs, rhs, currScope, cb, _.idiv(), _.ddiv())
    case SSA.Rem(assigned, lhs, rhs) => genArithBinop(assigned, lhs, rhs, currScope, cb, _.irem(), _.drem())

    case SSA.LogicNeg(assigned, operand) =>
      cb.iconst_m1()
      genValueLoad(operand, currScope, cb)
      cb.ixor()
      genValueStore(assigned, currScope, cb)

    case And(assigned, lhs, rhs) => genArithBinop(assigned, lhs, rhs, currScope, cb, _.iand(), _ => assert(false))
    case Or(assigned, lhs, rhs) => genArithBinop(assigned, lhs, rhs, currScope, cb, _.ior(), _ => assert(false))

    case SSA.Equal(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == INT && typeKindOf(rhs, currScope) == INT =>
      genIntCompBinop(assigned, lhs, rhs, currScope, cb, _.ifeq(_))
    case SSA.Leq(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == INT =>
      genIntCompBinop(assigned, lhs, rhs, currScope, cb, _.if_icmple(_))
    case SSA.Lt(assigned, lhs, rhs) if typeKindOf(rhs, currScope) == INT =>
      genIntCompBinop(assigned, lhs, rhs, currScope, cb, _.if_icmplt(_))

    case SSA.Equal(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == DOUBLE && typeKindOf(rhs, currScope) == DOUBLE => ???
    case SSA.Leq(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == DOUBLE && typeKindOf(rhs, currScope) == DOUBLE => ???
    case SSA.Lt(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == DOUBLE && typeKindOf(rhs, currScope) == DOUBLE => ???

    // FIXME enforce a.equals(a) when redefining equals
    case SSA.Equal(assigned, lhs, rhs) =>
      genValueLoad(lhs, currScope, cb)
      ensureAssignable(AnyType, dealiasedTypeOf(lhs, currScope), cb)
      genValueLoad(rhs, currScope, cb)
      ensureAssignable(AnyType, dealiasedTypeOf(rhs, currScope), cb)
      cb.invokevirtual(CD_Object, equalsMethodName, MethodTypeDesc.of(CD_boolean, CD_Object))
      genValueStore(assigned, currScope, cb)

    case SSA.Leq(assigned, lhs, rhs) =>
      throw AssertionError(s"unexpected Leq between ${dealiasedTypeOf(lhs, currScope)} and ${dealiasedTypeOf(rhs, currScope)}")
    case SSA.Lt(assigned, lhs, rhs) =>
      throw AssertionError(s"unexpected Lt between ${dealiasedTypeOf(lhs, currScope)} and ${dealiasedTypeOf(rhs, currScope)}")

    case fr@SSA.FieldRead(assigned, owner, field) =>
      val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
      val ownerDesc = tConv.descriptorFor(field.getReceiverSigUnsafe.id)
      genValueLoad(owner, currScope, cb)
      cb.getfield(ownerDesc, field.fieldId.stringId, tConv.descriptorFor(field.getInstantiatedTypeUnsafe))
      if (!(funGenCtx.enclosingFunc.isSyntheticAccessor && fr.getIdxInScopeOpt.get == 0)) {
        ensureAssignable(dealiasedTypeOf(assigned, currScope), field.getFieldUnsafe.tpe, cb)
        genValueStore(assigned, currScope, cb)
      }

    case SSA.FieldWrite(owner, field, rhs) =>
      val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
      val ownerDesc = tConv.descriptorFor(field.getReceiverSigUnsafe.id)
      genValueLoad(owner, currScope, cb)
      genValueLoad(rhs, currScope, cb)
      ensureAssignable(field.getFieldUnsafe.tpe, dealiasedTypeOf(rhs, currScope), cb)
      cb.putfield(ownerDesc, field.fieldId.stringId, tConv.descriptorFor(field.getInstantiatedTypeUnsafe))

    // FIXME this is temporary, for testing purposes
    case SSA.InvokeFunc(assigned, receiver, func, typeArgs, args) if func.getFunSigOpt.get.functionName.stringId == "println" =>
      assert(args.size == 1)
      val systemDesc = ClassDesc.of("java.lang.System")
      val printStreamDesc = ClassDesc.of("java.io.PrintStream")
      cb.getstatic(systemDesc, "out", printStreamDesc)
      genValueLoad(args.head, currScope, cb)
      ensureAssignable(AnyType, dealiasedTypeOf(args.head, currScope), cb)
      cb.invokevirtual(printStreamDesc, "println", MethodTypeDesc.of(CD_void, CD_Object))

    case SSA.InvokeFunc(assigned, receiver, func, typeArgs, args) =>
      val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
      val funSig = func.getFunSigUnsafe
      val receiverDesc = tConv.descriptorFor(func.getFunSigUnsafe.receiverType)
      genValueLoad(receiver, currScope, cb)
      val paramTypes = funSig.paramsWithoutThis.map(_._2)
      for ((arg, paramType) <- args.zip(paramTypes)) {
        genValueLoad(arg, currScope, cb)
        ensureAssignable(paramType, dealiasedTypeOf(arg, currScope), cb)
      }
      cb.invokevirtual(receiverDesc, func.funId.stringId, mkFunDesc(funSig))
      ensureAssignable(dealiasedTypeOf(assigned, currScope), funSig.retType, cb)
      genValueStore(assigned, currScope, cb)

    case SSA.InvokeClosure(assigned, callee, closureTypingTarget, args) => ???

    case SSA.Instantiate(assigned, classOrRecordName, typeArgs, fieldsInit) =>
      val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
      val fieldsInitMap = fieldsInit.toMap
      val createdObjTypeSig = resolCtx.resolveTypeSigAs[UserInstantiableTypeSig](classOrRecordName).get
      cb.new_(tConv.descriptorFor(classOrRecordName))
      cb.dup()
      for (fld <- createdObjTypeSig.fields.values) {
        val argVal = fieldsInitMap.apply(fld.id)
        genValueLoad(argVal, currScope, cb)
        ensureAssignable(fld.tpe, dealiasedTypeOf(argVal, currScope), cb)
      }
      cb.invokespecial(tConv.descriptorFor(classOrRecordName), INIT_NAME, mkConstrDesc(createdObjTypeSig))
      genValueStore(assigned, currScope, cb)

    case SSA.MkClosure(assigned, params, body, isPure) => ???

    case SSA.MkHeapVar(assigned) => ???
    case SSA.HeapVarRead(assigned, heapVar) => ???
    case SSA.HeapVarWrite(heapVar, newValue) => ???

    case SSA.TypeTest(assigned, testedValue, testedTypeId) =>
      val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
      genValueLoad(testedValue, currScope, cb)
      cb.instanceOf(tConv.descriptorFor(testedTypeId))
      genValueStore(assigned, currScope, cb)

    case SSA.Cast(inValue, target) =>
      val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
      genValueLoad(inValue, currScope, cb)
      cb.checkcast(tConv.descriptorFor(target))
      genValueStore(inValue, currScope, cb)

    case conv@SSA.Conversion(assigned, inValue, targetType) =>
      import compiler.lang.TypeConversion.*
      val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
      conv.forceGetTypeConversion match {
        case None => generateInstr(AssignVal(assigned, inValue), cb, currScope)
        case Some(conversion) =>
          genValueLoad(inValue, currScope, cb)
          conversion match {
            case Int2Double => cb.i2d()
            case Double2Int => cb.d2i()
            case IntToChar => cb.i2c()
            case CharToInt => ()
            case IntToString | BoolToString | CharToString | DoubleToString =>
              val fromDesc = tConv.descriptorFor(conversion.from)
              cb.invokestatic(boxDesc(fromDesc), "toString", MethodTypeDesc.of(CD_String, fromDesc))
          }
          genValueStore(assigned, currScope, cb)
      }

    case hCast@SSA.HybridCast(inValue) =>
      val assertionErrorDesc = ClassDesc.ofInternalName(assertionErrorInternalName)
      val skipThrowLabel = cb.newLabel()
      hCast.getTargetRefinement match {
        case Some(formula) =>
          val (ssa, resVal) = FormulasCompilation.convertFormulaToSSA(formula, currScope)
          for (instr <- ssa) {
            generateInstr(instr, cb, currScope)
          }
          cb.ifne(skipThrowLabel)
          cb.new_(assertionErrorDesc)
          cb.dup()
          cb.ldc(s"assertion $formula failed")
          cb.invokespecial(assertionErrorDesc, INIT_NAME, MethodTypeDesc.of(CD_void, CD_String))
          cb.athrow()
        case None =>
          genValueLoad(inValue, currScope, cb)
          cb.ifnonnull(skipThrowLabel)
          cb.new_(assertionErrorDesc)
          cb.dup()
          cb.ldc(s"non nullity assertion failed")
          cb.invokespecial(assertionErrorDesc, INIT_NAME, MethodTypeDesc.of(CD_void, CD_String))
          cb.athrow()
      }
      cb.labelBinding(skipThrowLabel)

    case ret@SSA.Return(retVal) =>
      val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
      val retType = funGenCtx.enclosingFunc.retType
      if (!(funGenCtx.enclosingFunc.isSyntheticAccessor && ret.getIdxInScopeOpt.get == 1)) {
        genValueLoad(retVal, currScope, cb)
        ensureAssignable(retType, dealiasedTypeOf(retVal, currScope), cb)
      }
      cb.return_(tConv.kindFor(retType))
      throw TerminateScopeSignal

    case SSA.Panic(msg) =>
      val assertionErrorDesc = ClassDesc.ofInternalName(assertionErrorInternalName)
      cb.new_(assertionErrorDesc)
      cb.dup()
      genValueLoad(msg, currScope, cb)
      cb.invokespecial(assertionErrorDesc, INIT_NAME, MethodTypeDesc.of(CD_void, CD_String))
      cb.athrow()
      throw TerminateScopeSignal

    case SSA.Drop(droppedValue) => ()
    case SSA.LocalDecl(localId, tpe) => ()

    case SSA.Unreachable() =>
      val assertionErrorDesc = ClassDesc.ofInternalName(assertionErrorInternalName)
      cb.new_(assertionErrorDesc)
      cb.dup()
      cb.ldc(unreachablePathMessage)
      cb.invokespecial(assertionErrorDesc, INIT_NAME, MethodTypeDesc.of(CD_void, CD_String))
      cb.athrow()
      throw TerminateScopeSignal
  }

  private def genValueMove(to: IdValue, from: IdValue, currScope: Scope, cb: CodeBuilder)
                          (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext, simplifiedSubtypingCtx: SimplifiedSubtypingContext): Unit = {
    val typeDescOfTo = typeDescOf(to, currScope)
    val typeDescOfFrom = typeDescOf(from, currScope)
    if (funcGenCtx.getSlot(from) != allocateAndDeclareIfNew(to, currScope, cb) || typeDescOfFrom != typeDescOfTo) {
      genValueLoad(from, currScope, cb)
      ensureAssignable(dealiasedTypeOf(to, currScope), dealiasedTypeOf(from, currScope), cb)
      genValueStore(to, currScope, cb)
    }
  }

  private def genValueLoad(rawIdVal: IdValue, currScope: Scope, cb: CodeBuilder)
                          (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext): Unit = {
    funcGenCtx.asIntConst(rawIdVal) match {
      case Some(cst) =>
        cb.loadConstant(cst)
      case None =>
        val substIdVal = funcGenCtx.getSubst(rawIdVal)
        val kind = typeKindOf(substIdVal, currScope)
        if (kind != VOID) {
          val slot = funcGenCtx.getSlot(substIdVal)
          cb.loadLocal(kind, slot)
        }
    }
  }

  private def genValueStore(idVal: IdValue, currScope: Scope, cb: CodeBuilder)
                           (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext): Unit = {
    val slot = allocateAndDeclareIfNew(idVal, currScope, cb)
    val kind = typeKindOf(idVal, currScope)
    if (kind != VOID) {
      cb.storeLocal(kind, slot)
    }
  }

  /**
   * Adds instructions for boxing, unboxing, or cast, if needed
   */
  private def ensureAssignable(dstType: Type, srcType: Type, cb: CodeBuilder)
                              (using dealiasingCtx: DealiasingContext, simplifiedSubtypingCtx: SimplifiedSubtypingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val dstDesc = tConv.descriptorFor(dstType)
    val dstKind = tConv.kindFor(dstType)
    val srcDesc = tConv.descriptorFor(srcType)
    val srcKind = tConv.kindFor(srcType)
    if (srcDesc.isPrimitive && !dstDesc.isPrimitive) {
      val srcBoxedDesc = boxDesc(srcDesc)
      cb.invokestatic(srcBoxedDesc, "valueOf", MethodTypeDesc.of(srcBoxedDesc, srcDesc))
    } else if (!srcDesc.isPrimitive && dstDesc.isPrimitive) {
      val dstBoxedDesc = boxDesc(dstDesc)
      cb.invokevirtual(dstBoxedDesc, unboxingFunc(srcDesc), MethodTypeDesc.of(dstDesc, dstBoxedDesc))
    } else (dealiasingCtx.dealiasType(dstType), dealiasingCtx.dealiasType(srcType)) match {
      case (NamedType(dstTypeId, _, _), NamedType(srcTypeId, _, _)) if !simplifiedSubtypingCtx.isSubtype(srcTypeId, dstTypeId) =>
        cb.checkcast(dstDesc)
      case _ => ()
    }
    if (srcKind != VOID && dstKind == VOID) {
      if (srcKind.slotSize() == 2) {
        cb.pop2()
      } else {
        cb.pop()
      }
    }
  }

  private def unboxingFunc(boxedDesc: ClassDesc): String = boxedDesc match {
    case CD_Integer => "intValue"
    case CD_Boolean => "booleanValue"
    case CD_Double => "doubleValue"
    case CD_Character => "charValue"
    case boxedDesc => throw AssertionError(s"unexpected boxed type descriptor: $boxedDesc")
  }

  private def allocateAndDeclare(idVal: NamedIdValue, cb: CodeBuilder, currScope: Scope)
                                (using fungenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext): Int = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tpe = currScope.typeOfNoSmartcast(idVal).get
    val kind = tConv.kindFor(tpe)
    val descr = tConv.descriptorFor(tpe)
    val slot = fungenCtx.allocateSlot(kind, idVal)
    cb.localVariable(slot, idVal.name, descr, cb.startLabel(), cb.endLabel())
    slot
  }

  private def allocateAndDeclareIfNew(idVal: IdValue, currScope: Scope, cb: CodeBuilder)
                                     (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext): Int = {
    idVal match {
      case idVal: NamedIdValue if !funcGenCtx.hasSlotFor(idVal) =>
        allocateAndDeclare(idVal, cb, currScope)
      case _ =>
        funcGenCtx.getOrAllocSlot(typeKindOf(idVal, currScope), idVal)
    }
  }

  private def dealiasedTypeOf(idVal: IdValue, currScope: Scope)(using dealiasingCtx: DealiasingContext): Type =
    dealiasingCtx.dealiasType(currScope.typeOfNoSmartcast(idVal).getOrElse(NothingType))

  private def typeDescOf(idVal: IdValue, currScope: Scope)(using DealiasingContext): ClassDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tpe = currScope.typeOfNoSmartcast(idVal).get
    tConv.descriptorFor(tpe)
  }

  private def typeKindOf(idVal: IdValue, currScope: Scope)(using DealiasingContext): TypeKind = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    currScope.typeOfNoSmartcast(idVal) match {
      case Some(tpe) => tConv.kindFor(tpe)
      case None => VOID
    }
  }

  private def genArithBinop(assigned: IdValue, lhs: IdValue, rhs: IdValue, currScope: Scope, cb: CodeBuilder,
                            intOp: CodeBuilder => Unit, doubleOp: CodeBuilder => Unit)
                           (using FunctionGenerationContext, DealiasingContext): Unit = {
    genValueLoad(lhs, currScope, cb)
    genValueLoad(rhs, currScope, cb)
    dispatchArithOnVal(lhs, currScope, whenInt = {
      intOp(cb)
    }, whenDouble = {
      doubleOp(cb)
    })
    genValueStore(assigned, currScope, cb)
  }

  private def genIntCompBinop(assigned: IdValue, lhs: IdValue, rhs: IdValue, currScope: Scope, cb: CodeBuilder, mkCmpInstr: (ccb: CodeBuilder, trueLabel: Label) => Unit)
                             (using FunctionGenerationContext, DealiasingContext): Unit = {
    genValueLoad(lhs, currScope, cb)
    genValueLoad(rhs, currScope, cb)
    val trueLabel = cb.newLabel()
    val endLabel = cb.newLabel()
    mkCmpInstr(cb, trueLabel)
    cb.iconst_0()
    cb.goto_(endLabel)
    cb.labelBinding(trueLabel)
    cb.iconst_1()
    cb.labelBinding(endLabel)
    genValueStore(assigned, currScope, cb)
  }

  private def dispatchArithOnVal(idVal: IdValue, currScope: Scope, whenInt: => Unit, whenDouble: => Unit)(using DealiasingContext): Unit =
    dispatchArithOnKind(typeKindOf(idVal, currScope), whenInt, whenDouble)

  private def dispatchArithOnKind(kind: TypeKind, whenInt: => Unit, whenDouble: => Unit): Unit = kind match {
    case INT =>
      val _ = whenInt
    case DOUBLE =>
      val _ = whenDouble
    case _ =>
      throw AssertionError(s"unexpected kind in arithmetic dispatcher: $kind")
  }

}
