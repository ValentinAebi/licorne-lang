package compiler.backend

import compiler.gennames.FileExtensions
import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.ssa.Formulas.{IdValue, IntermediateIdValue, NamedIdValue}
import compiler.irs.ssa.SSA.*
import compiler.irs.ssa.{Formulas, SSA}
import compiler.lang.*
import compiler.lang.Types.PrimitiveType.AnyType
import compiler.lang.Types.{NamedType, Type}
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.typing.SubtypingInfo
import compiler.typing.contexts.DealiasingContext
import compiler.util.toJavaUtilList

import java.lang
import java.lang.classfile.*
import java.lang.constant.ConstantDescs.*
import java.lang.constant.{ClassDesc, MethodTypeDesc}
import java.nio.file.{Files, Path}
import scala.collection.mutable

// TODO make sure that main functions have input type Array[String] (or possibly take no argument)
final class Backend(outputDirectoryPath: Path) extends CompilerStep[(Program, SubtypingInfo), List[String]] {

  // TODO see if lower JVM versions can be supported
  private val javaVersionCode = (ClassFile.JAVA_25_VERSION, 0)

  private val objectInstanceFieldName = "INSTANCE"
  private val mainFuncName = "main"

  override def apply(input: (Program, SubtypingInfo)): List[String] = {
    val (program, subtypingInfo) = input

    given Program = program

    given DealiasingContext = DealiasingContext(program.typeAliases)

    given SimplifiedSubtypingContext = SimplifiedSubtypingContext(subtypingInfo.subtypingGraph)

    val generatedClasses = mutable.LinkedHashSet.empty[String]
    for (tSig <- program.runtimeSignatures) {
      if (tSig.functions.exists(_._2.isMain)) {
        generatedClasses.add(tSig.id.stringId)
      }
      generateTypeDecl(tSig, program)
    }
    generatedClasses.toList
  }

  private def generateTypeDecl(tSig: RuntimeTypeSignature, program: Program)
                              (using DealiasingContext, SimplifiedSubtypingContext): Unit = {
    val tid = tSig.id
    val path = generatePathToClass(tid)
    Files.createDirectories(path.getParent)
    ClassFile.of().buildTo(
      path,
      ClassDesc.of(tid.stringId),
      cb => {
        val (majorVersion, minorVersion) = javaVersionCode
        cb.withVersion(majorVersion, minorVersion)
        tSig match {
          case tSig: ObjectSignature =>
            generateInstanceFieldAndInitializer(tSig, cb)
          case _ => ()
        }
        if (tSig.isInstanceOf[ConcreteTypeSig]) {
          generateConstructor(tid, tSig.fields.values, cb, isPrivate = tSig.isInstanceOf[ObjectSignature])
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

  private def generateConstructor(ownerId: TypeIdentifier, fields: Iterable[Field], cb: ClassBuilder, isPrivate: Boolean)(using DealiasingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val constrDesc = MethodTypeDesc.of(CD_void, fields.map(f => tConv.descriptorFor(f.tpe)).toArray *)
    val flags = if isPrivate then ClassFile.ACC_PRIVATE else ClassFile.ACC_PUBLIC
    cb.withMethod(INIT_NAME, constrDesc, flags, mb => mb.withCode(cb => {
      cb.aload(cb.receiverSlot())
      cb.invokespecial(CD_Object, INIT_NAME, MethodTypeDesc.of(CD_void))
      var paramSlotIdx = 1
      for (fld <- fields) {
        cb.aload(paramSlotIdx)
        cb.putfield(tConv.descriptorFor(ownerId), fld.id.stringId, tConv.descriptorFor(fld.tpe))
        paramSlotIdx += tConv.kindFor(fld.tpe).slotSize()
      }
      cb.return_()
    }))
  }

  private def generateFunctions(ownerId: TypeIdentifier, functions: Iterable[FunctionSignature], cb: ClassBuilder)
                               (using program: Program, dealiasingCtx: DealiasingContext, simplifiedSubtypingCtx: SimplifiedSubtypingContext): Unit = {
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
      cb.invokevirtual(ownerTypeDesc, mainFunSig.functionName.stringId, generateFunDescr(mainFunSig))
      cb.return_()
    }))
  }

  private def generateFunc(funSig: FunctionSignature, bodyOpt: Option[SSA.Scope], cb: ClassBuilder)
                          (using DealiasingContext, SimplifiedSubtypingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val funDesc = generateFunDescr(funSig)
    cb.withMethod(funSig.functionName.stringId, funDesc, generateFunFlags(funSig), mb => {
      bodyOpt.foreach { body =>
        mb.withCode(cb => {
          given funGenCtx: FunctionGenerationContext = FunctionGenerationContext(funSig.retType)

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

  private def generateFunDescr(funSig: FunctionSignature)(using DealiasingContext): MethodTypeDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    MethodTypeDesc.of(tConv.descriptorFor(funSig.retType),
      funSig.paramsWithoutThis.map((_, tpe) => tConv.descriptorFor(tpe)).toJavaUtilList)
  }

  private def generateFunFlags(funSig: FunctionSignature): Int = {
    funSig.visibility match {
      case Visibility.Private => ClassFile.ACC_PRIVATE
      case Visibility.Public => ClassFile.ACC_PUBLIC
    }
  }

  private def generatePathToClass(typeId: TypeIdentifier): Path = {
    typeId.prefixes
      .foldLeft(outputDirectoryPath)(_.resolve(_))
      .resolve(typeId.nonPrefixedId + FileExtensions.dot(_.clazz))
  }

  private def generateScope(scope: SSA.Scope, cb: CodeBuilder)
                           (using funGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext, simplifiedSubtypingCtx: SimplifiedSubtypingContext): Unit = {
    // instruction indices are currently unused, but could help with some optimizations
    scope.writeInstrIndices()
    for (instr <- scope.instructions) {
      funGenCtx.onNewLineNumber(instr.getPosition) { l =>
        cb.lineNumber(l)
      }
      generateInstr(instr, cb, scope)
    }
  }

  private def generateInstr(instr: SSA.Instr, cb: CodeBuilder, currScope: SSA.Scope)
                           (using funGenCtx: FunctionGenerationContext, dealiasingCtxt: DealiasingContext, simplifiedSubtypingCtx: SimplifiedSubtypingContext): Unit = instr match {

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

    case SSA.StaticTypeAssert(value, tpe) => ()

    // FIXME collapse assignments when rhs is an IdValue or a constant

    case SSA.AssignVal(assigned, src) =>
      if (assigned.isInstanceOf[IntermediateIdValue] && typeKindOf(assigned, currScope) == typeKindOf(src, currScope) && !funGenCtx.hasSlotFor(assigned)) {
        funGenCtx.saveSubst(assigned, src)
      } else {
        genValueMove(assigned, src, currScope, cb)
      }

    case SSA.AssignIntConst(assigned, src) =>
      if (assigned.isInstanceOf[IntermediateIdValue] && typeKindOf(assigned, currScope) == TypeKind.INT) {
        funGenCtx.saveIntSubst(assigned, src)
      } else {
        cb.loadConstant(src)
        genValueStore(assigned, currScope, cb)
      }

    case SSA.AssignBoolConst(assigned, src) =>
      val srcAsInt = if src then 1 else 0
      if (assigned.isInstanceOf[IntermediateIdValue] && typeKindOf(assigned, currScope) == TypeKind.INT) {
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

    case SSA.LogicNeg(assigned, operand) => ???

    case SSA.Equal(assigned, lhs, rhs) => ???

    case SSA.Leq(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == TypeKind.INT =>
      genIntCompBinop(assigned, lhs, rhs, currScope, cb, _.if_icmple(_))
    case SSA.Lt(assigned, lhs, rhs) if typeKindOf(rhs, currScope) == TypeKind.INT =>
      genIntCompBinop(assigned, lhs, rhs, currScope, cb, _.if_icmplt(_))

    case SSA.Leq(assigned, lhs, rhs) => ???
    case SSA.Lt(assigned, lhs, rhs) => ???

    case SSA.FieldRead(assigned, owner, field) => ???
    case SSA.HeapVarRead(assigned, heapVar) => ???
    case SSA.FieldWrite(owner, field, rhs) => ???
    case SSA.HeapVarWrite(heapVar, newValue) => ???

    // FIXME this is temporary, for testing purposes
    case SSA.InvokeFunc(assigned, receiver, func, typeArgs, args) if func.getFunSigOpt.get.functionName.stringId == "println" =>
      assert(args.size == 1)
      val systemDesc = ClassDesc.of("java.lang.System")
      val printStreamDesc = ClassDesc.of("java.io.PrintStream")
      cb.getstatic(systemDesc, "out", printStreamDesc)
      genValueLoad(args.head, currScope, cb)
      ensureAssignable(AnyType, dealiasedTypeOf(args.head, currScope), cb)
      cb.invokevirtual(printStreamDesc, "println", MethodTypeDesc.of(CD_void, CD_Object))

    case SSA.InvokeFunc(assigned, receiver, func, typeArgs, args) => ???

    case SSA.InvokeClosure(assigned, callee, closureTypingTarget, args) => ???

    case SSA.Instantiate(assigned, classOrRecordName, typeArgs, fieldsInit) => ???

    case SSA.MkClosure(assigned, params, body, isPure) => ???
    case SSA.MkHeapVar(assigned) => ???

    case SSA.TypeTest(assigned, testedValue, testedTypeId) => ???
    case SSA.Conversion(assigned, inValue, targetType) => ???
    case SSA.Cast(inValue, target) => ???
    case SSA.HybridCast(inValue) => ???

    case SSA.Return(retVal) =>
      genValueLoad(retVal, currScope, cb)
      ensureAssignable(funGenCtx.funRetType, dealiasedTypeOf(retVal, currScope), cb)
      cb.return_(typeKindOf(retVal, currScope))

    case SSA.Panic(msg) => ???

    case SSA.Drop(droppedValue) => ()
    case SSA.LocalDecl(localId, tpe) => ()

    case SSA.Unreachable() => ???
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
        if (kind != TypeKind.VOID) {
          val slot = funcGenCtx.getSlot(substIdVal)
          cb.loadLocal(kind, slot)
        }
    }
  }

  private def genValueStore(idVal: IdValue, currScope: Scope, cb: CodeBuilder)
                           (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext): Unit = {
    val slot = allocateAndDeclareIfNew(idVal, currScope, cb)
    cb.storeLocal(typeKindOf(idVal, currScope), slot)
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
    if (srcKind != TypeKind.VOID && dstKind == TypeKind.VOID) {
      if (srcKind.slotSize() == 2){
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

  private def boxDesc(cd: ClassDesc): ClassDesc = cd match {
    case CD_boolean => CD_Boolean
    case CD_int => CD_Integer
    case CD_char => CD_Character
    case CD_double => CD_Double
    case _ => assert(false)
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
    dealiasingCtx.dealiasType(currScope.typeOfNoSmartcast(idVal).get)

  private def typeDescOf(idVal: IdValue, currScope: Scope)(using DealiasingContext): ClassDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tpe = currScope.typeOfNoSmartcast(idVal).get
    tConv.descriptorFor(tpe)
  }

  private def typeKindOf(idVal: IdValue, currScope: Scope)(using DealiasingContext): TypeKind = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tpe = currScope.typeOfNoSmartcast(idVal).get
    tConv.kindFor(tpe)
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
    case TypeKind.INT =>
      val _ = whenInt
    case TypeKind.DOUBLE =>
      val _ = whenDouble
    case _ =>
      throw AssertionError(s"unexpected kind in arithmetic dispatcher: $kind")
  }

}
