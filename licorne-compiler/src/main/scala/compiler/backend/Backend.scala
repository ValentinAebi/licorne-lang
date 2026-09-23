package compiler.backend

import compiler.backend.Boxing.{boxDesc, unboxDesc}
import compiler.backend.Erasure.getRuntimeType
import compiler.gennames.FileExtensions
import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.ircornegen.ClosuresNamer
import compiler.irs.ircorne.Formulas.*
import compiler.irs.ircorne.IRcorne.*
import compiler.irs.ircorne.{Formulas, IRcorne, SourceLevelFormulaPrinter}
import compiler.lang
import compiler.lang.*
import compiler.lang.Types.PrimitiveType.{AnyType, NothingType, NullType}
import compiler.lang.Types.{NamedType, NullableType, Type}
import compiler.pipeline.CompilationStep.CodeGen
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.stdlib.StdLib
import compiler.stdlib.StdLib.*
import compiler.typing.SubtypingInfo
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, TypeParamsContext}
import compiler.util.toJavaUtilList
import compiler.valuesconversion.GlobalValuesContext

import java.lang.classfile.*
import java.lang.classfile.ClassFile.ClassHierarchyResolverOption
import java.lang.classfile.TypeKind.*
import java.lang.classfile.attribute.SourceFileAttribute
import java.lang.constant.ConstantDescs.*
import java.lang.constant.{ClassDesc, MethodTypeDesc}
import java.nio.file.{Files, Path}
import java.{lang, util}
import scala.collection.immutable.SeqMap
import scala.collection.mutable

// TODO make sure that main functions have input type Array[String] (or possibly take no argument)
final class Backend(
                     outputDirectoryPath: Path,
                     disableOverflowChecks: Boolean,
                     closuresNamer: ClosuresNamer,
                     er: ErrorReporter
                   ) extends CompilerStep[(Program, SubtypingInfo), List[String]] {

  // TODO see if lower JVM versions can be supported
  private val javaVersionCode = (ClassFile.JAVA_25_VERSION, 0)

  private val objectInstanceFieldName = "INSTANCE"
  private val mainFuncName = "main"
  private val licorneCoreStringInternalName = "licorne/core/String"

  private val unreachablePathMessage = "Licorne: UNREACHABLE PATH ERROR\n" +
    "This path has been marked unreachable by the Licorne compiler. This code should never be executed.\n" +
    "If this message appears as an AssertionError thrown during program execution, this means that the compiler made an error and the code is corrupted (or that reflection has been used)."

  private val nullUnboxingMessage = "tried to unbox null"

  private val equalsMethodName = "equals"
  private val assertionErrorInternalName = "java/lang/AssertionError"
  private val assertionErrorConstrDesc = MethodTypeDesc.of(CD_void, CD_Object)
  private val heapVarDesc = ClassDesc.of(heapVarTypeId.stringId)
  private val assertionErrorDesc = ClassDesc.ofInternalName(assertionErrorInternalName)
  private val closureFunName = "run"

  private val javaLangMathDesc = ClassDesc.ofInternalName("java/lang/Math")

  override def apply(input: (Program, SubtypingInfo)): List[String] = {
    val (program, subtypingInfo) = input

    given Program = program

    given DealiasingContext = DealiasingContext(program.typeAliases)

    given SimplifiedSubtypingContext = SimplifiedSubtypingContext(subtypingInfo.subtypingGraph)

    given ResolutionContext = ResolutionContext(program, er)(using CodeGen)

    given classHierarchyResolver: ClassHierarchyResolver = mkClassHierarchyResolver(subtypingInfo)

    val mainClasses = mutable.LinkedHashSet.empty[String]
    for (tSig <- program.runtimeSignatures) {
      if (tSig.functions.exists(_._2.isMain)) {
        mainClasses.add(tSig.id.stringId)
      }
      generateTypeDecl(tSig, program)
    }
    er.displayAndTerminateIfErrors()
    mainClasses.toList
  }

  private def generateTypeDecl(tSig: RuntimeTypeSignature, program: Program)
                              (using DealiasingContext, SimplifiedSubtypingContext, ResolutionContext, ClassHierarchyResolver): Unit = {
    val tid = tSig.id
    val path = mkPathToClass(tid)
    Files.createDirectories(path.getParent)
    ClassFile.of(ClassHierarchyResolverOption.of(summon[ClassHierarchyResolver])).buildTo(
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
        tSig.declPosOpt.foreach { declPos =>
          cb.`with`(SourceFileAttribute.of(declPos.srcCodeProviderName))
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

        given TypeParamsContext = TypeParamsContext(tSig.typeParams)

        generateFields(tid, tSig.fields.values, cb)
        generateFunctions(tSig, cb)(using program)
        generateInterfacesList(tSig.directSupertypes.map(_.typeName), cb)
      }
    )
  }

  // TODO maybe there could be an issue with the ClassHierarchyResolver not being aware of the subtyping relationship between closures and the Closure interface
  private def mkClassHierarchyResolver(subtypingInfo: SubtypingInfo)(using dealiasingCtx: DealiasingContext, resolCtx: ResolutionContext): ClassHierarchyResolver = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val interfaces = util.ArrayList[ClassDesc]()
    val superClasses = util.HashMap[ClassDesc, ClassDesc]()
    for ((tid, superClassesMap) <- subtypingInfo.flattenedSupertypesSubstitutions) {
      val tDesc = tConv.descriptorFor(tid)
      val tSig = resolCtx.resolveTypeSigAs[RuntimeTypeSignature](tid).get
      if (tSig.isInstanceOf[AbstractTypeSig]) {
        interfaces.add(tDesc)
      }
      for ((superTid, _) <- superClassesMap) {
        superClasses.put(tDesc, tConv.descriptorFor(superTid))
      }
    }
    val closureTypeDesc = ClassDesc.of(StdLib.closureTypeId.stringId)
    interfaces.add(closureTypeDesc)
    for (closure <- closuresNamer.closures) {
      superClasses.put(ClassDesc.of(closure.stringId), closureTypeDesc)
    }
    ClassHierarchyResolver.of(interfaces, superClasses)
      .orElse(ClassHierarchyResolver.defaultResolver())
      .cached()
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

  private def generateFields(ownerId: TypeIdentifier, fields: Iterable[Field], cb: ClassBuilder)
                            (using TypeParamsContext, DealiasingContext): Unit = {
    // we ignore accessors: the IR generator already added them to the list of functions
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    for (fld <- fields) {
      var flags = ClassFile.ACC_PRIVATE
      if (fld.isStable) {
        flags |= ClassFile.ACC_FINAL
      }
      cb.withField(fld.id.stringId, tConv.descriptorFor(fld.tpe), flags)
    }
  }

  private def generateConstructor(tSig: ConcreteTypeSig, cb: ClassBuilder, isPrivate: Boolean)
                                 (using TypeParamsContext, DealiasingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tDesc = tConv.descriptorFor(tSig.id)
    val constrDesc = mkConstrDesc(tSig)
    val flags = if isPrivate then ClassFile.ACC_PRIVATE else ClassFile.ACC_PUBLIC
    cb.withMethod(INIT_NAME, constrDesc, flags, mb => mb.withCode(cb => {
      cb.aload(cb.receiverSlot())
      cb.dup()
      cb.invokespecial(CD_Object, INIT_NAME, MethodTypeDesc.of(CD_void))
      cb.astore(0)
      cb.localVariable(0, tSig.id.nonPrefixedId, tDesc, cb.startLabel(), cb.endLabel())
      var paramSlotIdx = 1
      for (fld <- tSig.fields.values) {
        cb.aload(0)
        cb.aload(paramSlotIdx)
        val fldId = fld.id.stringId
        val fldTypeDesc = tConv.descriptorFor(fld.tpe)
        cb.putfield(tDesc, fldId, fldTypeDesc)
        cb.localVariable(paramSlotIdx, fldId, fldTypeDesc, cb.startLabel(), cb.endLabel())
        paramSlotIdx += tConv.kindFor(fld.tpe).slotSize()
      }
      cb.return_()
    }))
  }

  private def generateFunctions(ownerTypeSig: RuntimeTypeSignature, cb: ClassBuilder)
                               (using program: Program, dealiasingCtx: DealiasingContext,
                                simplifiedSubtypingCtx: SimplifiedSubtypingContext, resolCtx: ResolutionContext,
                                classHierarchyResolver: ClassHierarchyResolver): Unit = {
    given GlobalValuesContext = program.globalValuesContext

    val ownerId = ownerTypeSig.id
    val functions = ownerTypeSig.functions.values
    for (funSig <- functions) {
      val bodyOpt = program.functions.apply(ownerId, funSig.descriptor).bodyOpt
      generateFunc(funSig, bodyOpt, ownerTypeSig, cb)
      if (funSig.isMain) {
        generateMainFunc(ownerId, funSig, cb)
      }
    }
  }

  private def generateMainFunc(ownerId: TypeIdentifier, mainFunSig: FunctionSignature, cb: ClassBuilder)
                              (using ResolutionContext, DealiasingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val ownerTypeDesc = tConv.descriptorFor(ownerId)
    cb.withMethod(mainFuncName, MethodTypeDesc.of(CD_void, CD_String.arrayType()), ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC, mb => mb.withCode(cb => {
      cb.getstatic(ownerTypeDesc, objectInstanceFieldName, ownerTypeDesc)
      if (mainFunSig.paramsWithoutThis.nonEmpty) {
        // this has to be an array of Strings
        cb.aload(0)
      }
      cb.invokevirtual(ownerTypeDesc, "$" + mainFunSig.functionName.stringId, mkFunDesc(mainFunSig)(using TypeParamsContext.empty))
      cb.return_()
    }))
  }

  private def generateFunc(funSig: FunctionSignature, bodyOpt: Option[IRcorne.Scope], ownerSig: TypeSignature, cb: ClassBuilder)
                          (using DealiasingContext, SimplifiedSubtypingContext, GlobalValuesContext, ResolutionContext, ClassHierarchyResolver): Unit = {
    given tpCtx: TypeParamsContext = TypeParamsContext(ownerSig.typeParams ++ funSig.typeParams)

    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val isStaticStringFunc = StdLib.hasReceiver(stringTypeId)(funSig) && StdLibFunctions.stringFuncRedirectFor(funSig).isEmpty
    val funDesc = mkFunDesc(funSig, extractParams = if isStaticStringFunc then _.paramsInclThis else _.paramsWithoutThis)
    var flags = funSig.visibility match {
      case Visibility.Private => ClassFile.ACC_PRIVATE
      case Visibility.Public => ClassFile.ACC_PUBLIC
    }
    if (funSig.overridability == Overridability.Abstract) {
      flags |= ClassFile.ACC_ABSTRACT
    }
    if (isStaticStringFunc) {
      flags |= ClassFile.ACC_STATIC
    }
    val funName = if funSig.isMain then "$" + funSig.functionName.stringId else funSig.functionName.stringId
    cb.withMethod(funName, funDesc, flags, mb => {
      StdLibFunctions.intrinsicFor(funSig) match {
        case Some(genIntrinsicFunc) =>
          genIntrinsicFunc(mb)
        case None =>
          bodyOpt.foreach { body =>
            mb.withCode(cb => {

              given funGenCtx: FunctionGenerationContext = FunctionGenerationContext(summon[GlobalValuesContext], tpCtx, funSig.isSyntheticAccessor, funSig.ownerName, funSig.retType, closureInfoOpt = None)

              for ((idVal, tpe) <- funSig.paramsInclThis) {
                allocateAndDeclare(idVal, cb, body)
              }
              generateScope(body, cb)
              if (!body.hasExited) {
                cb.return_()
              }
            })
          }
      }
    })
  }


  private def mkFunDesc(funSig: FunctionSignature, extractParams: FunctionSignature => Iterable[(NamedIdValue, Type)] = _.paramsWithoutThis)
                       (using tpCtx: TypeParamsContext, resolCtx: ResolutionContext, dealiasingCtx: DealiasingContext): MethodTypeDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tSig = resolCtx.resolveTypeSigAs[RuntimeTypeSignature](funSig.receiverType.asInstanceOf[NamedType].typeName).get
    val subst = (tSig.typeParams ++ funSig.typeParams).map(tp => tp.tid -> tp.upperBoundOpt.getOrElse(NullableType(AnyType))).toMap
    MethodTypeDesc.of(tConv.descriptorFor(funSig.retType.substitute(subst, Map.empty)),
      extractParams(funSig).map((_, tpe) => tConv.descriptorFor(tpe.substitute(subst, Map.empty))).toJavaUtilList)
  }

  private def mkConstrDesc(tSig: ConcreteTypeSig)(using DealiasingContext): MethodTypeDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    MethodTypeDesc.of(CD_void, tSig.fields.values.map(f => tConv.descriptorFor(f.tpe)(using TypeParamsContext(tSig.typeParams))).toArray *)
  }

  private def mkPathToClass(typeId: TypeIdentifier): Path = {
    typeId.prefixes
      .foldLeft(outputDirectoryPath)(_.resolve(_))
      .resolve(typeId.nonPrefixedId + FileExtensions.dot(_.clazz))
  }

  private def generateScope(scope: IRcorne.Scope, cb: CodeBuilder)
                           (using funGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext,
                            simplifiedSubtypingCtx: SimplifiedSubtypingContext, resolCtx: ResolutionContext,
                            globalValsCtx: GlobalValuesContext, classHierarchyResolver: ClassHierarchyResolver): Unit = {
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

  private def generateInstr(instr: IRcorne.Instr, cb: CodeBuilder, currScope: IRcorne.Scope)
                           (using funGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext,
                            simplifiedSubtypingCtx: SimplifiedSubtypingContext, resolCtx: ResolutionContext,
                            globalValsCtx: GlobalValuesContext, classHierarchyResolver: ClassHierarchyResolver): Unit = {
    given TypeParamsContext = funGenCtx.typeParamsCtx

    instr match {

      case scope: IRcorne.Scope => generateScope(scope, cb)

      case IRcorne.Loop(cond, condEvalResultVal, body, variables) =>
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

      case IRcorne.Disjunction(condEvalResultVal, thenBr, elseBr, variables) =>
        for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
          val afterThenValTypeKind = typeKindOf(afterThenVal, thenBr)
          val afterElseValTypeKind = typeKindOf(afterElseVal, elseBr)
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
          allocateAndDeclareIfNew(afterThenVal, thenBr, cb)
          allocateAndDeclareIfNew(afterElseVal, elseBr, cb)
        }
        val elseBrLabel = cb.newLabel()
        val afterDisjLabel = cb.newLabel()
        genValueLoad(condEvalResultVal, currScope, cb)
        cb.ifeq(elseBrLabel)
        generateScope(thenBr, cb)
        for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
          genValueMove(joinedVal, afterThenVal, thenBr, cb)
        }
        cb.goto_(afterDisjLabel)
        cb.labelBinding(elseBrLabel)
        generateScope(elseBr, cb)
        for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
          genValueMove(joinedVal, afterElseVal, elseBr, cb)
        }
        cb.labelBinding(afterDisjLabel)
        cb.nop()

      case IRcorne.StaticTypeAssert(value, tpe) => ()

      case IRcorne.AssignVal(assigned, src) =>
        genValueMove(assigned, src, currScope, cb)

      case IRcorne.AssignIntConst(assigned, src) =>
        cb.loadConstant(src)
        genValueStore(assigned, currScope, cb)

      case IRcorne.AssignBoolConst(assigned, src) =>
        val srcAsInt = if src then 1 else 0
        cb.loadConstant(srcAsInt)
        genValueStore(assigned, currScope, cb)

      case IRcorne.AssignStringConst(assigned, src) =>
        val cstEntry = cb.constantPool().stringEntry(src)
        cb.ldc(cstEntry)
        genValueStore(assigned, currScope, cb)

      case IRcorne.NumNeg(assigned, operand) =>
        genValueLoad(operand, currScope, cb)
        dispatchArithOnVal(operand, currScope, whenInt = {
          cb.ineg()
        }, whenDouble = {
          cb.dneg()
        })
        genValueStore(assigned, currScope, cb)

      case IRcorne.Add(assigned, lhs, rhs) if disableOverflowChecks => genArithKindBinop(assigned, lhs, rhs, currScope, cb, _.iadd(), _.dadd())
      case IRcorne.Sub(assigned, lhs, rhs) if disableOverflowChecks => genArithKindBinop(assigned, lhs, rhs, currScope, cb, _.isub(), _.dsub())
      case IRcorne.Mul(assigned, lhs, rhs) if disableOverflowChecks => genArithKindBinop(assigned, lhs, rhs, currScope, cb, _.imul(), _.dmul())
      case IRcorne.Div(assigned, lhs, rhs) if disableOverflowChecks => genArithKindBinop(assigned, lhs, rhs, currScope, cb, _.idiv(), _.ddiv())
      case IRcorne.Add(assigned, lhs, rhs) => genArithExactBinop(assigned, lhs, rhs, currScope, cb, "addExact")
      case IRcorne.Sub(assigned, lhs, rhs) => genArithExactBinop(assigned, lhs, rhs, currScope, cb, "subtractExact")
      case IRcorne.Mul(assigned, lhs, rhs) => genArithExactBinop(assigned, lhs, rhs, currScope, cb, "multiplyExact")
      case IRcorne.Div(assigned, lhs, rhs) => genArithExactBinop(assigned, lhs, rhs, currScope, cb, "divideExact")
      case IRcorne.Rem(assigned, lhs, rhs) => genArithKindBinop(assigned, lhs, rhs, currScope, cb, _.irem(), _.drem())

      case IRcorne.LogicNeg(assigned, operand) =>
        cb.iconst_m1()
        genValueLoad(operand, currScope, cb)
        cb.ixor()
        genValueStore(assigned, currScope, cb)

      case And(assigned, lhs, rhs) => genArithKindBinop(assigned, lhs, rhs, currScope, cb, _.iand(), _ => assert(false))
      case Or(assigned, lhs, rhs) => genArithKindBinop(assigned, lhs, rhs, currScope, cb, _.ior(), _ => assert(false))

      case IRcorne.Equal(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == INT && typeKindOf(rhs, currScope) == INT =>
        genIntCompBinop(assigned, lhs, rhs, currScope, cb, _.if_icmpeq(_))
      case IRcorne.Leq(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == INT =>
        genIntCompBinop(assigned, lhs, rhs, currScope, cb, _.if_icmple(_))
      case IRcorne.Lt(assigned, lhs, rhs) if typeKindOf(rhs, currScope) == INT =>
        genIntCompBinop(assigned, lhs, rhs, currScope, cb, _.if_icmplt(_))

      case IRcorne.Equal(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == DOUBLE && typeKindOf(rhs, currScope) == DOUBLE => ???
      case IRcorne.Leq(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == DOUBLE && typeKindOf(rhs, currScope) == DOUBLE => ???
      case IRcorne.Lt(assigned, lhs, rhs) if typeKindOf(lhs, currScope) == DOUBLE && typeKindOf(rhs, currScope) == DOUBLE => ???

      // FIXME enforce a.equals(a) and purity of equals when redefining equals
      case IRcorne.Equal(assigned, lhs, rhs) =>
        genValueLoad(lhs, currScope, cb)
        ensureAssignable(AnyType, dealiasedTypeOf(lhs, currScope), cb)
        genValueLoad(rhs, currScope, cb)
        ensureAssignable(AnyType, dealiasedTypeOf(rhs, currScope), cb)
        cb.invokevirtual(CD_Object, equalsMethodName, MethodTypeDesc.of(CD_boolean, CD_Object))
        genValueStore(assigned, currScope, cb)

      case IRcorne.Leq(assigned, lhs, rhs) =>
        throw AssertionError(s"unexpected Leq between ${dealiasedTypeOf(lhs, currScope)} and ${dealiasedTypeOf(rhs, currScope)}")
      case IRcorne.Lt(assigned, lhs, rhs) =>
        throw AssertionError(s"unexpected Lt between ${dealiasedTypeOf(lhs, currScope)} and ${dealiasedTypeOf(rhs, currScope)}")

      case fr@IRcorne.FieldRead(assigned, owner, field) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        val ownerDesc = tConv.descriptorFor(field.getReceiverSigUnsafe.id)
        genValueLoad(owner, currScope, cb)
        cb.getfield(ownerDesc, field.fieldId.stringId, tConv.descriptorFor(field.getReceiverSigUnsafe.fields.apply(field.fieldId).tpe))
        if (!(funGenCtx.isSyntheticAccessor && fr.getIdxInScopeOpt.get == 0)) {
          ensureAssignable(dealiasedTypeOf(assigned, currScope), field.getFieldUnsafe.tpe, cb)
          genValueStore(assigned, currScope, cb)
        }

      case IRcorne.FieldWrite(owner, field, rhs) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        val ownerDesc = tConv.descriptorFor(field.getReceiverSigUnsafe.id)
        genValueLoad(owner, currScope, cb)
        genValueLoad(rhs, currScope, cb)
        ensureAssignable(field.getFieldUnsafe.tpe, dealiasedTypeOf(rhs, currScope), cb)
        cb.putfield(ownerDesc, field.fieldId.stringId, tConv.descriptorFor(field.getReceiverSigUnsafe.fields.apply(field.fieldId).tpe))

      case InvokeFunc(assigned, receiver, func, typeArgs, args) if StdLibFunctions.staticRedirectFor(func.getFunSigUnsafe).isDefined =>
        val funSig = func.getFunSigUnsafe
        val (definingClassDesc, funName, funDesc) = StdLibFunctions.staticRedirectFor(funSig).get
        generateArgsList(args, funSig, Map.empty, cb, currScope)
        cb.invokestatic(definingClassDesc, funName, funDesc)
        ensureAssignable(dealiasedTypeOf(assigned, currScope), funSig.retType, cb)
        genValueStore(assigned, currScope, cb)

      // Array methods
      case IRcorne.InvokeFunc(assigned, receiver, func, typeArgs, args) if isFunc(arrayTypeId, arrayGetFunId, 1)(func.getFunSigUnsafe) =>
        genValueLoad(receiver, currScope, cb)
        genValueLoad(args.head, currScope, cb)
        cb.aaload()
        if (typeKindOf(assigned, currScope) != TypeKind.REFERENCE) {
          val elemTypeDescUnboxed = typeDescOf(assigned, currScope)
          val elemTypeDescBoxed = boxDesc(elemTypeDescUnboxed)
          if (typeDescOf(receiver, currScope).componentType() == CD_Object) {
            cb.checkcast(elemTypeDescBoxed)
          }
          cb.invokevirtual(elemTypeDescBoxed, unboxingFunc(elemTypeDescBoxed), MethodTypeDesc.of(unboxDesc(elemTypeDescBoxed)))
        }
        genValueStore(assigned, currScope, cb)
      case IRcorne.InvokeFunc(assigned, receiver, func, typeArgs, args) if isFunc(arrayTypeId, arraySetFunId, 2)(func.getFunSigUnsafe) =>
        genValueLoad(receiver, currScope, cb)
        genValueLoad(args.head, currScope, cb)
        genValueLoad(args(1), currScope, cb)
        if (typeKindOf(args(1), currScope) != TypeKind.REFERENCE) {
          val elemTypeDescUnboxed = typeDescOf(args(1), currScope)
          val elemTypeDescBoxed = boxDesc(elemTypeDescUnboxed)
          cb.invokestatic(elemTypeDescBoxed, "valueOf", MethodTypeDesc.of(elemTypeDescBoxed, elemTypeDescUnboxed))
        }
        cb.aastore()
      case IRcorne.InvokeFunc(assigned, receiver, func, typeArgs, args) if isFunc(arrayTypeId, arraySizeFunId, 0)(func.getFunSigUnsafe) =>
        genValueLoad(receiver, currScope, cb)
        cb.arraylength()
        genValueStore(assigned, currScope, cb)

      case IRcorne.InvokeFunc(assigned, receiver, func, typeArgs, args) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        val funSig = func.getFunSigUnsafe
        val isStaticStringFunc = StdLib.hasReceiver(stringTypeId)(funSig) && StdLibFunctions.stringFuncRedirectFor(funSig).isEmpty
        genValueLoad(receiver, currScope, cb)
        val NamedType(receiverTypeId, receiverTypeArgs, _) = funSig.receiverType: @unchecked
        val recTypeSig = resolCtx.resolveTypeSigAs[RuntimeTypeSignature](receiverTypeId).get
        val typeArgsSubst = Map.from(recTypeSig.typeParams.map(_.tid).zip(receiverTypeArgs) ++ funSig.typeParams.map(_.tid).zip(typeArgs))
        generateArgsList(args, funSig, typeArgsSubst, cb, currScope)
        val (targetReceiverDesc, targetFunName, targetFunDesc) = StdLibFunctions.stringFuncRedirectFor(funSig) match {
          case Some(targetFunId, targetFunDesc) => (CD_String, targetFunId, targetFunDesc)
          case None => (tConv.descriptorFor(receiverTypeId), funSig.functionName.stringId, mkFunDesc(funSig, extractParams = if isStaticStringFunc then _.paramsInclThis else _.paramsWithoutThis))
        }
        if (isStaticStringFunc) {
          cb.invokestatic(ClassDesc.ofInternalName(licorneCoreStringInternalName), targetFunName, targetFunDesc)
        } else if (recTypeSig.isInstanceOf[ConcreteTypeSig]) {
          cb.invokevirtual(targetReceiverDesc, targetFunName, targetFunDesc)
        } else {
          cb.invokeinterface(targetReceiverDesc, targetFunName, targetFunDesc)
        }
        ensureAssignable(dealiasedTypeOf(assigned, currScope), funSig.retType.substitute(typeArgsSubst, Map.empty), cb)
        genValueStore(assigned, currScope, cb)

      case IRcorne.InvokeClosure(assigned, callee, closureTypingTarget, args) =>
        genValueLoad(callee, currScope, cb)
        cb.loadConstant(args.size)
        val argsArraySlot = funGenCtx.allocateSlotOfSize(1)
        cb.anewarray(CD_Object)
        cb.dup()
        cb.astore(argsArraySlot)
        for ((arg, idx) <- args.zipWithIndex) {
          cb.aload(argsArraySlot)
          cb.loadConstant(idx)
          genValueLoad(arg, currScope, cb)
          if (typeKindOf(arg, currScope) != TypeKind.REFERENCE) {
            val unboxedDesc = typeDescOf(arg, currScope)
            val boxedDesc = boxDesc(unboxedDesc)
            cb.invokestatic(boxedDesc, "valueOf", MethodTypeDesc.of(boxedDesc, unboxedDesc))
          }
          cb.aastore()
        }
        cb.invokeinterface(ClassDesc.of(StdLib.closureTypeId.stringId), closureFunName, MethodTypeDesc.of(CD_Object, CD_Object.arrayType()))
        val assignedKind = typeKindOf(assigned, currScope)
        if (assignedKind == TypeKind.VOID) {
          cb.pop()
        } else if (assignedKind != TypeKind.REFERENCE) {
          val unboxedDesc = typeDescOf(assigned, currScope)
          val boxedDesc = boxDesc(unboxedDesc)
          cb.checkcast(boxedDesc)
          cb.invokevirtual(boxedDesc, unboxingFunc(boxedDesc), MethodTypeDesc.of(unboxedDesc))
        } else {
          cb.checkcast(typeDescOf(assigned, currScope))
        }
        genValueStore(assigned, currScope, cb)


      case instantiate@IRcorne.Instantiate(assigned, StdLib.arrayTypeId, _, List((_, sizeVal))) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        val NamedType(StdLib.arrayTypeId, List(elemType), Nil) = getRuntimeType(instantiate.getOutType): @unchecked
        val elemDesc = tConv.descriptorFor(elemType)
        genValueLoad(sizeVal, currScope, cb)
        cb.anewarray(if elemDesc.isPrimitive then boxDesc(elemDesc) else elemDesc)
        genValueStore(assigned, currScope, cb)

      case IRcorne.Instantiate(assigned, classOrRecordName, typeArgs, fieldsInit) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        val fieldsInitMap = fieldsInit.toMap
        val createdObjTypeSig = resolCtx.resolveTypeSigAs[UserInstantiableTypeSig](classOrRecordName).get
        val desc = tConv.descriptorFor(classOrRecordName)
        cb.new_(desc)
        cb.dup()
        for (fld <- createdObjTypeSig.fields.values) {
          val argVal = fieldsInitMap.apply(fld.id)
          genValueLoad(argVal, currScope, cb)
          ensureAssignable(fld.tpe, dealiasedTypeOf(argVal, currScope), cb)
        }
        cb.invokespecial(desc, INIT_NAME, mkConstrDesc(createdObjTypeSig))
        genValueStore(assigned, currScope, cb)

      case IRcorne.MkClosure(assigned, params, body, isPure, closureTypeName) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        val paramsSet = params.map(_._1).toSet[IdValue]
        val freeVals = SeqMap.from(
          body.freeVals.toList.filterNot(paramsSet.contains)
            .filterNot(_.isInstanceOf[UninterpretedConstIdValue])
            .map(fv => fv -> getRuntimeType(dealiasedTypeOf(fv, currScope)))
        )
        val closureClassDesc = generateClosureClass(closureTypeName, params, body, freeVals, funGenCtx.rootEnclosingTypeName)
        cb.new_(closureClassDesc)
        cb.dup()
        for ((fv, tpe) <- freeVals) {
          genValueLoad(fv, currScope, cb)
        }
        cb.invokespecial(closureClassDesc, INIT_NAME, MethodTypeDesc.of(CD_void, freeVals.map((_, tpe) => tConv.descriptorFor(tpe)).toSeq *))
        genValueStore(assigned, currScope, cb)

      case IRcorne.MkHeapVar(assigned) =>
        val slot = allocateAndDeclare(assigned, cb, currScope)
        cb.new_(heapVarDesc)
        cb.dup()
        cb.aconst_null()
        cb.invokespecial(heapVarDesc, INIT_NAME, MethodTypeDesc.of(CD_void, CD_Object))
        cb.astore(slot)

      case IRcorne.HeapVarRead(assigned, heapVar) =>
        genValueLoad(heapVar, currScope, cb)
        cb.invokevirtual(heapVarDesc, heapVarGetFunId.stringId, MethodTypeDesc.of(CD_Object))
        val kindOfAssigned = typeKindOf(assigned, currScope)
        if (kindOfAssigned == TypeKind.VOID) {
          cb.pop()
        } else if (kindOfAssigned != TypeKind.REFERENCE) {
          val assignedTypeDescUnboxed = typeDescOf(assigned, currScope)
          val assignedTypeDescBoxed = boxDesc(assignedTypeDescUnboxed)
          cb.checkcast(assignedTypeDescBoxed)
          cb.invokevirtual(assignedTypeDescBoxed, unboxingFunc(assignedTypeDescBoxed), MethodTypeDesc.of(assignedTypeDescUnboxed))
        } else {
          cb.checkcast(typeDescOf(assigned, currScope))
        }
        genValueStore(assigned, currScope, cb)

      case IRcorne.HeapVarWrite(heapVar, newValue) =>
        genValueLoad(heapVar, currScope, cb)
        genValueLoad(newValue, currScope, cb)
        if (typeKindOf(newValue, currScope) != TypeKind.REFERENCE) {
          val assignedTypeDescUnboxed = typeDescOf(newValue, currScope)
          val assignedTypeDescBoxed = boxDesc(assignedTypeDescUnboxed)
          cb.invokestatic(assignedTypeDescBoxed, "valueOf", MethodTypeDesc.of(assignedTypeDescBoxed, assignedTypeDescUnboxed))
        }
        cb.invokevirtual(heapVarDesc, heapVarSetFunId.stringId, MethodTypeDesc.of(CD_void, CD_Object))

      case IRcorne.TypeTest(assigned, testedValue, testedTypeId) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        genValueLoad(testedValue, currScope, cb)
        cb.instanceOf(tConv.descriptorFor(testedTypeId))
        genValueStore(assigned, currScope, cb)

      case IRcorne.Cast(inValue, target) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        genValueLoad(inValue, currScope, cb)
        cb.checkcast(tConv.descriptorFor(target))
        genValueStore(inValue, currScope, cb)

      case conv@IRcorne.Conversion(assigned, inValue, targetType) =>
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

      case hCast@IRcorne.HybridCast(inValue) =>
        val skipThrowLabel = cb.newLabel()
        hCast.getModeUnsafe match {
          case HybridCastMode.AssertPredicate(predicate, compiledPredicate, resultValue) =>
            for (instr <- compiledPredicate) {
              generateInstr(instr, cb, currScope)
            }
            genValueLoad(resultValue, currScope, cb)
            cb.ifne(skipThrowLabel)
            cb.new_(assertionErrorDesc)
            cb.dup()
            cb.ldc(s"assertion ${SourceLevelFormulaPrinter.prettyprint(predicate)} failed")
            cb.invokespecial(assertionErrorDesc, INIT_NAME, assertionErrorConstrDesc)
            cb.athrow()
          case HybridCastMode.AssertNonNull =>
            genValueLoad(inValue, currScope, cb)
            cb.ifnonnull(skipThrowLabel)
            cb.new_(assertionErrorDesc)
            cb.dup()
            cb.ldc(s"non nullity assertion failed")
            cb.invokespecial(assertionErrorDesc, INIT_NAME, assertionErrorConstrDesc)
            cb.athrow()
        }
        cb.labelBinding(skipThrowLabel)

      case ret@IRcorne.Return(retVal) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        val retType = funGenCtx.expRetType
        if (!(funGenCtx.isSyntheticAccessor && ret.getIdxInScopeOpt.get == 1)) {
          genValueLoad(retVal, currScope, cb)
          ensureAssignable(retType, dealiasedTypeOf(retVal, currScope), cb)
        }
        cb.return_(tConv.kindFor(retType))
        throw TerminateScopeSignal

      case IRcorne.Panic(msg) =>
        cb.new_(assertionErrorDesc)
        cb.dup()
        genValueLoad(msg, currScope, cb)
        cb.invokespecial(assertionErrorDesc, INIT_NAME, assertionErrorConstrDesc)
        cb.athrow()
        throw TerminateScopeSignal

      case IRcorne.LocalDecl(localId, tpe) => ()

      case IRcorne.Unreachable() =>
        cb.new_(assertionErrorDesc)
        cb.dup()
        cb.ldc(unreachablePathMessage)
        cb.invokespecial(assertionErrorDesc, INIT_NAME, assertionErrorConstrDesc)
        cb.athrow()
        throw TerminateScopeSignal
    }
  }

  private def generateArgsList(args: List[IdValue], funSig: FunctionSignature, typeArgsSubst: Map[TypeIdentifier, Type], cb: CodeBuilder, currScope: Scope)
                              (using TypeParamsContext, FunctionGenerationContext, DealiasingContext, SimplifiedSubtypingContext, GlobalValuesContext): Unit = {
    for ((arg, paramType) <- args.zip(funSig.paramsWithoutThis.map(_._2.substitute(typeArgsSubst, Map.empty)))) {
      genValueLoad(arg, currScope, cb)
      ensureAssignable(paramType, dealiasedTypeOf(arg, currScope), cb)
    }
  }

  private def generateClosureClass(closureTypeName: TypeIdentifier, params: List[(Formulas.ParamIdValue, Type)], body: Scope, freeVals: SeqMap[IdValue, Type], enclosingClassId: TypeIdentifier)
                                  (using tpCtx: TypeParamsContext, dealiasingCtx: DealiasingContext, classHierarchyResolver: ClassHierarchyResolver,
                                   globalValsCtx: GlobalValuesContext, subtypingCtx: SimplifiedSubtypingContext, resolCtx: ResolutionContext): ClassDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val freeValFields = freeVals.map((fv, tpe) => mkFieldNameForFreeVal(fv) -> (fv, tpe))
    val closureClassDesc = ClassDesc.of(closureTypeName.stringId)
    ClassFile.of(ClassHierarchyResolverOption.of(classHierarchyResolver)).buildTo(
      mkPathToClass(closureTypeName),
      closureClassDesc,
      clb => {

        clb.withInterfaceSymbols(ClassDesc.of(StdLib.closureTypeId.stringId))

        // generate fields
        for ((fldId, (fv, tpe)) <- freeValFields) {
          clb.withField(fldId, tConv.descriptorFor(tpe), ClassFile.ACC_PRIVATE | ClassFile.ACC_FINAL)
        }

        // generate constructor
        clb.withMethod(INIT_NAME, MethodTypeDesc.of(CD_void, freeVals.map((_, tpe) => tConv.descriptorFor(tpe)).toSeq *), ClassFile.ACC_PUBLIC, mb => {
          mb.withCode(cb => {
            cb.aload(0)
            cb.invokespecial(CD_Object, INIT_NAME, MethodTypeDesc.of(CD_void))
            var slotIdx = 1
            for ((fldName, (fldFv, fldType)) <- freeValFields) {
              val k = tConv.kindFor(fldType)
              cb.aload(0)
              cb.loadLocal(k, slotIdx)
              cb.putfield(closureClassDesc, fldName, tConv.descriptorFor(fldType))
              slotIdx += k.slotSize()
            }
            cb.return_()
          })
        })

        // generate apply method
        val applyFunGenCtx = FunctionGenerationContext(globalValsCtx, tpCtx, isSyntheticAccessor = false, enclosingClassId, NullableType(AnyType), Some(
          freeValFields.map { case (fldName, (fv, tpe)) => (fv, (fldName, tpe)) }, closureClassDesc
        ))
        clb.withMethod(closureFunName, MethodTypeDesc.of(CD_Object, CD_Object.arrayType()), ClassFile.ACC_PUBLIC, mb => {
          mb.withCode(cb => {
            applyFunGenCtx.allocateSlotOfSize(1) // slot for this
            val argsArraySlot = applyFunGenCtx.allocateSlotOfSize(1)
            for (((paramVal, paramType), paramIdx) <- params.zipWithIndex) {
              val paramSlot = allocateAndDeclare(paramVal, cb, body)(using applyFunGenCtx)
              cb.aload(argsArraySlot)
              cb.loadConstant(paramIdx)
              cb.aaload()
              val paramKind = tConv.kindFor(paramType)
              if (paramKind != TypeKind.REFERENCE) {
                val unboxedTypeDesc = tConv.descriptorFor(paramType)
                val boxedTypeDesc = boxDesc(unboxedTypeDesc)
                cb.checkcast(boxedTypeDesc)
                cb.invokevirtual(boxedTypeDesc, unboxingFunc(boxedTypeDesc), MethodTypeDesc.of(unboxedTypeDesc))
              }
              cb.storeLocal(paramKind, paramSlot)
            }
            generateScope(body, cb)(using applyFunGenCtx)
            if (!body.hasExited) {
              cb.aconst_null()
              cb.areturn()
            }
          })
        })

      }
    )
    closureClassDesc
  }

  private def mkFieldNameForFreeVal(fv: IdValue): String =
    s"fv${fv.uid}" ++ (fv match {
      case fv: NamedIdValue => fv.name
      case IntermediateIdValue(definingScope, uid, nameHint) => nameHint
    })

  private def genValueMove(to: IdValue, from: IdValue, currScope: Scope, cb: CodeBuilder)
                          (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext, simplifiedSubtypingCtx: SimplifiedSubtypingContext, globalValsCtx: GlobalValuesContext): Unit = {
    given TypeParamsContext = funcGenCtx.typeParamsCtx

    val typeDescOfTo = typeDescOf(to, currScope)
    val typeDescOfFrom = typeDescOf(from, currScope)
    if (!funcGenCtx.hasSlotFor(from) || funcGenCtx.hasSlotFor(to) || funcGenCtx.getSlot(from) != allocateAndDeclareIfNew(to, currScope, cb) || typeDescOfFrom != typeDescOfTo) {
      genValueLoad(from, currScope, cb)
      ensureAssignable(dealiasedTypeOf(to, currScope), dealiasedTypeOf(from, currScope), cb)
      genValueStore(to, currScope, cb)
    }
  }

  private def genValueLoad(idVal: IdValue, currScope: Scope, cb: CodeBuilder, isHeapVarRefLoad: Boolean = false)
                          (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext, globalValsCtx: GlobalValuesContext): Unit = {
    given TypeParamsContext = funcGenCtx.typeParamsCtx

    idVal match {
      case _ if funcGenCtx.isNullVal(idVal) =>
        cb.aconst_null()
      case _ if funcGenCtx.isFieldLoad(idVal) =>
        val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
        val closureInfo = funcGenCtx.closureInfoOpt.get
        val (fldName, fldType) = closureInfo.freeValFields.apply(idVal)
        cb.aload(0)
        cb.getfield(closureInfo.closureClassDesc, fldName, tConv.descriptorFor(fldType))
      case _ =>
        val kind = if idVal.isInstanceOf[HeapVarIdValue] then TypeKind.REFERENCE else typeKindOf(idVal, currScope)
        if (kind != VOID) {
          if (funcGenCtx.hasSlotFor(idVal)) {
            val slot = funcGenCtx.getSlot(idVal)
            cb.loadLocal(kind, slot)
          } else {
            val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
            val objId = globalValsCtx.getNameOfObject(idVal).get
            val objDesc = tConv.descriptorFor(objId)
            cb.getstatic(objDesc, objectInstanceFieldName, objDesc)
          }
        }
    }
  }

  private def genValueStore(idVal: IdValue, currScope: Scope, cb: CodeBuilder)
                           (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext): Unit = {
    given TypeParamsContext = funcGenCtx.typeParamsCtx

    val kind = typeKindOf(idVal, currScope)
    idVal match {
      case _ if kind == VOID => ()
      case idVal: IntermediateIdValue if idVal.users.isEmpty =>
        genPop(kind, cb)
      case _ =>
        val slot = allocateAndDeclareIfNew(idVal, currScope, cb)
        cb.storeLocal(kind, slot)
    }
  }

  /**
   * Adds instructions for boxing, unboxing, or cast, if needed
   */
  private def ensureAssignable(dstType: Type, srcType: Type, cb: CodeBuilder)
                              (using tpCtx: TypeParamsContext, dealiasingCtx: DealiasingContext, simplifiedSubtypingCtx: SimplifiedSubtypingContext): Unit = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val dstDesc = tConv.descriptorFor(dstType)
    val dstKind = tConv.kindFor(dstType)
    val srcDesc = tConv.descriptorFor(srcType)
    val srcKind = tConv.kindFor(srcType)
    if (srcType == NullType && dstDesc.isPrimitive) {
      cb.new_(assertionErrorDesc)
      cb.dup()
      cb.ldc(nullUnboxingMessage)
      cb.invokespecial(assertionErrorDesc, INIT_NAME, assertionErrorConstrDesc)
      cb.athrow()
    } else if (srcType == NullType || srcKind == TypeKind.VOID && dstKind == TypeKind.VOID) {
      // nothing to do
    } else if (srcKind == TypeKind.VOID && dstKind != TypeKind.VOID) {
      cb.iconst_0()
    } else if (dstKind == TypeKind.VOID && srcKind != TypeKind.VOID) {
      cb.pop()
    } else if (srcDesc.isPrimitive && !dstDesc.isPrimitive) {
      val srcBoxedDesc = boxDesc(srcDesc)
      cb.invokestatic(srcBoxedDesc, "valueOf", MethodTypeDesc.of(srcBoxedDesc, srcDesc))
    } else if (!srcDesc.isPrimitive && dstDesc.isPrimitive) {
      val dstBoxedDesc = boxDesc(dstDesc)
      if (srcDesc != dstBoxedDesc) {
        cb.checkcast(dstBoxedDesc)
      }
      cb.invokevirtual(dstBoxedDesc, unboxingFunc(dstBoxedDesc), MethodTypeDesc.of(dstDesc))
    } else (getRuntimeType(dstType), getRuntimeType(srcType)) match {
      case (NamedType(dstTypeId, _, _), NamedType(srcTypeId, _, _)) if !simplifiedSubtypingCtx.isSubtype(srcTypeId, dstTypeId) =>
        cb.checkcast(dstDesc)
      case _ => ()
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
                                (using funGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext): Int = {
    given TypeParamsContext = funGenCtx.typeParamsCtx

    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tpe = rawTypeOf(idVal, currScope).get
    val kind = tConv.kindFor(tpe)
    val descr = tConv.descriptorFor(tpe)
    val slot = funGenCtx.allocateSlot(kind, idVal)
    idVal.name.split('.').lastOption.foreach { simplifiedName =>
      cb.localVariable(slot, simplifiedName, descr, cb.startLabel(), cb.endLabel())
    }
    slot
  }

  private def allocateAndDeclareIfNew(idVal: IdValue, currScope: Scope, cb: CodeBuilder)
                                     (using funcGenCtx: FunctionGenerationContext, dealiasingCtx: DealiasingContext): Int = {
    given TypeParamsContext = funcGenCtx.typeParamsCtx

    idVal match {
      case idVal: NamedIdValue if !funcGenCtx.hasSlotFor(idVal) =>
        allocateAndDeclare(idVal, cb, currScope)
      case _ =>
        funcGenCtx.getOrAllocSlot(typeKindOf(idVal, currScope), idVal)
    }
  }

  private def dealiasedTypeOf(idVal: IdValue, currScope: Scope)(using dealiasingCtx: DealiasingContext): Type =
    dealiasingCtx.dealiasType(rawTypeOf(idVal, currScope).getOrElse(NothingType))

  private def rawTypeOf(idVal: IdValue, currScope: Scope): Option[Type] = idVal match {
    case idVal: HeapVarIdValue => Some(NamedType(StdLib.heapVarTypeId, List.empty, List.empty))
    case _ => currScope.typeOfNoSmartcast(idVal)
  }

  private def typeDescOf(idVal: IdValue, currScope: Scope)(using TypeParamsContext, DealiasingContext): ClassDesc = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    val tpe = rawTypeOf(idVal, currScope).get
    tConv.descriptorFor(tpe)
  }

  private def typeKindOf(idVal: IdValue, currScope: Scope)(using TypeParamsContext, DealiasingContext): TypeKind = {
    val tConv = NonBoxingTypesConverter.fromAmbientDealiasingCtx
    rawTypeOf(idVal, currScope) match {
      case Some(tpe) => tConv.kindFor(tpe)
      case None => VOID
    }
  }

  private def genArithExactBinop(assigned: IdValue, lhs: IdValue, rhs: IdValue, currScope: Scope, cb: CodeBuilder, jvmMethodName: String)
                                (using FunctionGenerationContext, DealiasingContext, GlobalValuesContext): Unit = {
    genArithKindBinop(assigned, lhs, rhs, currScope, cb,
      _.invokestatic(javaLangMathDesc, jvmMethodName, MethodTypeDesc.of(CD_int, CD_int, CD_int)),
      _ => ??? // TODO implement for Doubles
    )
  }

  private def genArithKindBinop(assigned: IdValue, lhs: IdValue, rhs: IdValue, currScope: Scope, cb: CodeBuilder,
                                intOp: CodeBuilder => Unit, doubleOp: CodeBuilder => Unit)
                               (using FunctionGenerationContext, DealiasingContext, GlobalValuesContext): Unit = {
    given TypeParamsContext = summon[FunctionGenerationContext].typeParamsCtx

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
                             (using FunctionGenerationContext, DealiasingContext, GlobalValuesContext): Unit = {
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

  private def dispatchArithOnVal(idVal: IdValue, currScope: Scope, whenInt: => Unit, whenDouble: => Unit)(using TypeParamsContext, DealiasingContext): Unit =
    dispatchArithOnKind(typeKindOf(idVal, currScope), whenInt, whenDouble)

  private def dispatchArithOnKind(kind: TypeKind, whenInt: => Unit, whenDouble: => Unit): Unit = kind match {
    case INT | BOOLEAN =>
      val _ = whenInt
    case DOUBLE =>
      val _ = whenDouble
    case _ =>
      throw AssertionError(s"unexpected kind in arithmetic dispatcher: $kind")
  }

  private def genPop(k: TypeKind, cb: CodeBuilder): Unit = k.slotSize() match {
    case 0 => ()
    case 1 =>
      cb.pop()
    case 2 =>
      cb.pop2()
    case slotSize =>
      throw AssertionError(s"pop: unexpected size $slotSize (kind is $k)")
  }

}
