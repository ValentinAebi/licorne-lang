package compiler.backend

import compiler.identifiers.TypeIdentifier
import compiler.irs.ssa.SSA
import compiler.lang.{Field, FunctionSignature, RuntimeTypeSignature, Visibility}
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.typing.SubtypingInfo
import compiler.typing.contexts.DealiasingContext
import compiler.util.toJavaUtilList

import java.lang.classfile.CodeBuilder.BlockCodeBuilder
import java.lang.classfile.{ClassBuilder, ClassFile, CodeBuilder}
import java.lang.constant.{ClassDesc, MethodTypeDesc}
import java.nio.file.Path


final class Backend(outputDirectoryPath: Path) extends CompilerStep[(Program, SubtypingInfo), Unit] {

  // FIXME see if lower versions can be supported
  private val javaVersionCode = (ClassFile.JAVA_25_VERSION, 0)

  override def apply(input: (Program, SubtypingInfo)): Unit = {
    val (program, subtypingInfo) = input

    given Program = program

    given DealiasingContext = DealiasingContext(program.typeAliases)

    ???
  }

  private def generateType(tSig: RuntimeTypeSignature, program: Program)(using DealiasingContext): Unit = {
    val tid = tSig.id
    ClassFile.of().buildTo(
      generateClassPath(tid),
      ClassDesc.of(tid.stringId),
      cb => {
        val (majorVersion, minorVersion) = javaVersionCode
        cb.withVersion(majorVersion, minorVersion)
        generateFields(tid, tSig.fields.values, cb)
        generateFunctions(tid, tSig.functions.values, cb)(using program)
        generateInterfacesList(tSig.directSupertypes.map(_.typeName), cb)
      }
    )
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

  private def generateFunctions(ownerId: TypeIdentifier, functions: Iterable[FunctionSignature], cb: ClassBuilder)
                               (using program: Program, dealiasingCtx: DealiasingContext): Unit = {
    for (funSig <- functions) {
      val bodyOpt = program.functions.apply(ownerId, funSig.functionName).bodyOpt
      generateFunc(funSig, bodyOpt, cb)
    }
  }

  private def generateFunc(funSig: FunctionSignature, bodyOpt: Option[SSA.Scope], cb: ClassBuilder)(using DealiasingContext): Unit = {
    cb.withMethod(funSig.functionName.stringId, generateFunDescr(funSig), generateFunFlags(funSig), mb => {
      bodyOpt.foreach { body =>
        mb.withCode(cb => generateScope(body, cb))
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

  private def generateClassPath(typeId: TypeIdentifier): Path = {
    typeId.prefixes
      .foldLeft(outputDirectoryPath)(_.resolve(_))
      .resolve(typeId.nonPrefixedId)
  }

  private def generateScope(scope: SSA.Scope, outerCb: CodeBuilder): Unit = {
    outerCb.block(innerCb => {
      // TODO generate entries for scope variables
      for (instr <- scope.instructions) {
        generateInstr(instr, innerCb, scope)
      }
    })
  }

  private def generateInstr(instr: SSA.Instr, cb: BlockCodeBuilder, currScope: SSA.Scope): Unit = instr match {
    case scope: SSA.Scope => generateScope(scope, cb)
    case SSA.Loop(cond, condVal, body, variables) => ???
    case SSA.Disjunction(condVal, thenBr, elseBr, variables) => ???
    case SSA.StaticTypeAssert(value, tpe) => ()
    case SSA.AssignVal(assigned, src) => ???
    case SSA.AssignIntConst(assigned, src) => ???
    case SSA.AssignBoolConst(assigned, src) => ???
    case SSA.AssignStringConst(assigned, src) => ???
    case SSA.NumNeg(assigned, operand) => ???
    case SSA.Add(assigned, lhs, rhs) => ???
    case SSA.Sub(assigned, lhs, rhs) => ???
    case SSA.Mul(assigned, lhs, rhs) => ???
    case SSA.Div(assigned, lhs, rhs) => ???
    case SSA.Rem(assigned, lhs, rhs) => ???
    case SSA.LogicNeg(assigned, operand) => ???
    case SSA.Equal(assigned, lhs, rhs) => ???
    case SSA.Leq(assigned, lhs, rhs) => ???
    case SSA.Lt(assigned, lhs, rhs) => ???
    case SSA.FieldRead(assigned, owner, field) => ???
    case SSA.HeapVarRead(assigned, heapVar) => ???
    case SSA.InvokeFunc(assigned, receiver, func, typeArgs, args) => ???
    case SSA.InvokeClosure(assigned, callee, closureTypingTarget, args) => ???
    case SSA.Instantiate(assigned, classOrRecordName, typeArgs, fieldsInit) => ???
    case SSA.MkClosure(assigned, params, body, isPure) => ???
    case SSA.MkHeapVar(assigned) => ???
    case SSA.TypeTest(assigned, testedValue, testedTypeId) => ???
    case SSA.Conversion(assigned, inValue, targetType) => ???
    case SSA.FieldWrite(owner, field, rhs) => ???
    case SSA.HeapVarWrite(heapVar, newValue) => ???
    case SSA.Return(retVal) => ???
    case SSA.Panic(msg) => ???
    case SSA.Cast(inValue, target) => ???
    case SSA.HybridCast(inValue) => ???
    case SSA.Drop(droppedValue) => ???
    case SSA.LocalDecl(localId, tpe) =>
      
    case SSA.Unreachable() => ???
  }

}
