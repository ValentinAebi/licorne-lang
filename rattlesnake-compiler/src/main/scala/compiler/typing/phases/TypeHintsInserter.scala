package compiler.typing.phases

import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.lang.Formulas.{Formula, IdValue}
import compiler.lang.RuntimeTypeSignature
import compiler.lang.Types.Type
import compiler.pipeline.CompilationStep.TypeHintsInsertion
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.typing.TypeHintsStore
import compiler.typing.contexts.{ResolutionContext, TypeVariablesContext}
import compiler.util.zipCommons
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeHintsInserter(
                               typeVarsCtx: TypeVariablesContext,
                               proxyStore: ProxyStore,
                               typeHintsStore: TypeHintsStore
                             ) extends CompilerStep[Program, Program] {

  private given CompilationStep = TypeHintsInsertion

  override def apply(program: Program): Program = {
    for {
      (funSig, func) <- program.functions
      body <- func.bodyOpt
    } {
      val fakeEr = ErrorReporter(
        _ => throw AssertionError("error reported during type hints insertion"),
        _ => throw AssertionError("fatal error during type hints insertion")
      )
      val resolCtx = ResolutionContext(program, typeVarsCtx, fakeEr)
      traverseScope(body, funSig.retType)(using resolCtx, program.globalValuesContext)
    }
    program
  }

  private def traverseScope(scope: Scope, expRetType: Type)
                           (using ResolutionContext, GlobalValuesContext): Unit = {
    for (instr <- scope.instructions.reverse) {
      traverseInstr(instr, expRetType)
    }
  }

  private def traverseInstr(instr: Instr, expRetType: Type)
                           (using resolutionCtx: ResolutionContext, globalValsCtx: GlobalValuesContext): Unit = instr match {
    case Loop(cond, condVal, body, variables) =>
      traverseScope(body, expRetType)
      traverseScope(cond, expRetType)
    case Disjunction(condVal, thenBr, elseBr, variables) =>
      for {
        DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables
        th <- typeHintsStore.getHints(joinedVal)
      } {
        typeHintsStore.addHint(afterThenVal, th)
        typeHintsStore.addHint(afterElseVal, th)
      }
      traverseScope(thenBr, expRetType)
      traverseScope(elseBr, expRetType)
    case StaticTypeAssert(value, tpe) =>
      typeHintsStore.addHint(value, tpe)
    case StaticAssert(value) => ()
    case AssignVal(assigned, src) =>
      for (th <- typeHintsStore.getHints(assigned)) {
        typeHintsStore.addHint(src, th)
      }
    case AssignIntConst(assigned, src) => ()
    case AssignBoolConst(assigned, src) => ()
    case AssignStringConst(assigned, src) => ()
    case NumNeg(assigned, operand) => ()
    case Add(assigned, lhs, rhs) => ()
    case Sub(assigned, lhs, rhs) => ()
    case Mul(assigned, lhs, rhs) => ()
    case Div(assigned, lhs, rhs) => ()
    case Rem(assigned, lhs, rhs) => ()
    case LogicNeg(assigned, operand) => ()
    case And(assigned, lhs, rhs) => ()
    case Or(assigned, lhs, rhs) => ()
    case Equal(assigned, lhs, rhs) => ()
    case Leq(assigned, lhs, rhs) => ()
    case Lt(assigned, lhs, rhs) => ()
    case FieldRead(assigned, owner, field) => ()
    case InvokeFunc(assigned, receiver, func, typeArgs, args) =>
      proxyStore.getProxy(receiver).foreach {
        case proxy: IdValue =>
          for {
            objId <- globalValsCtx.getNameOfObject(proxy)
            funSig <- resolutionCtx.resolveFunSig(objId, func.functionName).asOption
          } {
            val subst = mutable.Map.empty[IdValue, Formula]
            for (((paramVal, paramTypeRaw), argVal) <- funSig.paramsWithoutThis.zipCommons(args)) {
              val paramTypeSubst = paramTypeRaw.substitute(Map.empty, subst)
              typeHintsStore.addHint(argVal, paramTypeSubst)
              subst.put(paramVal, argVal)
            }
          }
        case proxy => ()
      }
    case InvokeClosure(assigned, callee, args) => ()
    case Instantiate(assigned, classOrRecordName, typeArgs) => ()
    case MkClosure(assigned, params, body) => ()
    case TypeTest(assigned, testedValue, testedTypeId) => ()
    case Conversion(assigned, inValue, targetType) => ()
    case FieldWrite(owner, field, rhs) => ()
    case Return(retVal) =>
      typeHintsStore.addHint(retVal, expRetType)
    case Panic(msg) => ()
    case Cast(inValue, target) => ()
    case Drop(droppedValue) => ()
    case LocalDecl(localId, tpe) => ()
    case scope: Scope =>
      traverseScope(scope, expRetType)
  }

}
