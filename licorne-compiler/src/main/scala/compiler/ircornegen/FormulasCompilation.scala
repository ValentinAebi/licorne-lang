package compiler.ircornegen

import compiler.irs.ircorne.Formulas.{Binop, Formula, IdValue, IntermediateIdValue}
import compiler.irs.ircorne.IRcorne.*
import compiler.irs.ircorne.{Formulas, IRcorne}
import compiler.valproxies.ProxyStore

import scala.collection.mutable

object FormulasCompilation {
  
  def convertFormulaToIR(formula: Formula, currScope: Scope, proxyStore: ProxyStore)
                        (typeInstr: RealInstr => Unit): (Iterable[IRcorne.RealInstr], IdValue) = {
    val instructions = mutable.ListBuffer.empty[IRcorne.RealInstr]
    val resVal = compileFormula(formula)(using instructions, currScope, proxyStore)
    for (instr <- instructions) {
      typeInstr(instr)
    }
    (instructions.toList, resVal)
  }

  private def compileFormula(formula: Formula)(using instrOut: mutable.ListBuffer[IRcorne.RealInstr], currScope: Scope, proxyStore: ProxyStore): IdValue = {

    def save(instr: IRcorne.AssigningInstr): Unit = {
      instrOut.addOne(instr)
      proxyStore.saveProxy(instr.assigned, formula)
    }

    formula match {

      case value: Formulas.IdValue => value

      case Formulas.IntConst(value) => withIntermediateValue { res =>
        save(AssignIntConst(res, value))
      }

      case Formulas.BoolConst(value) => withIntermediateValue { res =>
        save(AssignBoolConst(res, value))
      }

      case Formulas.StringConst(value) => withIntermediateValue { res =>
        save(AssignStringConst(res, value))
      }

      case Formulas.Select(owner, field) => withIntermediateValue { res =>
        val ownerVal = compileFormula(owner)
        save(FieldRead(res, ownerVal, field.copy))
      }

      case Formulas.FunCall(receiver, func, typeArgs, args) => withIntermediateValue { res =>
        val recVal = compileFormula(receiver)
        val argVals = args.map(compileFormula)
        save(InvokeFunc(res, recVal, func.copy, typeArgs, argVals))
      }

      case Formulas.ClosureCall(callee, closureTypingTarget, args) => withIntermediateValue { res =>
        val calleeVal = compileFormula(callee)
        val argVals = args.map(compileFormula)
        save(InvokeClosure(res, calleeVal, closureTypingTarget.copy, argVals))
      }

      case Formulas.PureClosureValue(params, body, closureVal) => closureVal

      case plus@Formulas.Plus(lhs, rhs) => genBinop(plus, Add(_, _, _))
      case times@Formulas.Times(lhs, rhs) => genBinop(times, Mul(_, _, _))
      case div@Formulas.DivBy(lhs, rhs) => genBinop(div, Div(_, _, _))
      case mod@Formulas.Modulo(lhs, rhs) => genBinop(mod, Rem(_, _, _))

      case Formulas.Neg(operand) => withIntermediateValue { res =>
        val operandVal = compileFormula(operand)
        save(NumNeg(res, operandVal))
      }

      case Formulas.LogicalNot(operand) => withIntermediateValue { res =>
        val operandVal = compileFormula(operand)
        save(LogicNeg(res, operandVal))
      }

      case and@Formulas.LogicalAnd(lhs, rhs) => genBinop(and, And(_, _, _))
      case or@Formulas.LogicalOr(lhs, rhs) => genBinop(or, Or(_, _, _))

      case eq@Formulas.Equality(lhs, rhs) => genBinop(eq, Equal(_, _, _))
      case leq@Formulas.LessOrEq(lhs, rhs) => genBinop(leq, Leq(_, _, _))
      case lt@Formulas.LessThan(lhs, rhs) => genBinop(lt, Lt(_, _, _))

      case Formulas.TypePredicate(subject, tpe) => withIntermediateValue { res =>
        val subjVal = compileFormula(subject)
        save(TypeTest(res, subjVal, tpe))
      }

      case Formulas.Phi(terms) =>
        throw AssertionError("cannot convert phi formula")

      case Formulas.WrappedScope(resVal, scope) =>
        instrOut.addOne(scope)
        resVal
    }
  }

  private def genBinop(binop: Binop, mkInstr: (res: IntermediateIdValue, lhs: IdValue, rhs: IdValue) => AssigningInstr)
                   (using instructions: mutable.ListBuffer[IRcorne.RealInstr], currScope: Scope, proxyStore: ProxyStore): IntermediateIdValue =
    withIntermediateValue { res =>
      val lhsVal = compileFormula(binop.lhs)
      val rhsVal = compileFormula(binop.rhs)
      val instr = mkInstr(res, lhsVal, rhsVal)
      instructions.addOne(instr)
      proxyStore.saveProxy(instr.assigned, binop)
    }

  private def withIntermediateValue(action: IntermediateIdValue => Unit, idHint: String = "f_interm")(using currScope: Scope): IntermediateIdValue = {
    val interm = currScope.newIntermediate(idHint)
    action(interm)
    interm
  }

}
