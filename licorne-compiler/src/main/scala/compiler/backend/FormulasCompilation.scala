package compiler.backend

import compiler.irs.ssa.Formulas.{Formula, IdValue, IntermediateIdValue}
import compiler.irs.ssa.SSA.*
import compiler.irs.ssa.{Formulas, SSA}

import scala.collection.mutable

object FormulasCompilation {

  def convertFormulaToSSA(formula: Formula, currScope: Scope): (Iterable[SSA.Instr], IdValue) = {
    val instructions = mutable.ListBuffer.empty[SSA.Instr]
    val resVal = compileFormula(formula)(using instructions, currScope)
    (instructions.toList, resVal)
  }

  private def compileFormula(formula: Formula)(using instrOut: mutable.ListBuffer[SSA.Instr], currScope: Scope): IdValue = {

    def save(instr: SSA.Instr): Unit = {
      instrOut.addOne(instr)
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
        save(FieldRead(res, ownerVal, field))
      }

      case Formulas.FunCall(receiver, func, typeArgs, args) => withIntermediateValue { res =>
        val recVal = compileFormula(receiver)
        val argVals = args.map(compileFormula)
        save(InvokeFunc(res, recVal, func, typeArgs, argVals))
      }

      case Formulas.ClosureCall(callee, closureTypingTarget, args) => withIntermediateValue { res =>
        val calleeVal = compileFormula(callee)
        val argVals = args.map(compileFormula)
        save(InvokeClosure(res, calleeVal, closureTypingTarget, argVals))
      }

      case Formulas.PureClosureValue(params, body, closureVal) => closureVal

      case Formulas.Plus(lhs, rhs) => genBinop(lhs, rhs, Add(_, _, _))
      case Formulas.Times(lhs, rhs) => genBinop(lhs, rhs, Mul(_, _, _))
      case Formulas.DivBy(lhs, rhs) => genBinop(lhs, rhs, Div(_, _, _))
      case Formulas.Modulo(lhs, rhs) => genBinop(lhs, rhs, Rem(_, _, _))

      case Formulas.Neg(operand) => withIntermediateValue { res =>
        val operandVal = compileFormula(operand)
        save(NumNeg(res, operandVal))
      }

      case Formulas.LogicalNot(operand) => withIntermediateValue { res =>
        val operandVal = compileFormula(operand)
        save(LogicNeg(res, operandVal))
      }

      case Formulas.LogicalAnd(lhs, rhs) => genBinop(lhs, rhs, And(_, _, _))
      case Formulas.LogicalOr(lhs, rhs) => genBinop(lhs, rhs, Or(_, _, _))

      case Formulas.Equality(lhs, rhs) => genBinop(lhs, rhs, Equal(_, _, _))
      case Formulas.LessOrEq(lhs, rhs) => genBinop(lhs, rhs, Leq(_, _, _))
      case Formulas.LessThan(lhs, rhs) => genBinop(lhs, rhs, Lt(_, _, _))

      case Formulas.TypePredicate(subject, tpe) => withIntermediateValue { res =>
        val subjVal = compileFormula(subject)
        save(TypeTest(res, subjVal, tpe))
      }

      case Formulas.Phi(terms) =>
        throw AssertionError("cannot convert phi formula")
    }
  }

  private def genBinop(lhs: Formula, rhs: Formula, mkInstr: (res: IntermediateIdValue, lhs: IdValue, rhs: IdValue) => Instr)
                   (using instructions: mutable.ListBuffer[SSA.Instr], currScope: Scope): IntermediateIdValue =
    withIntermediateValue { res =>
      val lhsVal = compileFormula(lhs)
      val rhsVal = compileFormula(rhs)
      val instr = mkInstr(res, lhsVal, rhsVal)
      instructions.addOne(instr)
    }

  private def withIntermediateValue(action: IntermediateIdValue => Unit, idHint: String = "f_interm")(using currScope: Scope): IntermediateIdValue = {
    val interm = currScope.newIntermediate(idHint)
    action(interm)
    interm
  }

}
