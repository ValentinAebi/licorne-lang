package compiler.smt

import compiler.lang.Formulas
import compiler.lang.Formulas.Formula
import io.ksmt.KContext
import io.ksmt.expr.KExpr
import io.ksmt.solver.KSolverStatus
import io.ksmt.solver.z3.KZ3Solver
import io.ksmt.sort.KIntSort

final class Solver(kCtx: KContext, kZ3Solver: KZ3Solver) {

  def check(): KSolverStatus = kZ3Solver.check()

  def checkSat(): Boolean = check() == KSolverStatus.SAT

  def checkUnsat(): Boolean = check() == KSolverStatus.UNSAT

  def onNewFrame[T](action: => T): T = {
    kZ3Solver.push()
    val res = action
    kZ3Solver.pop()
    res
  }

  def assertLeq(lhs: Formula, rhs: Formula): Unit = {
    for {
      l <- convertAllInt(lhs)
      r <- convertAllInt(rhs)
    } do {
      kZ3Solver.assert(kCtx.le(l, r))
    }
  }

  def assertLt(lhs: Formula, rhs: Formula): Unit = {
    for {
      l <- convertAllInt(lhs)
      r <- convertAllInt(rhs)
    } do {
      kZ3Solver.assert(kCtx.lt(l, r))
    }
  }

  private def convertAllInt(formula: Formula): Option[KExpr[KIntSort]] = formula match {
    case value: Formulas.IdValue => Some(kCtx.mkConst(value.toString, kCtx.mkIntSort()))
    case Formulas.IntConst(value) => Some(kCtx.mkIntNum(value))
    case Formulas.BoolConst(value) => None
    case Formulas.StringConst(value) => None
    case Formulas.Select(owner, field) => None
    case Formulas.Call(receiver, func, args) => None
    case Formulas.Plus(lhs, rhs) =>
      for {
        l <- convertAllInt(lhs)
        r <- convertAllInt(rhs)
      } yield kCtx.mkArithAdd(l, r)
    case Formulas.Neg(negated) =>
      for {
        n <- convertAllInt(negated)
      } yield kCtx.mkArithUnaryMinus(n)
    case Formulas.Times(lhs, rhs) =>
      for {
        l <- convertAllInt(lhs)
        r <- convertAllInt(rhs)
      } yield kCtx.mkArithMul(l, r) // TODO see if we keep or not, as it introduces indecidability
    case Formulas.DivBy(lhs, rhs) =>
      for {
        l <- convertAllInt(lhs)
        r <- convertAllInt(rhs)
      } yield kCtx.mkArithDiv(l, r) // TODO see if division and modulo should be included
    case Formulas.Modulo(lhs, rhs) => None
  }

}
