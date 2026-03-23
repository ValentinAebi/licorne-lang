package compiler.smt

import compiler.lang.Formulas
import compiler.lang.Formulas.*
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
    case value: IdValue => Some(kCtx.mkConst(value.toString, kCtx.mkIntSort()))
    case IntConst(value) => Some(kCtx.mkIntNum(value))
    case BoolConst(value) => None
    case StringConst(value) => None
    case Select(owner, field) => None
    case Call(receiver, func, args) => None
    case Plus(lhs, rhs) =>
      for {
        l <- convertAllInt(lhs)
        r <- convertAllInt(rhs)
      } yield kCtx.mkArithAdd(l, r)
    case Neg(negated) =>
      for {
        n <- convertAllInt(negated)
      } yield kCtx.mkArithUnaryMinus(n)
    case Times(lhs, rhs) =>
      for {
        l <- convertAllInt(lhs)
        r <- convertAllInt(rhs)
      } yield kCtx.mkArithMul(l, r) // TODO see if we keep or not, as it introduces indecidability
    case DivBy(lhs, rhs) =>
      for {
        l <- convertAllInt(lhs)
        r <- convertAllInt(rhs)
      } yield kCtx.mkArithDiv(l, r) // TODO see if division and modulo should be included
    case Modulo(lhs, rhs) => None
    case LogicalAnd(lhs, rhs) => None
    case LogicalOr(lhs, rhs) => None
    case LessOrEq(lhs, rhs) => None
    case LessThan(lhs, rhs) => None
    case TypePredicate(subject, tpe) => None
  }

}
