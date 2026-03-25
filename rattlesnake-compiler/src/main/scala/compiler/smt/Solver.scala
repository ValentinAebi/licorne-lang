package compiler.smt

import compiler.lang.Formulas
import compiler.lang.Formulas.*
import io.ksmt.KContext
import io.ksmt.expr.KExpr
import io.ksmt.solver.KSolverStatus
import io.ksmt.solver.z3.KZ3Solver
import io.ksmt.sort.{KBoolSort, KIntSort}

import scala.util.Using


final class Solver(kCtx: KContext, kZ3Solver: KZ3Solver) {

  def check(): KSolverStatus = kZ3Solver.check()

  def checkSat(): Boolean = check() == KSolverStatus.SAT

  def checkUnsat(): Boolean = check() == KSolverStatus.UNSAT

  def canProve(formula: Formula): Boolean = onNewFrame {
    assert(LogicalNot(formula))
    checkUnsat()
  }

  def canProveLeq(lhs: Formula, rhs: Formula): Boolean = onNewFrame {
    assertLt(rhs, lhs)
    checkUnsat()
  }
  
  def canProveLt(lhs: Formula, rhs: Formula): Boolean = onNewFrame {
    assertLeq(rhs, lhs)
    checkUnsat()
  }

  def canProveGeZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProveLeq(IntConst(0), f)
  }

  def canProveGtZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProveLeq(IntConst(1), f)
  }

  def canProveLeZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProveLeq(f, IntConst(0))
  }

  def canProveLtZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProveLeq(f, IntConst(-1))
  }

  def canProveNotZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProve(LogicalNot(Equality(f, IntConst(0))))
  }

  def onNewFrame[T](action: => T): T = {
    kZ3Solver.push()
    val res = action
    kZ3Solver.pop()
    res
  }

  def intMin(l: Formula, r: Formula): Option[Formula] = {
    if canProveLeq(l, r) then Some(l)
    else if canProveLeq(r, l) then Some(r)
    else None
  }

  def intMin(formulas: Iterable[Formula]): Option[Formula] = findMinOrMax(formulas, intMin)

  def intMax(l: Formula, r: Formula): Option[Formula] = {
    if canProveLeq(l, r) then Some(r)
    else if canProveLeq(r, l) then Some(l)
    else None
  }

  def intMax(formulas: Iterable[Formula]): Option[Formula] = findMinOrMax(formulas, intMax)

  private def findMinOrMax(formulas: Iterable[Formula], minOrMaxFunc: (Formula, Formula) => Option[Formula]): Option[Formula] = {
    val iter = formulas.iterator
    var minOrMax = iter.next()
    while (iter.hasNext) {
      minOrMaxFunc(minOrMax, iter.next()) match {
        case Some(newMinOrMax) =>
          minOrMax = newMinOrMax
        case None =>
          return None
      }
    }
    Some(minOrMax)
  }

  def assert(formulas: Formula*): Unit = {
    for {
      formula <- formulas
      kFormula <- convertBool(formula)
    } {
      kZ3Solver.assert(kFormula)
    }
  }

  def assertLeq(lhs: Formula, rhs: Formula): Unit = {
    for {
      l <- convertInt(lhs)
      r <- convertInt(rhs)
    } do {
      kZ3Solver.assert(kCtx.le(l, r))
    }
  }

  def assertLt(lhs: Formula, rhs: Formula): Unit = {
    for {
      l <- convertInt(lhs)
      r <- convertInt(rhs)
    } do {
      kZ3Solver.assert(kCtx.lt(l, r))
    }
  }

  // TODO cache formula conversion
  private def convertInt(formula: Formula): Option[KExpr[KIntSort]] = formula match {
    case value: IdValue => Some(kCtx.mkConst(value.toString, kCtx.mkIntSort()))
    case IntConst(value) => Some(kCtx.mkIntNum(value))
    case BoolConst(value) => None
    case StringConst(value) => None
    // TODO encode selects
    case Select(owner, field) => None
    case Call(receiver, func, args) => None
    case Plus(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield kCtx.mkArithAdd(l, r)
    case Neg(negated) =>
      for {
        n <- convertInt(negated)
      } yield kCtx.mkArithUnaryMinus(n)
    case Times(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield kCtx.mkArithMul(l, r) // TODO see if we keep or not, as it introduces indecidability
    case DivBy(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield kCtx.mkArithDiv(l, r) // TODO see if division and modulo should be included
    case Modulo(lhs, rhs) => None
    case LogicalNot(operand) => None
    case LogicalAnd(lhs, rhs) => None
    case LogicalOr(lhs, rhs) => None
    case LessOrEq(lhs, rhs) => None
    case LessThan(lhs, rhs) => None
    case TypePredicate(subject, tpe) => None
    // FIXME additional cases
  }

  // TODO cache formula conversion
  private def convertBool(formula: Formula): Option[KExpr[KBoolSort]] = formula match {
    case value: IdValue => Some(kCtx.mkConst(value.toString, kCtx.mkBoolSort()))
    case IntConst(value) => None
    case BoolConst(value) => Some(kCtx.mkBool(value))
    case StringConst(value) => None
    // TODO encode selects
    case Select(owner, field) => None
    case Call(receiver, func, args) => None
    case Plus(lhs, rhs) => None
    case Neg(operand) => None
    case Times(lhs, rhs) => None
    case DivBy(lhs, rhs) => None
    case Modulo(lhs, rhs) => None
    case LogicalNot(operand) =>
      for {
        kOperand <- convertBool(operand)
      } yield kCtx.mkNot(kOperand)
    case LogicalAnd(lhs, rhs) =>
      for {
        l <- convertBool(lhs)
        r <- convertBool(rhs)
      } yield kCtx.mkAnd(l, r)
    case LogicalOr(lhs, rhs) =>
      for {
        l <- convertBool(lhs)
        r <- convertBool(rhs)
      } yield kCtx.mkOr(l, r)
    case LessOrEq(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield kCtx.mkArithLe(l, r)
    case LessThan(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield kCtx.mkArithLt(l, r)
    case TypePredicate(subject, tpe) => None
    // FIXME additional cases
  }

}

object Solver {
  
  def usingFreshSolver[T](f: Solver => T): T = Using(KContext()){ kCtx =>
    Using(KZ3Solver(kCtx)){ kZ3Solver =>
      val solver = Solver(kCtx, kZ3Solver)
      f(solver)
    }.get
  }.get
  
}
