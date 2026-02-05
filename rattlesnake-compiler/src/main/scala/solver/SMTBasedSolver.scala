package solver

import SMTBasedSolver.StackFrame
import io.ksmt.KContext
import io.ksmt.expr.KExpr
import io.ksmt.solver.KSolverStatus
import io.ksmt.solver.z3.KZ3Solver
import io.ksmt.sort.{KBoolSort, KIntSort}
import lang.Formulas
import lang.Formulas.*
import lang.Types.IntRangeType
import lang.Types.IntRangeType.Bound
import lang.Types.IntRangeType.Bound.*

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable

final class SMTBasedSolver(
                            kCtx: KContext,
                            kZ3Solver: KZ3Solver
                          ) extends Solver {
  private var currFrame = StackFrame(None)

  override def onNewStackFrameWithAssumptions[T](assumptions: Formula*)(action: => T): T = {
    push()
    for (assumption <- assumptions) {
      offerAssertion(assumption)
    }
    val result = action
    pop()
    result
  }

  def push(): Unit = {
    kZ3Solver.push()
    currFrame = StackFrame(Some(currFrame))
  }

  def pop(): Unit = {
    kZ3Solver.pop()
    currFrame = currFrame.prevFrameOpt.get
  }

  def offerAssertion(formula: Formula): Unit = {
    for assertion <- convertToZ3Bool(formula)
      do kZ3Solver.assert(assertion)
  }

  def canProve(formula: Formula): Boolean = convertToZ3Bool(Not(formula)) match {
    case Some(negatedAsExpr) =>
      kZ3Solver.push()
      kZ3Solver.assert(negatedAsExpr)
      val result = kZ3Solver.check()
      kZ3Solver.pop()
      result == KSolverStatus.UNSAT
    case None => false
  }

  def isSatisfiable(formula: Formula): Boolean = convertToZ3Bool(formula) match {
    case Some(asExpr) =>
      kZ3Solver.push()
      kZ3Solver.assert(asExpr)
      val result = kZ3Solver.check()
      kZ3Solver.pop()
      result == KSolverStatus.SAT
    case None => false
  }

  def canProveIntRangeSubtyping(subT: IntRangeType, superT: IntRangeType): Boolean = {
    val IntRangeType(subL, subU) = subT
    val IntRangeType(superL, superU) = superT
    canProveLeq(superL, subL) && canProveLeq(subU, superU)
  }

  private def canProveLeq(lb: Bound, rb: Bound): Boolean = lb match {
    case Bound.Simple(l) => canProveLeq(l, rb)
    case Bound.Max(lbs) => lbs.forall(l => canProveLeq(l, rb))
    case Bound.Min(lbs) => lbs.exists(l => canProveLeq(l, rb))
    case Bound.NoBound => rb == NoBound
  }

  private def canProveLeq(l: Formula, rb: Bound): Boolean = rb match {
    case Bound.Simple(r) => canProve(LessOrEq(l, r))
    case Bound.Max(rbs) => rbs.exists(r => canProve(LessOrEq(l, r)))
    case Bound.Min(rbs) => rbs.forall(r => canProve(LessOrEq(l, r)))
    case Bound.NoBound => true
  }

  private def convertToZ3Bool(formula: Formula): Option[KExpr[KBoolSort]] = formula match {
    case idValue: IdValue => Some(kCtx.mkConst(idValue.toString, kCtx.mkBoolSort()))
    case True => Some(kCtx.mkBool(true))
    case False => Some(kCtx.mkBool(false))
    case Formulas.And(lhs, rhs) =>
      val lOpt = convertToZ3Bool(lhs)
      val rOpt = convertToZ3Bool(rhs)
      (lOpt, rOpt) match {
        case (Some(l), Some(r)) => Some(kCtx.mkAnd(l, r))
        case (Some(l), _) => Some(l)
        case (_, Some(r)) => Some(r)
        case _ => None
      }
    case Formulas.Or(lhs, rhs) =>
      for {
        l <- convertToZ3Bool(lhs)
        r <- convertToZ3Bool(rhs)
      } yield kCtx.mkOr(l, r)
    case Formulas.LessThan(lhs, rhs) =>
      for {
        l <- convertToZ3Int(lhs)
        r <- convertToZ3Int(rhs)
      } yield kCtx.mkArithLt(l, r)
    case LessOrEq(lhs, rhs) =>
      for {
        l <- convertToZ3Int(lhs)
        r <- convertToZ3Int(rhs)
      } yield kCtx.mkArithLe(l, r)
    case Formulas.Equal(lhs, rhs) =>
      for {
        l <- convertToZ3Int(lhs)
        r <- convertToZ3Int(rhs)
      } yield kCtx.mkEq(l, r)
    case Formulas.Not(operand) =>
      for op <- convertToZ3Bool(operand)
        yield kCtx.mkNot(op)
    // TODO use type info to also support record fields
    case atom if atom.isPureByConstruction =>
      Some(kCtx.mkConst(currFrame.nameFor(atom), kCtx.mkBoolSort()))
    case _ => None
  }

  private def convertToZ3Int(formula: Formula): Option[KExpr[KIntSort]] = formula match {
    case idValue: IdValue => Some(kCtx.mkConst(idValue.completeDescr, kCtx.mkIntSort()))
    case Formulas.IntConstant(cst) => Some(kCtx.getExpr(cst))
    case Formulas.Plus(lhs, rhs) =>
      for {
        l <- convertToZ3Int(lhs)
        r <- convertToZ3Int(rhs)
      } yield kCtx.plus(l, r)
    case Formulas.Minus(lhs, rhs) =>
      for {
        l <- convertToZ3Int(lhs)
        r <- convertToZ3Int(rhs)
      } yield kCtx.minus(l, r)
    case Formulas.Neg(operand) =>
      for op <- convertToZ3Int(operand)
        yield kCtx.mkArithUnaryMinus(op)
    // TODO use type info to also support record fields
    case atom if atom.isPureByConstruction =>
      Some(kCtx.mkConst(currFrame.nameFor(atom), kCtx.mkIntSort()))
    case _ => None
  }

}

object SMTBasedSolver {

  final class StackFrame(val prevFrameOpt: Option[StackFrame]) {
    private val uidGen = AtomicInteger(0)
    private val atomToName = mutable.Map.empty[Formula, String]
    private val nameToAtom = mutable.Map.empty[String, Formula]

    def nameFor(atom: Formula): String = {
      queryName(atom) match {
        case Some(name) => name
        case None =>
          val name = s"<atom$$${uidGen.incrementAndGet()}>"
          saveAtom(name, atom)
          name
      }
    }

    def getAtom(name: String): Formula =
      nameToAtom.getOrElse(name, prevFrameOpt.get.getAtom(name))

    private def saveAtom(name: String, atom: Formula): Unit = {
      atomToName(atom) = name
      nameToAtom(name) = atom
    }

    private def queryName(atom: Formula): Option[String] =
      atomToName.get(atom).orElse(prevFrameOpt.flatMap(_.queryName(atom)))

  }

}
