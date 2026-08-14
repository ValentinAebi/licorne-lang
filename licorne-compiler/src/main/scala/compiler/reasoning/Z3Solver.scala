package compiler.reasoning

import compiler.irs.ssa.Formulas
import compiler.irs.ssa.Formulas.*
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.typing.contexts.DealiasingContext
import compiler.valuesconversion.GlobalValuesContext
import io.ksmt.KContext
import io.ksmt.expr.KExpr
import io.ksmt.solver.KSolverStatus
import io.ksmt.solver.z3.KZ3Solver
import io.ksmt.sort.{KBoolSort, KSort}

import scala.collection.mutable


final class Z3Solver[IntSort <: KSort] private[reasoning](kCtx: KContext, kZ3Solver: KZ3Solver, ihm: IntHandlingMode[IntSort], converter: FormulasConverter[IntSort], counterExBoxOpt: Option[CounterexampleBox]) extends Solver {
  import converter.{convertBool, convertInt, convertObj}

  private given KContext = kCtx

  // useful for debugging
  private val assertionsStack = mutable.Stack(mutable.LinkedHashSet.empty[KExpr[KBoolSort]])
  
  export converter.acceptingPhisForInts

  def check(): KSolverStatus = kZ3Solver.check()

  def checkSat(): Boolean = check() == KSolverStatus.SAT

  def checkUnsat(): Boolean = {
    check() match {
      case KSolverStatus.SAT =>
         counterExBoxOpt.foreach {
          _.setModel(kZ3Solver.model())
        }
        false
      case KSolverStatus.UNSAT => true
      case KSolverStatus.UNKNOWN => false
    }
  }

  def canProve(formula: Formula): Boolean = onNewFrame {
    assert(LogicalNot(formula))
    checkUnsat()
  }

  def canProveImplication(premise: Formula, conseq: Formula): Boolean = onNewFrame {
    assert(premise)
    assert(LogicalNot(conseq))
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

  def canProveNotZero(f: Formula): Boolean = {
    canProve(LogicalNot(Equality(f, IntConst(0))))
  }

  def onNewFrame[T](action: => T): T = {
    assertionsStack.push(mutable.LinkedHashSet.empty)
    kZ3Solver.push()
    val res = try {
      action
    } finally {
      kZ3Solver.pop()
      assertionsStack.pop()
    }
    res
  }

  def intMin(l: Formula, r: Formula): Option[Formula] = {
    if canProveLeq(l, r) then Some(l)
    else if canProveLeq(r, l) then Some(r)
    else None
  }

  def intMin(formulas: Iterable[Formula]): Option[Formula] = findMinOrMax(formulas, intMin)

  override def discardNonMins(formulas: Iterable[Formula]): Iterable[Formula] = {
    // TODO what if some of the formulas are provably equal?
    formulas.filterNot(cand => formulas.exists(canProveLt(_, cand)))
  }

  def intMax(l: Formula, r: Formula): Option[Formula] = {
    if canProveLeq(l, r) then Some(r)
    else if canProveLeq(r, l) then Some(l)
    else None
  }

  def intMax(formulas: Iterable[Formula]): Option[Formula] = findMinOrMax(formulas, intMax)

  override def discardNonMax(formulas: Iterable[Formula]): Iterable[Formula] = {
    // TODO what if some of the formulas are provably equal?
    formulas.filterNot(cand => formulas.exists(canProveLt(cand, _)))
  }

  private def findMinOrMax(formulas: Iterable[Formula], minOrMaxFunc: (Formula, Formula) => Option[Formula]): Option[Formula] =
    if formulas.isEmpty then None
    else {
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

  def assert(formula: Formula): Unit = {
    for {
      kFormula <- convertBool(formula)
    } {
      doAssert(kFormula)
    }
  }

  def assert(formulas: Iterable[Formula]): Unit = {
    for {
      formula <- formulas
      kFormula <- convertBool(formula)
    } {
      doAssert(kFormula)
    }
  }

  def assertEq[S <: KSort](lhs: Formula, rhs: Formula, simplifiedType: SimplifiedType[S]): Unit = {
    val conversionFunc: Formula => Iterable[KExpr[S]] = (simplifiedType: @unchecked) match {
      case SimplifiedType.Integer[IntSort] () => convertInt
      case SimplifiedType.Boolean => convertBool
      case SimplifiedType.Object => convertObj
    }
    for {
      l <- conversionFunc(lhs)
      r <- conversionFunc(rhs)
    } do {
      doAssert(kCtx.eq(l, r))
    }
  }

  def assertLeq(lhs: Formula, rhs: Formula): Unit = {
    for {
      l <- convertInt(lhs)
      r <- convertInt(rhs)
    } do {
      doAssert(ihm.leq(l, r))
    }
  }

  def assertLt(lhs: Formula, rhs: Formula): Unit = {
    for {
      l <- convertInt(lhs)
      r <- convertInt(rhs)
    } do {
      doAssert(ihm.lt(l, r))
    }
  }

  def assertInRange(formula: Formula, range: IntRangeType): Unit = {
    range.lowerBoundOpt.foreach { lb =>
      assertLeq(lb, formula)
    }
    range.upperBoundOpt.foreach { ub =>
      assertLeq(formula, ub)
    }
  }

  override def takeType(subject: Formula, tpe: Types.Type)(using dealiasingCtx: DealiasingContext, globalValsCtx: GlobalValuesContext): Unit = {
    val itValue = globalValsCtx.itValue
    for (t <- dealiasingCtx.dealiasType(tpe.withTypeVarsExpanded).withTypeVarsExpanded.breakdownIfIntersection) {
      val predicate = t.asRefinedType.flattenedRefinement.predicate
      assert(predicate.substitute(itValue, subject))
    }
  }

  def canProveIsOutsideRange(formula: Formula, range: IntRangeType): Boolean = onNewFrame {
    range.lowerBoundOpt.exists { lb =>
      canProveLt(formula, lb)
    } || range.upperBoundOpt.exists { ub =>
      canProveLt(ub, formula)
    }
  }

  private def doAssert[S <: KSort](kFormula: KExpr[KBoolSort]) = {
    kZ3Solver.assert(kFormula)
    assertionsStack.head.addOne(kFormula)
  }

}
