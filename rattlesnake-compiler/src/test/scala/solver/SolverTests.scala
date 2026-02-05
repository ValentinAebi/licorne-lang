package solver

import io.ksmt.KContext
import io.ksmt.solver.z3.KZ3Solver
import lang.Formulas
import lang.Formulas.*
import lang.Types.IntRangeType
import lang.Types.IntRangeType.Bound.{Max, Min, Simple}
import org.junit.Assert.{assertEquals, assertFalse, assertTrue}
import org.junit.{Assert, Test}
import solver.{SMTBasedSolver, Solver}

import scala.util.Using

class SolverTests {

  @Test def z3IntRangeSubtypingTest(): Unit = {

    val a0 = RegularIdValue("a", 0)
    val b0 = RegularIdValue("b", 0)
    val c0 = RegularIdValue("c", 0)

    val `[0,b0]` = IntRangeType(IntConstant(0), b0)
    val `[1,a0]` = IntRangeType(IntConstant(1), a0)
    val `[0,max{c0,9}]` = IntRangeType(
      Simple(IntConstant(0)),
      Max(c0, IntConstant(9))
    )
    val `[a0,b0]` = IntRangeType(a0, b0)
    val `[c0,b0]` = IntRangeType(c0, b0)

    val resultsArray = new Array[Boolean](5)
    Using(KContext()) { kCtx =>
      Using(KZ3Solver(kCtx)) { kZ3Solver =>
        val solver = SMTBasedSolver(kCtx, kZ3Solver)
        //  a0 < b0 ; b0 <= 10
        solver.offerAssertion(LessThan(a0, b0))
        solver.offerAssertion(LessOrEq(b0, IntConstant(10)))
        //  [1,a0] <: [0,b0]  -->  true
        resultsArray(0) = solver.canProveIntRangeSubtyping(`[1,a0]`, `[0,b0]`)
        //  [0,b0] <: [1,a0]  -->  false
        resultsArray(1) = solver.canProveIntRangeSubtyping(`[0,b0]`, `[1,a0]`)
        //  [1,a0] <: [0,max{c0,9}]  -->  true
        resultsArray(2) = solver.canProveIntRangeSubtyping(`[1,a0]`, `[0,max{c0,9}]`)
        //  [0,b0] <: [0,max{c0,9}]  -->  false
        resultsArray(3) = solver.canProveIntRangeSubtyping(`[0,b0]`, `[0,max{c0,9}]`)
        //  [c0,b0] <: [a0,b0]  --> false
        resultsArray(4) = solver.canProveIntRangeSubtyping(`[c0,b0]`, `[a0,b0]`)
      }.get
    }.get
    assertTrue(resultsArray(0))
    assertFalse(resultsArray(1))
    assertTrue(resultsArray(2))
    assertFalse(resultsArray(3))
    assertFalse(resultsArray(4))
  }

  @Test def simplifyRangeUsingMockSolverTest(): Unit = {

    val a0 = RegularIdValue("a", 0)
    val b0 = RegularIdValue("b", 0)
    val c0 = RegularIdValue("c", 0)
    val d0 = RegularIdValue("d", 0)
    val e0 = RegularIdValue("e", 0)
    val f0 = RegularIdValue("f", 0)

    val mockSolver = new Solver {

      override def onNewStackFrameWithAssumptions[T](assumptions: Formula*)(action: => T): T =
        fail("not implemented")

      override def offerAssertion(formula: Formulas.Formula): Unit =
        fail("not implemented")

      override def canProve(formula: Formulas.Formula): Boolean = formula match {
        // f0 == d0
        case LessOrEq(`d0`, `f0`) => true
        case LessOrEq(`f0`, `d0`) => true
        case LessOrEq(`a0`, `b0`) => true
        case LessOrEq(`a0`, `c0`) => true
        case LessOrEq(`c0`, `b0`) => true
        case LessOrEq(`a0`, df) if df == d0 || df == f0 => true
        case LessOrEq(`e0`, df) if df == d0 || df == f0 => true
        case _ => false
      }

      override def isSatisfiable(formula: Formulas.Formula): Boolean =
        fail("not implemented")

      override def canProveIntRangeSubtyping(subT: IntRangeType, superT: IntRangeType): Boolean =
        fail("not implemented")
    }

    val exp = IntRangeType(Max(b0, d0), Min(b0, e0))
    val input = IntRangeType(Max(a0, b0, c0, d0), Min(b0, d0, e0))
    val out = mockSolver.simplifyRange(input)
    assertEquals(exp, out)
  }

  private def fail(msg: String): Nothing = {
    Assert.fail(msg)
    assert(false)
  }

}
