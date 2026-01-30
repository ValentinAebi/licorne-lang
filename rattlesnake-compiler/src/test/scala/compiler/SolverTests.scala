package compiler

import compiler.solver.Solver
import lang.Formulas
import lang.Formulas.*
import lang.Formulas.RegularIdValue
import lang.Types.IntRangeType
import lang.Types.IntRangeType.Bound.{Max, Min}
import org.junit.{Assert, Test}
import org.junit.Assert.{assertEquals, fail}

class SolverTests {

  @Test def simplifyRangeUsingMockSolverTest(): Unit = {

    val a0 = RegularIdValue("a", 0)
    val b0 = RegularIdValue("b", 0)
    val c0 = RegularIdValue("c", 0)
    val d0 = RegularIdValue("d", 0)
    val e0 = RegularIdValue("e", 0)
    val f0 = RegularIdValue("f", 0)

    val mockSolver = new Solver {
      override def assert(formula: Formulas.Formula): Unit = fail("not implemented")

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

      override def isSatisfiable(formula: Formulas.Formula): Boolean = fail("not implemented")
    }

    val exp = IntRangeType(Max(Set(b0, d0)), Min(Set(b0, e0)))
    val input = IntRangeType(Max(Set(a0, b0, c0, d0)), Min(Set(b0, d0, e0)))
    val out = mockSolver.simplifyRange(input)
    assertEquals(exp, out)
  }

  private def fail(msg: String): Nothing = {
    Assert.fail(msg)
    assert(false)
  }

}
