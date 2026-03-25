package compiler.simplification

import compiler.identifiers.NormalFunOrVarId
import compiler.irs.SSA.Scope
import compiler.lang.Formulas.*
import compiler.lang.FormulasDsl.*
import compiler.lang.FormulasDsl.autoConvertIntToIConst
import compiler.lang.Types.IntRangeType
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.smt.Solver
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.assertEquals
import org.junit.Test

final class SimplificationTests {

  private val dummyScope = Scope.root(GlobalValuesContext())

  private def mkVal(id: String): ValIdValue =
    ValIdValue(NormalFunOrVarId(id), dummyScope, 0)

  private val a = mkVal("a")
  private val b = mkVal("b")

  private val `[a,b]` = IntRangeType(a, b)

  @Test def simplifyImpossibleTypeTest(): Unit = usingFreshSimplifier { (simplifier, solver) =>
    solver.assert(b + 2 <= a)
    assertEquals(NothingType, simplifier.simplify(`[a,b]`))
  }

  @Test def doNotSimplifyTest1(): Unit = usingFreshSimplifier { (simplifier, _) =>
    assertEquals(`[a,b]`, simplifier.simplify(`[a,b]`))
  }

  @Test def doNotSimplifyTest2(): Unit = usingFreshSimplifier { (simplifier, solver) =>
    solver.assert(a + 2 <= b)
    assertEquals(`[a,b]`, simplifier.simplify(`[a,b]`))
  }

  @Test def simplifyLinearFormulaTest1(): Unit = usingFreshSimplifier { (simplifier, _) =>
    // @formatter:off
    assertEquals(6*a + 5*b + 24, simplifier.simplify(a + 5*b - 3*a - 2 + 25 + 8*a + 1))
    // @formatter:on
  }

  @Test def simplifyLinearFormulaTest2(): Unit = usingFreshSimplifier { (simplifier, _) =>
    // @formatter:off
    assertEquals(9*a - 1, simplifier.simplify(2*4*a + a - 1))
    // @formatter:on
  }

  @Test def simplifyLinearFormulaTest3(): Unit = usingFreshSimplifier { (simplifier, _) =>
    // @formatter:off
    assertEquals(a, simplifier.simplify(2*a + 9*b - a - 5*b - 1 - 4*b + 1))
    assertEquals(IntConst(0), simplifier.simplify(2*a + 9*b - a - 5*b - 1 - 4*b + 1 - a))
    // @formatter:on
  }

  private def usingFreshSimplifier(action: (Simplifier, Solver) => Unit): Unit = Solver.usingFreshSolver { solver =>
    val simplifier = Simplifier(solver)
    action(simplifier, solver)
  }

}
