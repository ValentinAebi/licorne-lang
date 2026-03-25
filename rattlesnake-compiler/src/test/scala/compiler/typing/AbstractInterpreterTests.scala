package compiler.typing

import compiler.identifiers.NormalFunOrVarId
import compiler.irs.SSA.Scope
import compiler.lang.Formulas.{IntConst, Plus, ValIdValue}
import compiler.lang.FormulasDsl.autoConvertIntToIConst
import compiler.lang.FormulasDsl.*
import compiler.lang.Types.IntRangeType
import compiler.lang.Types.IntRangeType.*
import compiler.lang.Types.PrimitiveType.IntType
import compiler.simplification.Simplifier
import compiler.smt.Solver
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.assertEquals
import org.junit.Test

class AbstractInterpreterTests {

  private val dummyScope = Scope.root(GlobalValuesContext())

  private def mkVal(id: String): ValIdValue =
    ValIdValue(NormalFunOrVarId(id), dummyScope, 0)

  private val a = mkVal("a")
  private val b = mkVal("b")

  private val `[0,10]` = IntRangeType(0, 10)
  private val `[-5,5]` = IntRangeType(-5, 5)
  private val `[-5,15]` = IntRangeType(-5, 15)
  private val `[-10,20]` = IntRangeType(-10, 20)
  private val `[-50,50]` = IntRangeType(-50, 50)
  private val `[-100,100]` = IntRangeType(-100, 100)
  private val `[a,b]` = IntRangeType(a, b)
  private val `[1,a]` = IntRangeType(1, a)
  private val `[1,a+10]` = IntRangeType(1, a + 10)
  private val `[-9,a]` = IntRangeType(-9, a)
  private val `[-10a,20a]` = IntRangeType(-10 * a, 20 * a)
  private val `[-10a+1,21a]` = IntRangeType(-10 * a + 1, 21 * a)
  private val `[-11a,20a-1]` = IntRangeType(-11 * a, 20 * a - 1)
  private val `[0,a-1]` = IntRangeType(0, a - 1)
  private val `[-a+1,0]` = IntRangeType(-a + 1, 0)
  private val `[-5b,15b]` = IntRangeType(-5*b, 15*b)

  @Test def typePlusTypeTest(): Unit = usingFreshInterpreter { (absInt, _) =>
    import absInt.typePlusType
    assertEquals(Some(`[-5,15]`), typePlusType(`[0,10]`, `[-5,5]`))
    assertEquals(Some(`[1,a+10]`), typePlusType(`[0,10]`, `[1,a]`))
    assertEquals(Some(nonNegative), typePlusType(nonNegative, nonNegative))
    assertEquals(Some(IntType), typePlusType(nonNegative, nonPositive))
    assertEquals(Some(`[-10a+1,21a]`), typePlusType(`[-10a,20a]`, `[1,a]`))
  }

  @Test def typeMinusTypeTest(): Unit = usingFreshInterpreter { (absInt, _) =>
    import absInt.typeMinusType
    assertEquals(Some(`[-10,20]`), typeMinusType(`[-5,15]`, `[-5,5]`))
    assertEquals(Some(`[-9,a]`), typeMinusType(`[1,a]`, `[0,10]`))
    assertEquals(Some(nonNegative), typeMinusType(nonNegative, nonPositive))
    assertEquals(Some(IntType), typeMinusType(nonNegative, nonNegative))
    assertEquals(Some(`[-11a,20a-1]`), typeMinusType(`[-10a,20a]`, `[1,a]`))
  }

  @Test def typeTimesTypeTest(): Unit = usingFreshInterpreter { (absInt, solver) =>
    import absInt.typeTimesType
    assertEquals(Some(nonNegative), typeTimesType(nonNegative, nonNegative))
    assertEquals(Some(nonNegative), typeTimesType(nonPositive, nonPositive))
    assertEquals(Some(nonPositive), typeTimesType(nonNegative, nonPositive))
    assertEquals(Some(nonPositive), typeTimesType(nonPositive, nonNegative))
    assertEquals(Some(`[-50,50]`), typeTimesType(`[0,10]`, `[-5,5]`))
    assertEquals(Some(`[-50,50]`), typeTimesType(`[-5,5]`, `[0,10]`))
    assertEquals(Some(`[-100,100]`), typeTimesType(`[-5,5]`, `[-10,20]`))
    assertEquals(Some(`[-10a,20a]`), typeTimesType(`[1,a]`, `[-10,20]`))
    assertEquals(Some(IntType), typeTimesType(`[-5,15]`, `[a,b]`))
    solver.onNewFrame {
      solver.assertLeq(0, a)
      assertEquals(Some(`[-5b,15b]`), typeTimesType(`[-5,15]`, `[a,b]`))
    }
  }

  @Test def typeDivTypeTest(): Unit = usingFreshInterpreter { (absInt, _) =>
    import absInt.typeDivType
    assertEquals(Some(nonNegative), typeDivType(nonNegative, strictlyPositive))
    assertEquals(Some(nonNegative), typeDivType(nonPositive, strictlyNegative))
    assertEquals(Some(nonPositive), typeDivType(nonNegative, strictlyNegative))
    assertEquals(Some(nonPositive), typeDivType(nonPositive, strictlyPositive))
    assertEquals(Some(IntType), typeDivType(nonNegative, nonNegative))
    assertEquals(Some(nonNegative), typeDivType(`[0,10]`, `[1,a]`))
    assertEquals(Some(IntType), typeDivType(`[-5,5]`, `[1,a]`))
  }

  @Test def typeModuloTypeTest(): Unit = usingFreshInterpreter { (absInt, solver) =>
    import absInt.typeModuloType
    assertEquals(Some(nonNegative), typeModuloType(nonNegative, strictlyPositive))
    assertEquals(Some(nonPositive), typeModuloType(nonPositive, strictlyNegative))
    assertEquals(Some(nonNegative), typeModuloType(nonNegative, strictlyNegative))
    assertEquals(Some(nonPositive), typeModuloType(nonPositive, strictlyPositive))
    assertEquals(Some(IntType), typeModuloType(nonNegative, nonNegative))
    assertEquals(Some(IntType), typeModuloType(`[a,b]`, `[1,a]`))
    solver.onNewFrame {
      solver.assertLeq(0, a)
      assertEquals(Some(`[0,a-1]`), typeModuloType(`[a,b]`, `[1,a]`))
    }
    solver.onNewFrame {
      solver.assertLt(b, 0)
      assertEquals(Some(`[-a+1,0]`), typeModuloType(`[a,b]`, `[1,a]`))
    }
  }

  private def usingFreshInterpreter(action: (AbstractInterpreter, Solver) => Unit): Unit = Solver.usingFreshSolver { solver =>
    val simplifier = Simplifier(solver)
    val interpreter = AbstractInterpreter(solver, simplifier)
    action(interpreter, solver)
  }

}
