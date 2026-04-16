package compiler.typing.smartcasting.egraphs

import compiler.identifiers.NormalFunOrVarId
import compiler.irs.SSA.{FieldResolutionTarget, InvocationTarget, Scope}
import compiler.lang.Formulas.{Call, Formula, IntConst, Select, ValIdValue}
import compiler.lang.FormulasDsl.{autoConvertIntToIConst, *}
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.{assertFalse, assertTrue}
import org.junit.Test

class EGraphTests {

  @Test
  def commutativityTest(): Unit = {
    val x = newValue("x")
    val y = newValue("y")

    val eg = EGraph.newEmpty
    assertTrue(eg.areEqual(x + y, y + x))
  }

  @Test def transitivityTest(): Unit = {
    val x = newValue("x")
    val y = newValue("y")
    val z = newValue("z")

    val eg = EGraph.newEmpty
    assertFalse(eg.areEqual(x, y))
    assertFalse(eg.areEqual(x, z))
    assertFalse(eg.areEqual(y, z))
    eg.merge(x, y)
    assertTrue(eg.areEqual(x, y))
    assertFalse(eg.areEqual(x, z))
    assertFalse(eg.areEqual(y, z))
    eg.merge(y, z)
    assertTrue(eg.areEqual(x, y))
    assertTrue(eg.areEqual(x, z))
    assertTrue(eg.areEqual(y, z))
  }

  @Test def congruenceTest1(): Unit = {
    val x = newValue("x")
    val y = newValue("y")
    val z = newValue("z")

    val eg = EGraph.newEmpty
    assertFalse(eg.areEqual(x.sel("f"), y.sel("f")))
    eg.merge(x, y)
    assertTrue(eg.areEqual(x.sel("f"), y.sel("f")))

    // also test absence of "reverse congruence"
    eg.merge(x.sel("f"), z.sel("f"))
    assertTrue(eg.areEqual(y.sel("f"), z.sel("f")))
    assertFalse(eg.areEqual(y, z))
  }

  @Test def congurenceTest2(): Unit = {
    val a = newValue("a")
    val b = newValue("b")
    val c = newValue("c")
    val x = newValue("x")
    val y = newValue("y")
    val z = newValue("z")

    val eg = EGraph.newEmpty
    assertFalse(eg.areEqual(a.call("foo", b, c), x.call("foo", y, z)))
    eg.merge(a, x)
    eg.merge(y, b)
    eg.merge(c, z)
    assertTrue(eg.areEqual(a.call("foo", b, c), x.call("foo", y, z)))
    assertTrue(eg.areEqual(a.call("foo", b + 1, c - 2), x.call("foo", 1 + y, z - 2)))
    assertFalse(eg.areEqual(a.call("foo", b + 1, c - 2), x.call("foo", y + 2, z - 2)))
  }

  private val dummyScope = Scope.root(GlobalValuesContext())

  private def newValue(name: String) = ValIdValue(NormalFunOrVarId(name), dummyScope, 0, None)

  extension (f: Formula) private def sel(fldName: String): Formula = {
    val fldResolTarget = new FieldResolutionTarget(NormalFunOrVarId(fldName))
    Select(f, fldResolTarget)
  }

  extension (rec: Formula) private def call(funName: String, args: Formula*): Formula = {
    val invkTarget = InvocationTarget(NormalFunOrVarId(funName))
    Call(rec, invkTarget, List.empty, args.toList)
  }

}
