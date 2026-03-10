package compiler.egraphs

import compiler.egraphs.rewrites.EqualitySaturationRewriteRules.allRules
import compiler.identifiers.{NormalFunOrVarId, NormalTypeId}
import compiler.irs.SSA.{FieldResolutionTarget, Scope}
import compiler.lang.Formulas.*
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.lang.{Field, RecordSignature}
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.{assertEquals, assertFalse, assertTrue}
import org.junit.Test

import scala.collection.SeqMap


class EGraphTests {

  private given EClassId.Generator = new EClassId.Generator

  private val scope = Scope.root(GlobalValuesContext())

  private def newVal(id: String): IdValue =
    scope.newVal(NormalFunOrVarId(id))

  private val fid = NormalFunOrVarId("f")
  private val gid = NormalFunOrVarId("g")

  private val dummySig = RecordSignature(NormalTypeId("Dummy"), List.empty, SeqMap(
    fid -> Field.StableField(fid, NothingType, newVal("f")),
    gid -> Field.StableField(gid, NothingType, newVal("g"))
  ), List.empty, scope, None)

  extension (l: Formula) {
    def f =
      Select(l, FieldResolutionTarget.Resolved(dummySig, fid))
    def g =
      Select(l, FieldResolutionTarget.Resolved(dummySig, gid))

    infix def +(r: Formula) = Plus(l, r)
    infix def -(r: Formula) = Plus(l, Neg(r))
    infix def *(r: Formula) = Times(l, r)
    infix def /(r: Formula) = DivBy(l, r)

    def unary_- = Neg(l)
  }

  private given Conversion[Int, Formula] = IntConst(_)

  @Test
  def transitiveEqualityTest(): Unit = {

    val x = newVal("x")
    val y = newVal("y")
    val z = newVal("z")
    val t = newVal("t")

    val eg = MutEGraphWrapper.newEmpty
    eg.assertEquality(x, y)
    eg.assertEquality(y, z)

    // given
    assertTrue(eg.equalityQueryNoSaturation(x, y))
    assertTrue(eg.equalityQueryNoSaturation(y, z))

    // transitivity
    assertTrue(eg.equalityQueryNoSaturation(x, z))

    // not equal
    assertFalse(eg.equalityQueryNoSaturation(x, t))
    assertFalse(eg.equalityQueryNoSaturation(y, t))
    assertFalse(eg.equalityQueryNoSaturation(z, t))
  }

  @Test
  def simpleCongruenceTest(): Unit = {

    val t = newVal("t")
    val u = newVal("u")
    val x = newVal("x")
    val y = newVal("y")
    val z = newVal("z")

    val eg = MutEGraphWrapper.newEmpty
    eg.assertEquality(t, u)
    eg.assertEquality(x, y)
    eg.assertEquality(x, z)

    // basics
    assertTrue(eg.equalityQueryNoSaturation(t, u))
    assertTrue(eg.equalityQueryNoSaturation(x, y))
    assertFalse(eg.equalityQueryNoSaturation(t, x))
    assertFalse(eg.equalityQueryNoSaturation(t, y))
    assertFalse(eg.equalityQueryNoSaturation(u, x))
    assertFalse(eg.equalityQueryNoSaturation(u, y))

    // congruences
    assertTrue(eg.equalityQueryNoSaturation(t.f, u.f))
    assertTrue(eg.equalityQueryNoSaturation(x.f, y.f))
    assertFalse(eg.equalityQueryNoSaturation(x.f, y.g))
    assertFalse(eg.equalityQueryNoSaturation(t.f, x.f))
    assertFalse(eg.equalityQueryNoSaturation(u.g, z.g))

    // transitivity + congruence
    assertTrue(eg.equalityQueryNoSaturation(y.g, z.g))
  }

  @Test
  def equalitySaturationAssocCommutTest(): Unit = {

    val r = newVal("r")
    val s = newVal("s")
    val t = newVal("t")
    val u = newVal("u")
    val x = newVal("x")
    val y = newVal("y")
    val z = newVal("z")

    val eg = MutEGraphWrapper.newEmpty
    eg.assertEquality(t, u)
    eg.assertEquality(x, y)
    eg.assertEquality(x, z)

    val maxSteps = 500L

    assertTrue(eg.equalityQueryAfterSaturation(s + t, t + s, allRules, maxSteps))
    assertTrue(eg.equalityQueryAfterSaturation(s + t, u + s, allRules, maxSteps))
    assertFalse(eg.equalityQueryAfterSaturation(s + t, t + x, allRules, maxSteps))
    assertTrue(eg.equalityQueryAfterSaturation((s + t) + y, s + (t + z), allRules, maxSteps))
    assertFalse(eg.equalityQueryAfterSaturation((s + t) + x, r + (t + x), allRules, maxSteps))

    assertTrue(eg.equalityQueryAfterSaturation(r + s + t + x, t + r + x + s, allRules, maxSteps))
  }

  @Test
  def simplificationTest(): Unit = {

    def simplify(f: Formula, maxSteps: Long): Formula = {
      val (ig, fClId) = EGraph.empty.withFormulaAbsorbed(f)
      ig.toSimplifiedFormula(fClId, allRules, maxSteps).get
    }

    val x = newVal("x")
    val t = newVal("t")

    assertEquals(12: Formula, simplify(-(-(12: Formula)), 100))
    assertEquals(x, simplify(x + 0, 50))
    assertEquals(x + t, simplify(x * 1 + 1 * t, 100))
    assertEquals(3 * x, simplify(2 * x + x, 100))
    assertEquals(74: Formula, simplify(x / x * 2 + 11 * t - 11 * t + 8 * 9, 200))
    assertEquals(-2 * x + 3 * t, simplify(3 * x + 2 * t - 5 * x + t, 50_000))
  }

  @Test def costsOrderingTest(): Unit = {

    val x = newVal("x")
    val y = newVal("y")
    val z = newVal("z")

    val mg = MutEGraphWrapper.newEmpty

    def assertCostLt(l: Formula, r: Formula): Unit = {
      val lid = mg.absorbFormula(l)
      val rid = mg.absorbFormula(r)
      val costCache = mg.getCurrentState.costCache
      assertTrue(costCache.minCostOf(lid) < costCache.minCostOf(rid))
    }

    assertCostLt(42, x)
    assertCostLt(42, (30: Formula) + 12)
    assertCostLt(x, y + z)
    assertCostLt(2 * x, x + x)
    assertCostLt(2 * x, x * 2)
    assertCostLt(3 * x + y, x + y + 2 * x)
  }

  @Test def simpleInequalitiesTest(): Unit = {

    val r = newVal("r")
    val s = newVal("s")
    val t = newVal("t")
    val u = newVal("u")
    val x = newVal("x")
    val y = newVal("y")
    val z = newVal("z")

    // s <= r == x <= y == t
    val eg = MutEGraphWrapper.newEmpty
    eg.assertEquality(r, x)
    eg.assertLessOrEq(s, r)
    eg.assertEquality(y, t)
    eg.assertLessOrEq(x, y)

    assertTrue(eg.lessOrEqQueryNoSearch(x, x))
    assertTrue(eg.lessOrEqQueryNoSearch(x, y))
    assertTrue(eg.lessOrEqQueryNoSearch(s, x))
    assertTrue(eg.lessOrEqQueryNoSearch(r, y))
    assertTrue(eg.lessOrEqQueryNoSearch(s, t))

    assertFalse(eg.lessOrEqQueryNoSearch(x, z))
    assertFalse(eg.lessOrEqQueryNoSearch(r, s))
    assertFalse(eg.lessOrEqQueryNoSearch(t, r))
    assertFalse(eg.lessOrEqQueryNoSearch(u, y))

  }

  @Test def complexInequalitiesTest(): Unit = {

    val x = newVal("x")
    val y = newVal("y")
    val z = newVal("z")

    val eg = MutEGraphWrapper.newEmpty
    eg.assertLessOrEq(2 * x * y + 1, y - 2)
    eg.assertLessOrEq(y + 1, 3 * x + 4 * y)

    val maxSteps = 10_000

    assertTrue(eg.lessOrEqQueryAfterSearch(2 * x * y - 5, 3 * x + 4 * y + 1, allRules, maxSteps))
    assertFalse(eg.lessOrEqQueryAfterSearch(2 * x * y + 1, 3 * x + 4 * y - 5, allRules, maxSteps))

  }

}
