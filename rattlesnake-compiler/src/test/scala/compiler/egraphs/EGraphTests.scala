package compiler.egraphs

import compiler.egraphs.rewrites.{AssociativityDirection1, AssociativityDirection2, Commutativity}
import compiler.identifiers.{NormalFunOrVarId, NormalTypeId}
import compiler.irs.SSA.{FieldResolutionTarget, Scope}
import compiler.lang.Formulas.*
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.lang.{Field, RecordSignature}
import compiler.util.SeqSet
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.{assertFalse, assertTrue}
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
  }

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

    val rules = SeqSet(
      Commutativity(EPlusNode(_, _)),
      AssociativityDirection1(EPlusNode(_, _)),
      AssociativityDirection2(EPlusNode(_, _)),
      Commutativity(ETimesNode(_, _)),
      AssociativityDirection1(ETimesNode(_, _)),
      AssociativityDirection2(ETimesNode(_, _)),
    )

    val timeout = 10_000L

    assertTrue(eg.equalityQueryAfterSaturation(s + t, t + s, rules, timeout))
    assertTrue(eg.equalityQueryAfterSaturation(s + t, u + s, rules, timeout))
    assertFalse(eg.equalityQueryAfterSaturation(s + t, t + x, rules, timeout))
    assertTrue(eg.equalityQueryAfterSaturation((s + t) + y, s + (t + z), rules, timeout))
    assertFalse(eg.equalityQueryAfterSaturation((s + t) + x, r + (t + x), rules, timeout))

    assertTrue(eg.equalityQueryAfterSaturation(r + s + t + x, t + r + x + s, rules, timeout))
  }

}
