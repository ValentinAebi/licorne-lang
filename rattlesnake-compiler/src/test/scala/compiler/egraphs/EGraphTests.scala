package compiler.egraphs

import compiler.identifiers.{NormalFunOrVarId, NormalTypeId}
import compiler.irs.SSA.{FieldResolutionTarget, Scope}
import compiler.lang.Formulas.{Formula, IdValue, Select}
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.lang.{Field, RecordSignature}
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.{assertFalse, assertTrue}
import org.junit.Test

import scala.collection.SeqMap


class EGraphTests {

  // TODO test with congruence

  @Test
  def transitiveEqualityTest(): Unit = {
    given EClassId.Generator = new EClassId.Generator

    val scope = Scope.root(GlobalValuesContext())
    
    def newVal(id: String): IdValue =
      scope.newVal(NormalFunOrVarId(id))
    
    val x = newVal("x")
    val y = newVal("y")
    val z = newVal("z")
    val t = newVal("t")

    val eg = EGraph.newEmpty
      .withEquality(x, y)
      .withEquality(y, z)

    // given
    assertTrue(eg.areEqual(x, y))
    assertTrue(eg.areEqual(y, z))
    
    // transitivity
    assertTrue(eg.areEqual(x, z))
    
    // not equal
    assertFalse(eg.areEqual(x, t))
    assertFalse(eg.areEqual(y, t))
    assertFalse(eg.areEqual(z, t))
  }
  
  @Test
  def simpleCongruenceTest(): Unit = {
    given EClassId.Generator = new EClassId.Generator

    val scope = Scope.root(GlobalValuesContext())

    def newVal(id: String): IdValue =
      scope.newVal(NormalFunOrVarId(id))

    val t = newVal("t")
    val u = newVal("u")
    val x = newVal("x")
    val y = newVal("y")
    val z = newVal("z")
    
    val fid = NormalFunOrVarId("f")
    val gid = NormalFunOrVarId("g")
    
    val dummySig = RecordSignature(NormalTypeId("Dummy"), List.empty, SeqMap(
      fid -> Field.StableField(fid, NothingType, newVal("f")),
      gid -> Field.StableField(gid, NothingType, newVal("g"))
    ), List.empty, scope, None)
    
    extension (owner: Formula) {
      def f =
        Select(owner, FieldResolutionTarget.Resolved(dummySig, fid))
      def g =
        Select(owner, FieldResolutionTarget.Resolved(dummySig, gid))
    }
    
    val eg = EGraph.newEmpty
      .withEquality(t, u)
      .withEquality(x, y)
      .withEquality(x, z)
    
    // basics
    assertTrue(eg.areEqual(t, u))
    assertTrue(eg.areEqual(x, y))
    assertFalse(eg.areEqual(t, x))
    assertFalse(eg.areEqual(t, y))
    assertFalse(eg.areEqual(u, x))
    assertFalse(eg.areEqual(u, y))
    
    // congruences
    assertTrue(eg.areEqual(t.f, u.f))
    assertTrue(eg.areEqual(x.f, y.f))
    assertFalse(eg.areEqual(x.f, y.g))
    assertFalse(eg.areEqual(t.f, x.f))
    assertFalse(eg.areEqual(u.g, z.g))

    // transitivity + congruence
    assertTrue(eg.areEqual(y.g, z.g))
  }

}
