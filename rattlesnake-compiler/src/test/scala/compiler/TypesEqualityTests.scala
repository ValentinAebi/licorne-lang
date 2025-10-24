package compiler

import identifiers.{NormalFunOrVarId, NormalTypeId}
import lang.Capturables.IdPath
import lang.CaptureDescriptors.CaptureSet
import lang.Types.PrimitiveTypeShape.{BoolType, DoubleType, IntType}
import lang.Types.{ArrayTypeShape, NamedTypeShape, Type}
import org.junit.Assert.{assertTrue, fail}
import org.junit.Test

class TypesEqualityTests {

  @Test
  def equalityTests(): Unit = {
    val namedA = NamedTypeShape(NormalTypeId("A"))
    val namedACapEmpty = NamedTypeShape(NormalTypeId("A")) ^ CaptureSet.empty
    val namedACapX = NamedTypeShape(NormalTypeId("A")) ^ CaptureSet(IdPath(NormalFunOrVarId("x")))
    val namedACapXDotFoo = NamedTypeShape(NormalTypeId("A")) ^ CaptureSet(IdPath(NormalFunOrVarId("x")).dot(NormalFunOrVarId("foo")))
    assertTrue(namedA == namedACapEmpty)
    assertTrue(namedA != namedACapX)
    assertTrue(namedA != namedACapXDotFoo)
    assertTrue(namedACapEmpty == namedA)
    assertTrue(namedACapEmpty != namedACapX)
    assertTrue(namedACapEmpty != namedACapXDotFoo)
    assertTrue(namedACapX != namedA)
    assertTrue(namedACapX != namedACapEmpty)
    assertTrue(namedACapX != namedACapXDotFoo)
    assertTrue(namedACapXDotFoo != namedA)
    assertTrue(namedACapXDotFoo != namedACapEmpty)
    assertTrue(namedACapXDotFoo != namedACapX)
    val types = Seq(
      IntType,
      DoubleType,
      BoolType,
      namedA,
      NamedTypeShape(NormalTypeId("A")),
      namedACapEmpty,
      namedACapX,
      namedACapXDotFoo,
      NamedTypeShape(NormalTypeId("A")) ^ CaptureSet(IdPath(NormalFunOrVarId("x"))),
      NamedTypeShape(NormalTypeId("B")),
      ArrayTypeShape(IntType),
      ArrayTypeShape(IntType),
      ArrayTypeShape(IntType) ^ CaptureSet.empty,
      ArrayTypeShape(IntType) ^ CaptureSet.singletonOfRoot,
      ArrayTypeShape(DoubleType)
    )
    for t1 <- types; t2 <- types do {
      val eq = t1 == t2
      val eqStr = t1.toString == t2.toString
      if (eq && !eqStr){
        fail(s"types are equal but not their string representations: $t1 <> $t2")
      }
      if (!eq && eqStr){
        fail(s"types are not equal but not their string representations are: $t1 <> $t2")
      }
    }
  }

}
