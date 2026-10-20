package compiler.reasoning

import compiler.identifiers.NormalFunOrVarId
import compiler.irs.ircorne.Formulas.{IdValue, ValIdValue}
import compiler.irs.ircorne.FormulasDsl.{autoConvertIntToIConst, *}
import compiler.irs.ircorne.IRcorne.Scope
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.{assertEquals, assertTrue}
import org.junit.Test

import java.util.concurrent.atomic.AtomicLong

class VariableEvolutionTests {

  private val idGen = AtomicLong()
  private val globalValsCtx = GlobalValuesContext(new ProxyStore)
  private val fakeScope = Scope.root(globalValsCtx)

  private def idVal(name: String): IdValue =
    ValIdValue(NormalFunOrVarId(name), fakeScope, idGen.incrementAndGet(), None)

  @Test def closedFormTest1(): Unit = {
    val i = idVal("i")
    val rec = VariableEvolution.computeFrom(1, i + 2, i)
    val idx = idVal("idx")
    val closedFormOpt = rec.asClosedForm(idx)
    assertTrue(closedFormOpt.isDefined)
    assertEquals(2 * idx + 1, closedFormOpt.get)
  }

  @Test def closedFormTest2(): Unit = {
    val x = idVal("x")
    val a = idVal("a")
    val b = idVal("b")
    val rec = VariableEvolution.computeFrom(a, 1 + x + b + 2 * a, x)
    val idx = idVal("idx")
    val closedFormOpt = rec.asClosedForm(idx)
    assertTrue(closedFormOpt.isDefined)
    assertEquals(a + (b + 2 * a + 1) * idx, closedFormOpt.get)
  }

  @Test def closedFormTest3(): Unit = {
    val i = idVal("i")
    val rec = VariableEvolution.computeFrom(2, i + 2, i)
    val idx = idVal("idx")
    val closedFormOpt = rec.asClosedForm(idx)
    assertTrue(closedFormOpt.isDefined)
    assertEquals(2*idx + 2, closedFormOpt.get)
  }

}
