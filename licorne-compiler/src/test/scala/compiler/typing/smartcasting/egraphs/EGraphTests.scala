package compiler.typing.smartcasting.egraphs

import compiler.datastructures.Graph
import compiler.identifiers.NormalFunOrVarId
import compiler.irs.ircorne.Formulas.{Formula, FunCall, Select, ValIdValue}
import compiler.irs.ircorne.FormulasDsl.{autoConvertIntToIConst, *}
import compiler.irs.ircorne.{FieldResolutionTarget, InvocationTarget}
import compiler.irs.ircorne.IRcorne.Scope
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reasoning.{ArithIntMode, Reasoning, Simplifier}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeParamsContext, TypeVariablesContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.{assertFalse, assertTrue}
import org.junit.Test

import scala.collection.immutable.SeqMap
import scala.collection.mutable

class EGraphTests {

  private given TypeParamsContext = TypeParamsContext.empty

  private given CompilationStep = TypeChecking

  private val er = ErrorReporter(_ => fail(), _ => fail())

  private given proxyStore: ProxyStore = ProxyStore()

  private val globalValuesContext = GlobalValuesContext(proxyStore)
  private val dummyScope = Scope.root(globalValuesContext)
  private val program = Program(globalValuesContext, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty)
  private val dealiasingCtx = DealiasingContext(Map.empty)

  private given resolCtx: ResolutionContext = ResolutionContext(program, er)

  @Test
  def commutativityTest(): Unit = {
    val x = newValue("x")
    val y = newValue("y")

    val eg = EGraph.newEmpty
    assertTrue(eg.areEqual(x + y, y + x))
  }

  @Test def transitivityTest(): Unit = usingSimplifier {
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

  @Test def congruenceTest1(): Unit = usingSimplifier {
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

  @Test def congurenceTest2(): Unit = usingSimplifier {
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


  private def newValue(name: String) = ValIdValue(NormalFunOrVarId(name), dummyScope, 0, None)

  extension (f: Formula) private def sel(fldName: String): Formula = {
    val fldResolTarget = new FieldResolutionTarget(NormalFunOrVarId(fldName))
    Select(f, fldResolTarget)
  }

  extension (rec: Formula) private def call(funName: String, args: Formula*): Formula = {
    val invkTarget = InvocationTarget(NormalFunOrVarId(funName))
    FunCall(rec, invkTarget, List.empty, args.toList)
  }

  private def usingSimplifier(action: Simplifier ?=> Unit): Unit = {
    Reasoning.usingFreshReasoningToolkit(ArithIntMode, dealiasingCtx, resolCtx, proxyStore, globalValuesContext, None) { solver =>
      SubtypingContext(Graph.empty, mutable.SeqMap.empty, dealiasingCtx, resolCtx, solver, proxyStore, globalValuesContext, er, None)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      action(using simplifier)
    }
  }

  private def fail(): Nothing = {
    org.junit.Assert.fail()
    throw AssertionError("cannot happen")
  }

}
