package compiler.simplification

import compiler.datastructures.Graph
import compiler.identifiers.NormalFunOrVarId
import compiler.irs.ssa.SSA.Scope
import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.FormulasDsl.*
import compiler.irs.ssa.FormulasDsl.autoConvertIntToIConst
import compiler.lang.Types.IntRangeType
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reasoning.{ArithIntMode, Reasoning, Simplifier, Solver}
import compiler.typing.contexts.*
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert.assertEquals
import org.junit.{Assert, Test}

import scala.collection.mutable
import scala.collection.immutable.SeqMap

final class SimplificationTests {
  
  private given TypeParamsContext = TypeParamsContext.empty

  private val proxyStore = ProxyStore()
  private val dummyScope = Scope.root(GlobalValuesContext(proxyStore))

  private def mkVal(id: String): ValIdValue =
    ValIdValue(NormalFunOrVarId(id), dummyScope, 0, None)

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
    assertEquals(6*a + 5*b + 24, simplifier.simplifyInt(a + 5*b - 3*a - 2 + 25 + 8*a + 1))
    // @formatter:on
  }

  @Test def simplifyLinearFormulaTest2(): Unit = usingFreshSimplifier { (simplifier, _) =>
    // @formatter:off
    assertEquals(9*a - 1, simplifier.simplifyInt(2*4*a + a - 1))
    // @formatter:on
  }

  @Test def simplifyLinearFormulaTest3(): Unit = usingFreshSimplifier { (simplifier, _) =>
    // @formatter:off
    assertEquals(a, simplifier.simplifyInt(2*a + 9*b - a - 5*b - 1 - 4*b + 1))
    assertEquals(IntConst(0), simplifier.simplifyInt(2*a + 9*b - a - 5*b - 1 - 4*b + 1 - a))
    // @formatter:on
  }

  private def usingFreshSimplifier(action: (Simplifier, Solver) => Unit): Unit = {
    given CompilationStep = TypeChecking

    val er = ErrorReporter(_ => fail(), _ => fail())
    val globalValuesCtx = GlobalValuesContext(proxyStore)
    val program = Program(globalValuesCtx, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, Seq.empty)
    val dealiasingCtx = DealiasingContext(Map.empty)
    val resolutionCtx = ResolutionContext(program, er)
    Reasoning.usingFreshReasoningToolkit(ArithIntMode, dealiasingCtx, resolutionCtx, proxyStore, globalValuesCtx, None) { solver =>
      SubtypingContext(Graph.empty, mutable.SeqMap.empty, dealiasingCtx, resolutionCtx, solver, proxyStore, globalValuesCtx, er, None)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      action(simplifier, solver)
    }
  }

  private def fail(): Nothing = {
    Assert.fail()
    throw AssertionError() // cannot happen
  }

}
