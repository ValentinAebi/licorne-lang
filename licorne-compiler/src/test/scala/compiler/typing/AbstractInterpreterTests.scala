package compiler.typing

import compiler.datastructures.Graph
import compiler.identifiers.NormalFunOrVarId
import compiler.irs.ssa.SSA.Scope
import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.FormulasDsl.{autoConvertIntToIConst, *}
import compiler.lang.Types.IntRangeType.*
import compiler.lang.Types.PrimitiveType.IntType
import compiler.lang.Types.IntRangeType
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.{AbstractInterpreter, ArithIntMode, Reasoning, Simplifier, Solver}
import compiler.typing.contexts.*
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext
import org.junit.Assert
import org.junit.Assert.assertEquals
import org.junit.Test

import scala.collection.mutable
import scala.collection.immutable.SeqMap

class AbstractInterpreterTests {

  private given TypeParamsContext = TypeParamsContext.empty

  private given globalValuesCtx: GlobalValuesContext = GlobalValuesContext(proxyStore)

  private val proxyStore = ProxyStore()
  private val abScope = Scope.root(globalValuesCtx)

  private val a: IdValue = abScope.newVal(NormalFunOrVarId("a"), None)
  private val b: IdValue = abScope.newVal(NormalFunOrVarId("b"), None)

  private val `[0,10]` = IntRangeType(0, 10)
  private val `[0/a,10]` = IntRangeType(0 / a, 10)
  private val `[-10,0]` = IntRangeType(-10, 0)
  private val `[-5,5]` = IntRangeType(-5, 5)
  private val `[-5,15]` = IntRangeType(-5, 15)
  private val `[-10,20]` = IntRangeType(-10, 20)
  private val `[-50,50]` = IntRangeType(-50, 50)
  private val `[-100,100]` = IntRangeType(-100, 100)
  private val `[a,b]` = IntRangeType(a, b)
  private val `[-b,-a]` = IntRangeType(-b, -a)
  private val `[1,a]` = IntRangeType(1, a)
  private val `[1,a+10]` = IntRangeType(1, a + 10)
  private val `[-9,a]` = IntRangeType(-9, a)
  private val `[-10a,20a]` = IntRangeType(-10 * a, 20 * a)
  private val `[-10a+1,21a]` = IntRangeType(-10 * a + 1, 21 * a)
  private val `[-11a,20a-1]` = IntRangeType(-11 * a, 20 * a - 1)
  private val `[0,a-1]` = IntRangeType(0, a - 1)
  private val `[-a+1,0]` = IntRangeType(-a + 1, 0)
  private val `[-5b,15b]` = IntRangeType(-5 * b, 15 * b)

  @Test def typePlusTypeTest(): Unit = usingFreshInterpreter { (absInt, _, _) =>
    import absInt.typePlusType
    assertEquals(Some(`[-5,15]`), typePlusType(`[0,10]`, `[-5,5]`))
    assertEquals(Some(`[1,a+10]`), typePlusType(`[0,10]`, `[1,a]`))
    assertEquals(Some(nonNegative), typePlusType(nonNegative, nonNegative))
    assertEquals(Some(IntType), typePlusType(nonNegative, nonPositive))
    assertEquals(Some(`[-10a+1,21a]`), typePlusType(`[-10a,20a]`, `[1,a]`))
  }

  @Test def typeMinusTypeTest(): Unit = usingFreshInterpreter { (absInt, _, _) =>
    import absInt.typeMinusType
    assertEquals(Some(`[-10,20]`), typeMinusType(`[-5,15]`, `[-5,5]`))
    assertEquals(Some(`[-9,a]`), typeMinusType(`[1,a]`, `[0,10]`))
    assertEquals(Some(nonNegative), typeMinusType(nonNegative, nonPositive))
    assertEquals(Some(IntType), typeMinusType(nonNegative, nonNegative))
    assertEquals(Some(`[-11a,20a-1]`), typeMinusType(`[-10a,20a]`, `[1,a]`))
  }

  @Test def typeTimesTypeTest(): Unit = usingFreshInterpreter { (absInt, _, solver) =>
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

  @Test def typeDivTypeTest(): Unit = usingFreshInterpreter { (absInt, _, _) =>
    import absInt.typeDivType
    assertEquals(Some(nonNegative), typeDivType(nonNegative, strictlyPositive))
    assertEquals(Some(nonNegative), typeDivType(nonPositive, strictlyNegative))
    assertEquals(Some(nonPositive), typeDivType(nonNegative, strictlyNegative))
    assertEquals(Some(nonPositive), typeDivType(nonPositive, strictlyPositive))
    assertEquals(Some(IntType), typeDivType(nonNegative, nonNegative))
    assertEquals(Some(`[0/a,10]`), typeDivType(`[0,10]`, `[1,a]`))
    assertEquals(Some(IntType), typeDivType(`[-5,5]`, `[1,a]`))
  }

  @Test def typeModuloTypeTest(): Unit = usingFreshInterpreter { (absInt, _, solver) =>
    val typeModuloType = absInt.typeModuloType(None)
    assertEquals(Some(nonNegative), typeModuloType(nonNegative, strictlyPositive))
    assertEquals(Some(nonPositive), typeModuloType(nonPositive, strictlyNegative))
    assertEquals(Some(nonNegative), typeModuloType(nonNegative, strictlyNegative))
    assertEquals(Some(nonPositive), typeModuloType(nonPositive, strictlyPositive))
    assertEquals(Some(nonNegative), typeModuloType(nonNegative, nonNegative))
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

  @Test def typeNegationTest(): Unit = usingFreshInterpreter { (absInt, _, _) =>
    import absInt.unaryNegType
    assertEquals(Some(`[-50,50]`), unaryNegType(`[-50,50]`))
    assertEquals(Some(`[-10,0]`), unaryNegType(`[0,10]`))
    assertEquals(Some(`[0,10]`), unaryNegType(`[-10,0]`))
    assertEquals(Some(`[-b,-a]`), unaryNegType(`[a,b]`))
    assertEquals(Some(`[a,b]`), unaryNegType(`[-b,-a]`))
    assertEquals(Some(`[-a+1,0]`), unaryNegType(`[0,a-1]`))
    assertEquals(Some(`[0,a-1]`), unaryNegType(`[-a+1,0]`))
  }

  @Test def interpretUnderAssumptionsTest(): Unit = usingFreshInterpreter { (absInt, simplifier, _) =>
    import absInt.interpretUnderAssumptions

    given CompilationStep = TypeChecking

    val program = Program(globalValuesCtx, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, Seq.empty)
    val er = ErrorReporter(_ => fail(), _ => fail())

    given ResolutionContext = ResolutionContext(program, er)

    given TypeParamsContext = TypeParamsContext(Map.empty)

    val xScope = Scope.nestedInsideNodeOpt(abScope, None)
    val x = xScope.newVal(NormalFunOrVarId("x"), None)

    assertEquals(Some(IntRangeType(1, 19)), interpretUnderAssumptions(2 * a - 1, Map(a -> IntRangeType(1, 10)), None))
    assertEquals(Some(IntRangeType.singleton((a + 1) * b)), interpretUnderAssumptions((a + 1) * b, Map(a -> IntRangeType(0, 5), b -> IntRangeType(0, a)), Some(x)))
    assertEquals(Some(IntType), interpretUnderAssumptions((a + 1) * x, Map(a -> IntRangeType(0, 5), x -> IntRangeType(0, a)), Some(b)))
    assertEquals(Some(IntRangeType(a, 2 * a)), interpretUnderAssumptions(a + x, Map(a -> IntRangeType(0, 5), x -> IntRangeType(0, a)), Some(b)))
    assertEquals(Some(`[1,a]`), interpretUnderAssumptions(x + 1, Map(x -> `[0,a-1]`), None))
  }

  private def usingFreshInterpreter(action: (AbstractInterpreter, Simplifier, Solver) => Unit): Unit = {
    given CompilationStep = TypeChecking

    val er = ErrorReporter(_ => fail(), _ => fail())
    val program = Program(globalValuesCtx, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, SeqMap.empty, Seq.empty)
    val dealiasingCtx = DealiasingContext(Map.empty)
    val resolutionCtx = ResolutionContext(program, er)

    Reasoning.usingFreshReasoningToolkit(ArithIntMode, dealiasingCtx, resolutionCtx, proxyStore, globalValuesCtx, None) { solver =>
      SubtypingContext(Graph.empty, mutable.SeqMap.empty, dealiasingCtx, resolutionCtx, solver, proxyStore, globalValuesCtx, er, None)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      action(absInt, simplifier, solver)
    }
  }

  private def fail(): Nothing = {
    Assert.fail()
    throw AssertionError() // cannot happen
  }

}
