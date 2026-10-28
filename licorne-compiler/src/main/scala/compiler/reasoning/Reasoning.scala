package compiler.reasoning

import compiler.reasoning.Solver.TimeoutConfig
import compiler.reporting.Errors.ErrorReporter
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext
import io.ksmt.KContext
import io.ksmt.solver.z3.KZ3Solver

import scala.util.Using

object Reasoning {

  def usingFreshReasoningToolkit[T](ihm: IntHandlingMode[?], timeoutConfig: TimeoutConfig, dealiasingCtx: DealiasingContext, resolutionCtx: ResolutionContext, proxyStore: ProxyStore, globalValuesContext: GlobalValuesContext, counterExBoxOpt: Option[CounterexampleBox], er: ErrorReporter)
                                   (mkSubtypingCtx: Solver => SubtypingContext)
                                   (f: (Solver, SubtypingContext, TypeSimplifier, MeetJoinComputer, AbstractInterpreter) => T): T =
    usingFreshSolver(ihm, timeoutConfig, dealiasingCtx, resolutionCtx, globalValuesContext, proxyStore, counterExBoxOpt, er) { solver =>
      val subtypingCtx = mkSubtypingCtx(solver)
      val meetJoin = MeetJoinComputer(dealiasingCtx, resolutionCtx, subtypingCtx, solver, proxyStore, globalValuesContext)
      val simplifier = meetJoin.simplifier
      val absInt = AbstractInterpreter(solver, simplifier, meetJoin, globalValuesContext)
      f(solver, subtypingCtx, simplifier, meetJoin, absInt)
    }

  def usingFreshSolver[T](ihm: IntHandlingMode[?], timeoutConfig: TimeoutConfig, dealiasingCtx: DealiasingContext, resolCtx: ResolutionContext, globalValsCtx: GlobalValuesContext, proxyStore: ProxyStore, counterExBoxOpt: Option[CounterexampleBox], er: ErrorReporter)(f: Solver => T): T = Using(KContext()) { kCtx =>
    Using(KZ3Solver(kCtx)) { kZ3Solver =>
      val converter = FormulasConverter(kCtx, ihm, dealiasingCtx, resolCtx, globalValsCtx, proxyStore, counterExBoxOpt)
      val solver = Z3Solver(kCtx, kZ3Solver, ihm, timeoutConfig, converter, counterExBoxOpt, er)
      f(solver)
    }.get
  }.get

}
