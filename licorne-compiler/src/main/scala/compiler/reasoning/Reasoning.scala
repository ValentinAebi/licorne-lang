package compiler.reasoning

import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext
import io.ksmt.KContext
import io.ksmt.solver.z3.KZ3Solver

import scala.util.Using

object Reasoning {

  def usingFreshReasoningToolkit[T](ihm: IntHandlingMode[?], dealiasingCtx: DealiasingContext, resolutionCtx: ResolutionContext, proxyStore: ProxyStore, globalValuesContext: GlobalValuesContext, counterExBoxOpt: Option[CounterexampleBox])
                                   (mkSubtypingCtx: Solver => SubtypingContext)
                                   (f: (Solver, SubtypingContext, Simplifier, MeetJoinComputer, AbstractInterpreter) => T): T =
    usingFreshSolver(ihm, dealiasingCtx, resolutionCtx, globalValuesContext, proxyStore, counterExBoxOpt) { solver =>
      val subtypingCtx = mkSubtypingCtx(solver)
      val meetJoin = MeetJoinComputer(dealiasingCtx, resolutionCtx, subtypingCtx, solver, globalValuesContext)
      val simplifier = meetJoin.simplifier
      val absInt = AbstractInterpreter(solver, simplifier, globalValuesContext)
      f(solver, subtypingCtx, simplifier, meetJoin, absInt)
    }

  def usingFreshSolver[T](ihm: IntHandlingMode[?], dealiasingCtx: DealiasingContext, resolCtx: ResolutionContext, globalValsCtx: GlobalValuesContext, proxyStore: ProxyStore, counterExBoxOpt: Option[CounterexampleBox])(f: Solver => T): T = Using(KContext()) { kCtx =>
    Using(KZ3Solver(kCtx)) { kZ3Solver =>
      val converter = FormulasConverter(kCtx, ihm, dealiasingCtx, resolCtx, globalValsCtx, proxyStore, counterExBoxOpt)
      val solver = Z3Solver(kCtx, kZ3Solver, ihm, converter, counterExBoxOpt)
      f(solver)
    }.get
  }.get

}
