package compiler.smt

import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext
import io.ksmt.KContext
import io.ksmt.solver.z3.KZ3Solver

import scala.util.Using

object Reasoning {

  def usingFreshReasoningToolkit[T](dealiasingCtx: DealiasingContext, resolutionCtx: ResolutionContext, proxyStore: ProxyStore, globalValuesContext: GlobalValuesContext)
                                   (mkSubtypingCtx: Solver => SubtypingContext)
                                   (f: (Solver, SubtypingContext, Simplifier, MeetJoinComputer, AbstractInterpreter) => T): T =
    usingFreshSolver(dealiasingCtx, proxyStore) { solver =>
      val subtypingCtx = mkSubtypingCtx(solver)
      val meetJoin = MeetJoinComputer(dealiasingCtx, resolutionCtx, subtypingCtx, solver, globalValuesContext)
      val simplifier = meetJoin.simplifier
      val absInt = AbstractInterpreter(solver, simplifier)
      f(solver, subtypingCtx, simplifier, meetJoin, absInt)
    }

  def usingFreshSolver[T](dealiasingCtx: DealiasingContext, proxyStore: ProxyStore)(f: Solver => T): T = Using(KContext()) { kCtx =>
    Using(KZ3Solver(kCtx)) { kZ3Solver =>
      val solver = Solver(kCtx, kZ3Solver, dealiasingCtx, proxyStore)
      f(solver)
    }.get
  }.get

}
