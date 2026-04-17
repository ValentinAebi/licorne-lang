package compiler.smt

import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext}
import io.ksmt.KContext
import io.ksmt.solver.z3.KZ3Solver

import scala.util.Using

object Reasoning {

  def usingFreshReasoningToolkit[T](dealiasingCtx: DealiasingContext, resolutionCtx: ResolutionContext)
                                   (mkSubtypingCtx: Solver => SubtypingContext)
                                   (f: (Solver, SubtypingContext, Simplifier, MeetJoinComputer, AbstractInterpreter) => T): T =
    usingFreshSolver { solver =>
      val subtypingCtx = mkSubtypingCtx(solver)
      val meetJoin = MeetJoinComputer(dealiasingCtx, resolutionCtx, subtypingCtx, solver)
      val simplifier = meetJoin.simplifier
      val absInt = AbstractInterpreter(solver, simplifier)
      f(solver, subtypingCtx, simplifier, meetJoin, absInt)
    }

  def usingFreshSolver[T](f: Solver => T): T = Using(KContext()) { kCtx =>
    Using(KZ3Solver(kCtx)) { kZ3Solver =>
      val solver = Solver(kCtx, kZ3Solver)
      f(solver)
    }.get
  }.get

}
