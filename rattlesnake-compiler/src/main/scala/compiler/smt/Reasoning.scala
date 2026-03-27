package compiler.smt

import compiler.typing.contexts.SubtypingContext
import io.ksmt.KContext
import io.ksmt.solver.z3.KZ3Solver

import scala.util.Using

object Reasoning {

  def usingFreshReasoningToolkit[T](mkSubtypingCtx: Solver => SubtypingContext)
                                   (f: (Solver, SubtypingContext, Simplifier, AbstractInterpreter) => T): T =
    usingFreshSolver { solver =>
      val subtypingCtx = mkSubtypingCtx(solver)
      val simplifier = Simplifier(subtypingCtx, solver)
      val absInt = AbstractInterpreter(solver, simplifier)
      f(solver, subtypingCtx, simplifier, absInt)
    }

  def usingFreshSolver[T](f: Solver => T): T = Using(KContext()) { kCtx =>
    Using(KZ3Solver(kCtx)) { kZ3Solver =>
      val solver = Solver(kCtx, kZ3Solver)
      f(solver)
    }.get
  }.get

}
