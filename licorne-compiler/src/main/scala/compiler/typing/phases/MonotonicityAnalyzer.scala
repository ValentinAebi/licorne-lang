package compiler.typing.phases

import compiler.irs.ssa.SSA.*
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.smt.{IntHandlingMode, Reasoning, Solver}
import compiler.typing.contexts.DealiasingContext
import compiler.valproxies.ProxyStore
import io.ksmt.KContext
import io.ksmt.solver.z3.KZ3Solver

import scala.util.Using

final class MonotonicityAnalyzer(ihm: IntHandlingMode[?], proxyStore: ProxyStore) extends CompilerStep[Program, Program] {

  override def apply(program: Program): Program = {
    val dealiasingCtx = DealiasingContext(program.typeAliases)
    for (loop <- program.loops) {
      inferInvariants(loop, dealiasingCtx)
    }
    program
  }

  private def inferInvariants(loop: Loop, dealiasingCtx: DealiasingContext): Unit = Reasoning.usingFreshSolver(ihm, dealiasingCtx, proxyStore) { solver =>
    for {
      loopVarData <- loop.variables
      recurrence <- loopVarData.recurrenceOpt
    } do {
      recurrence.computeMonotonicity(solver)
    }
  }

}
