package compiler.typing.phases

import compiler.irs.SSA.*
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.smt.Solver
import io.ksmt.KContext
import io.ksmt.solver.z3.KZ3Solver

import scala.util.Using

final class MonotonicityAnalysis extends CompilerStep[Program, Program] {

  override def apply(program: Program): Program = {
    for (loop <- program.loops) {
      inferInvariants(loop)
    }
    program
  }

  private def inferInvariants(loop: Loop): Unit = Solver.usingFreshSolver { solver =>
    for {
      loopVarData <- loop.variables
      recurrence <- loopVarData.recurrenceOpt
    } do {
      recurrence.computeMonotonicity(solver)
    }
  }

}
