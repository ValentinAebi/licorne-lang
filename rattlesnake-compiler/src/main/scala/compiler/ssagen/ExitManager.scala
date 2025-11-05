package compiler.ssagen

import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position

final class ExitManager {

  private enum ExitedStatus {
    case Active, HasExited, ReportedHasExited
  }
  
  private var exitedStatus = ExitedStatus.Active

  def markHasExited(): Unit = {
    if (exitedStatus != ExitedStatus.Active) {
      throw IllegalStateException()
    }
    exitedStatus = ExitedStatus.HasExited
  }

  def reportHasExitedIfNeeded(er: ErrorReporter, compilationStep: CompilationStep,
                              posOpt: Option[Position]): Unit = {
    if (exitedStatus == ExitedStatus.HasExited) {
      er.push(Err(compilationStep, "dead code", posOpt))
      exitedStatus = ExitedStatus.ReportedHasExited
    }
  }

  def hasExited: Boolean = exitedStatus != ExitedStatus.Active
}