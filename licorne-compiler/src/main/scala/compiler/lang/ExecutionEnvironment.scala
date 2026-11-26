package compiler.lang

import compiler.lang.Types.Type
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position

trait ExecutionEnvironment {
  def expectedResultType: Type
  
  def reportImpurity(msg: String, posOpt: Option[Position], er: ErrorReporter)(using CompilationStep): Unit
  
}
