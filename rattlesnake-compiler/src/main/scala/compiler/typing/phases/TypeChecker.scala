package compiler.typing.phases

import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.typing.TypeStore

final class TypeChecker(er: ErrorReporter, typeStore: TypeStore) extends CompilerStep[Program, Program] {
  
  private given CompilationStep = TypeChecking

  override def apply(input: Program): Program = {
    ???
  }
  
  // TODO check that user-provided assignments of type parameters match bounds

  // TODO call for methods and closures

  // TODO check that non-Unit methods and closures return
  
}
