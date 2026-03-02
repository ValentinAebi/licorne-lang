package compiler.typing.phases

import compiler.lang.Types.PrimitiveType.UnitType
import compiler.lang.Types.Type
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.TypeStore
import compiler.typing.smartcasting.ControlFlowInfo

final class TypeChecker(er: ErrorReporter, typeStore: TypeStore) extends CompilerStep[Program, Program] {
  
  private given CompilationStep = TypeChecking

  override def apply(input: Program): Program = {
    ???
  }
  
  // TODO check that user-provided assignments of type parameters match bounds

  // TODO call for methods and closures
  private def checkReturnsIfNonUnit(retType: Type, endCf: ControlFlowInfo, functionKindDescr: String, posOpt: Option[Position]): Unit = {
    if (retType != UnitType && !endCf.hasExited) {
      er.reportError(s"missing return in non-$UnitType $functionKindDescr", posOpt)
    }
  }
  
}
