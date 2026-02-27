package compiler.typing.phases

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.lang.*
import compiler.lang.Field.*
import compiler.lang.Formulas.*
import compiler.lang.Operators.OperatorSignature
import compiler.lang.Types.*
import compiler.lang.Visibility.Private
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.typing.TypeStore
import compiler.typing.contexts.DealiasingContext
import compiler.typing.smartcasting.ControlFlowInfo
import compiler.util.{Result, mapVals}

import scala.collection.mutable
import scala.util.boundary


final class TyperPhase1(ts: TypeStore) extends CompilerStep[Program, Program] {

  override def apply(program: Program): Program = {
    ???
  }

}
