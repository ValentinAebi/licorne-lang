package compiler.typing.phases

import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.typing.TypeStore


final class TyperPhase1(ts: TypeStore) extends CompilerStep[Program, Program] {

  override def apply(program: Program): Program = {
    ???
  }

}
