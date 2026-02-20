package compiler.typing.phases

import compiler.pipeline.CompilerStep
import compiler.program.Program

final class TyperPhase2 extends CompilerStep[(Program, TypeStore), (Program, TypeStore)] {

  override def apply(input: (Program, TypeStore)): (Program, TypeStore) = {
    ???
  }
  
}
