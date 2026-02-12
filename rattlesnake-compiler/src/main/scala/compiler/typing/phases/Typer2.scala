package compiler.typing.phases

import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.typing.TypeStore

final class Typer2 extends CompilerStep[(Program, TypeStore), (Program, TypeStore)] {

  override def apply(input: (Program, TypeStore)): (Program, TypeStore) = {
    ???
  }
  
}
