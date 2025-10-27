package compiler.pipeline


trait CompilerStep[-In, +Out] {
  thisStep =>

  def apply(input: In): Out

  final infix def andThen[NextIn >: Out, NextOut](nextStep: CompilerStep[NextIn, NextOut]): CompilerStep[In, NextOut] = {
    (input: In) => {
      val func = thisStep.apply.andThen(nextStep.apply)
      func.apply(input)
    }
  }

}

/**
 * Runs `threadPipeline` on multiple inputs
 */
final case class MultiStep[In, Out](threadPipeline: CompilerStep[In, Out]) extends CompilerStep[List[In], List[Out]] {

  override def apply(input: List[In]): List[Out] = {
    input.map(threadPipeline.apply)
  }
}

/**
 * Compiler step that performs a transformation using `f`
 */
final case class Mapper[In, Out](f: In => Out) extends CompilerStep[In, Out] {
  override def apply(input: In): Out = f(input)
}
