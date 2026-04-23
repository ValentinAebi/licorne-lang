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
 * Runs `pipeline1` and then `pipeline2`, and combines their output
 */
final case class Concurrent[In, Out1, Out2, Out](
                                             pipeline1: CompilerStep[In, Out1],
                                             pipeline2: CompilerStep[In, Out2],
                                             combineFunc: (Out1, Out2) => Out
                                           ) extends CompilerStep[In, Out] {
  override def apply(input: In): Out = {
    val out1 = pipeline1.apply(input)
    val out2 = pipeline2.apply(input)
    combineFunc(out1, out2)
  }
}

final case class IdentityStep[Data]() extends CompilerStep[Data, Data] {
  override def apply(input: Data): Data = input
}
