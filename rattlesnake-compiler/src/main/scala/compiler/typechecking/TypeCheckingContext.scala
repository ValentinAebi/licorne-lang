package compiler.typechecking

import compiler.program.Program
import lang.Types.{BaseType, Type}
import lang.Values.IdValue

final case class TypeCheckingContext(
                                      program: Program,
                                      smartcasts: Map[IdValue, BaseType],
                                      thisVal: IdValue
                                    ) {
  private var alwaysExitsFlag = false
  
  def raiseAlwaysExitsFlag(): Unit = {
    alwaysExitsFlag = true
  }
  
  def alwaysExitsFlagIsRaised: Boolean = alwaysExitsFlag

  def withAdditionalSmartCasts(newSmartCasts: Map[IdValue, BaseType]): TypeCheckingContext = {
    val newCtx = copy(smartcasts = smartcasts ++ newSmartCasts)
    newCtx.alwaysExitsFlag = this.alwaysExitsFlag
    newCtx
  }

}
