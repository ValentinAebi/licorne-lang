package compiler.typing

import compiler.lang.FunctionSignature

import scala.collection.mutable


final class OverridesStore {
  private val overrides = mutable.Map.empty[FunctionSignature, mutable.LinkedHashSet[FunctionSignature]]
  
  def saveOverride(subFunc: FunctionSignature, superFunc: FunctionSignature): Unit = {
    overrides.getOrElseUpdate(subFunc, mutable.LinkedHashSet.empty).add(superFunc)
  }
  
  def getFunctionsOverriddenBy(func: FunctionSignature): Iterable[FunctionSignature] = overrides.getOrElse(func, List.empty)

}
