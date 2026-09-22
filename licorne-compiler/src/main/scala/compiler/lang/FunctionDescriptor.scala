package compiler.lang

import compiler.identifiers.FunOrVarId

final case class FunctionDescriptor(funId: FunOrVarId, paramsCnt: Int) {
  override def toString: String = s"$funId(#$paramsCnt)"
}
