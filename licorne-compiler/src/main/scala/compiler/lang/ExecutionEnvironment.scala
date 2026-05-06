package compiler.lang

import compiler.lang.Types.Type

trait ExecutionEnvironment {
  def expectedResultType: Type
  def requiresPurityInBody: Boolean
  def root: FunctionSignature
}
