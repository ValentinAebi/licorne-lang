package lang

import identifiers.{FunOrVarId, NormalFunOrVarId}

object ArrayApi extends PredefApi {
  
  val length: FunOrVarId = NormalFunOrVarId("length")
  val get: FunOrVarId = NormalFunOrVarId("get")
  val set: FunOrVarId = NormalFunOrVarId("set")
  
  def functions: Map[FunOrVarId, FunctionSignature] = Map(
    // TODO with refined types and a type parameter
  )

}
