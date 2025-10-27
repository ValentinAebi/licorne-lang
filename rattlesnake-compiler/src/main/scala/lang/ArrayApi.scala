package lang

import identifiers.{FunOrVarId, NormalFunOrVarId, NormalTypeId, TypeIdentifier}

object ArrayApi extends PredefApi {

  override def name: TypeIdentifier = NormalTypeId("Array")

  val length: FunOrVarId = NormalFunOrVarId("length")
  val get: FunOrVarId = NormalFunOrVarId("get")
  val set: FunOrVarId = NormalFunOrVarId("set")

  override def typeParams: List[TypeIdentifier] = List(NormalTypeId("T"))

  def functions: Map[FunOrVarId, FunctionSignature] = Map(
    // TODO with refined types and a type parameter
  )

}
