package lang

import identifiers.{FunOrVarId, NormalFunOrVarId}
import lang.Types.PrimitiveTypeShape.{StringType, VoidType}

object ConsoleApi extends Device.DeviceApi {

  val print: FunOrVarId = NormalFunOrVarId("print")
  val readLine: FunOrVarId = NormalFunOrVarId("readLine")

  override def functions: Map[FunOrVarId, FunctionSignature] = Map(
    sig(print, List(None -> StringType), VoidType),
    sig(readLine, List.empty, StringType)
  )
  
}
