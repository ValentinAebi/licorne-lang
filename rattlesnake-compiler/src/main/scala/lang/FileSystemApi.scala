package lang

import identifiers.{FunOrVarId, NormalFunOrVarId}
import lang.Types.PrimitiveTypeShape.{BoolType, IntType, StringType, VoidType}

object FileSystemApi extends Device.DeviceApi {

  val openR: FunOrVarId = NormalFunOrVarId("openR")
  val openW: FunOrVarId = NormalFunOrVarId("openW")
  val openA: FunOrVarId = NormalFunOrVarId("openA")
  val write: FunOrVarId = NormalFunOrVarId("write")
  val read: FunOrVarId = NormalFunOrVarId("read")
  val close: FunOrVarId = NormalFunOrVarId("close")
  val createDir: FunOrVarId = NormalFunOrVarId("createDir")
  val delete: FunOrVarId = NormalFunOrVarId("delete")


  override def functions: Map[FunOrVarId, FunctionSignature] = Map(
    sig(openR, List(None -> StringType), IntType),
    sig(openW, List(None -> StringType), IntType),
    sig(openA, List(None -> StringType), IntType),
    sig(write, List(None -> IntType, None -> StringType), VoidType),
    sig(read, List(None -> IntType), IntType),
    sig(close, List(None -> IntType), VoidType),
    sig(createDir, List(None -> StringType), BoolType),
    sig(delete, List(None -> StringType), BoolType)
  )
  
}
