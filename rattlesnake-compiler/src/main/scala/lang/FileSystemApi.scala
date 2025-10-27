package lang

import identifiers.{FunOrVarId, NormalFunOrVarId}
import lang.Types.PrimitiveTypeShape.{BoolType, IntType, StringType, VoidType}

object FileSystemApi extends PredefApi {

  val openR: FunOrVarId = NormalFunOrVarId("openR")
  val openW: FunOrVarId = NormalFunOrVarId("openW")
  val openA: FunOrVarId = NormalFunOrVarId("openA")
  val write: FunOrVarId = NormalFunOrVarId("write")
  val read: FunOrVarId = NormalFunOrVarId("read")
  val close: FunOrVarId = NormalFunOrVarId("close")
  val createDir: FunOrVarId = NormalFunOrVarId("createDir")
  val delete: FunOrVarId = NormalFunOrVarId("delete")


  override def functions: Map[FunOrVarId, FunctionSignature] = Map(
    sig(openR, List(None -> StringType.toType), IntType.toType),
    sig(openW, List(None -> StringType.toType), IntType.toType),
    sig(openA, List(None -> StringType.toType), IntType.toType),
    sig(write, List(None -> IntType.toType, None -> StringType.toType), VoidType.toType),
    sig(read, List(None -> IntType.toType), IntType.toType),
    sig(close, List(None -> IntType.toType), VoidType.toType),
    sig(createDir, List(None -> StringType.toType), BoolType.toType),
    sig(delete, List(None -> StringType.toType), BoolType.toType)
  )
  
}
