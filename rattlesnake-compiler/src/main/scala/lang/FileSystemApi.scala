package lang

import identifiers.{FunOrVarId, NormalFunOrVarId, NormalTypeId, TypeIdentifier}
import lang.Types.PrimitiveTypeShape.{BoolType, IntType, StringType, VoidType}

object FileSystemApi extends PredefApi {

  override def name: TypeIdentifier = NormalTypeId("FileSystem")

  val openR: FunOrVarId = NormalFunOrVarId("openR")
  val openW: FunOrVarId = NormalFunOrVarId("openW")
  val openA: FunOrVarId = NormalFunOrVarId("openA")
  val write: FunOrVarId = NormalFunOrVarId("write")
  val read: FunOrVarId = NormalFunOrVarId("read")
  val close: FunOrVarId = NormalFunOrVarId("close")
  val createDir: FunOrVarId = NormalFunOrVarId("createDir")
  val delete: FunOrVarId = NormalFunOrVarId("delete")

  override def typeParams: List[TypeIdentifier] = List.empty

  override def functions: Map[FunOrVarId, FunctionSignature] = Map(
    sig(openR, List(path -> StringType.toType), IntType.toType),
    sig(openW, List(path -> StringType.toType), IntType.toType),
    sig(openA, List(path -> StringType.toType), IntType.toType),
    sig(write, List(fileId -> IntType.toType, NormalFunOrVarId("s") -> StringType.toType), VoidType.toType),
    sig(read, List(fileId -> IntType.toType), IntType.toType),
    sig(close, List(fileId -> IntType.toType), VoidType.toType),
    sig(createDir, List(path -> StringType.toType), BoolType.toType),
    sig(delete, List(path -> StringType.toType), BoolType.toType)
  )
  
  private val path = NormalFunOrVarId("path")
  private val fileId = NormalFunOrVarId("fileId")
  
}
