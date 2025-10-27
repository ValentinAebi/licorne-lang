package lang

import identifiers.{FunOrVarId, NormalFunOrVarId, NormalTypeId, TypeIdentifier}
import lang.Types.PrimitiveTypeShape.{StringType, VoidType}

object ConsoleApi extends PredefApi {

  override def name: TypeIdentifier = NormalTypeId("Console")

  val print: FunOrVarId = NormalFunOrVarId("print")
  val readLine: FunOrVarId = NormalFunOrVarId("readLine")

  override def typeParams: List[TypeIdentifier] = List.empty

  override def functions: Map[FunOrVarId, FunctionSignature] = Map(
    sig(print, List(NormalFunOrVarId("s") -> StringType.toType), VoidType.toType),
    sig(readLine, List.empty, StringType.toType)
  )
  
}
