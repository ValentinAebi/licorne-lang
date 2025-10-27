package lang

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Types.Type
import lang.Visibility.Public

import scala.collection.mutable

trait PredefApi {
  
  def name: TypeIdentifier
  def typeParams: List[TypeIdentifier]
  def functions: Map[FunOrVarId, FunctionSignature]

  protected def sig(name: FunOrVarId, args: List[(FunOrVarId, Type)], retType: Type): (FunOrVarId, FunctionSignature) = {
    name -> FunctionSignature(name, List.empty, mutable.LinkedHashMap.from(args), retType, Public)
  }
  
}

object PredefApi {

  val predefPackageApis: List[PredefApi] = List(ConsoleApi, FileSystemApi)
  val predefClassApis: List[PredefApi] = List(ArrayApi)
  
}
