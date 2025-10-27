package lang

import identifiers.FunOrVarId
import lang.Types.Type
import lang.Visibility.Public

trait PredefApi {

  def functions: Map[FunOrVarId, FunctionSignature]

  protected def sig(name: FunOrVarId, args: List[(Option[FunOrVarId], Type)], retType: Type): (FunOrVarId, FunctionSignature) = {
    name -> FunctionSignature(name, args, retType, Public)
  }
  
}
