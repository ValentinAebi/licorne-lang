package compiler.valuesconversion

import compiler.valuesconversion.ValuesContext.LocalInfo
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.ReassigStatus
import lang.Types.Type
import lang.Values.Value

trait ValuesContext {

  val valuesGen: ValuesGenerator

  def resolveObject(objectId: TypeIdentifier): Value
  
  private[valuesconversion] def updateLocal(id: FunOrVarId, value: Value): Boolean
  
  private[valuesconversion] def queryLocal(id: FunOrVarId): Option[LocalInfo]
  
}

object ValuesContext {
  protected[valuesconversion] final case class LocalInfo(var value: Option[Value], reassigStatus: ReassigStatus, typeUpperBound: Option[Type])
}
