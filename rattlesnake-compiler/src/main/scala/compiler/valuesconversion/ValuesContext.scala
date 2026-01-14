package compiler.valuesconversion

import compiler.valuesconversion.ValuesContext.LocalInfo
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.ReassigPermission
import lang.Types.Type
import lang.Values.{Constant, IdValue, Value}

trait ValuesContext {

  val globalCtx: GlobalValuesContext
  val valuesGen: ValuesGenerator

  def resolveObject(objectId: TypeIdentifier): Value

  def deepCopyWithSameGlobalCtx: ValuesContext

  private[valuesconversion] def queryLocal(id: FunOrVarId): Option[LocalInfo]

}

object ValuesContext {
  private[valuesconversion] final case class LocalInfo(
                                                        var value: Option[IdValue],
                                                        reassigPermission: ReassigPermission,
                                                        typeUpperBoundOpt: Option[Type]
                                                      )
}
