package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.ReassigPermission
import compiler.valuesconversion.ValuesContext.LocalInfo
import compiler.lang.Types.Type
import compiler.lang.Formulas.{Constant, IdValue, Value}

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
