package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.ssa.Formulas.IdValue
import compiler.lang.ReassigPermission
import compiler.valuesconversion.ValuesContext.LocalInfo
import compiler.lang.Types.Type

trait ValuesContext {

  val globalCtx: GlobalValuesContext

  def resolveObject(objectId: TypeIdentifier): IdValue

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
