package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.ircorne.Formulas.{IdValue, UninterpretedConstIdValue}
import compiler.irs.ircorne.IRcorne.{LocalDecl, Scope}
import compiler.lang.ReassigPermission
import compiler.lang.Types.Type
import compiler.valuesconversion.ValuesContext.LocalInfo

trait ValuesContext {

  val globalCtx: GlobalValuesContext

  def resolveObject(objectId: TypeIdentifier): UninterpretedConstIdValue

  def deepCopyWithSameGlobalCtx: ValuesContext

  def withOneMoreFrame: LocalValuesContext

  private[valuesconversion] def queryLocal(id: FunOrVarId): Option[LocalInfo]

}

object ValuesContext {
  private[valuesconversion] final case class LocalInfo(
                                                        var value: Option[IdValue],
                                                        defScope: Scope,
                                                        reassigPermission: ReassigPermission,
                                                        var declarationTypeAnnotOpt: Option[Type]
                                                      ){
    private var declOpt: Option[LocalDecl] = None

    def declaration_=(decl: LocalDecl): Unit = {
      declOpt = Some(decl)
      declarationTypeAnnotOpt = Some(decl.tpe)
    }

    def declaration: Option[LocalDecl] = declOpt
  }
}
