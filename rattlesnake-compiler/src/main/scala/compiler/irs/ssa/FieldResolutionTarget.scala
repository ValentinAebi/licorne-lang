package compiler.irs.ssa

import compiler.identifiers.FunOrVarId
import compiler.lang.Types.Type
import compiler.lang.UserInstantiableTypeSig

final class FieldResolutionTarget(val fieldId: FunOrVarId) {
  private var receiverSigOpt = Option.empty[UserInstantiableTypeSig]
  private var instantiatedFieldTypeOpt = Option.empty[Type]
  private var cannotResolveFlag = false

  def isResolved: Boolean = receiverSigOpt.isDefined

  def isResolvedAndStable: Boolean =
    receiverSigOpt.exists(_.fields.get(fieldId).exists(_.isStable))

  def isUnresolvable: Boolean = cannotResolveFlag

  def isNotResolvedYet: Boolean = !isResolved && !isUnresolvable

  def resolve(receiverSig: UserInstantiableTypeSig, instantiatedFieldType: Type): Unit = {
    if (isResolved) {
      throw AssertionError("trying to resolve an already resolved field resolution target")
    } else if (isUnresolvable) {
      throw AssertionError("trying to resolve a field resolution target marked as unresolvable")
    }
    receiverSigOpt = Some(receiverSig)
    instantiatedFieldTypeOpt = Some(instantiatedFieldType)
  }

  def getReceiverSigUnsafe: UserInstantiableTypeSig = receiverSigOpt.get

  def getInstantiatedFieldTypeUnsafe: Type = instantiatedFieldTypeOpt.get

  def markUnresolvable(): Unit = {
    cannotResolveFlag = true
  }

  override def toString: String = {
    if isResolved then s"$fieldId<rec:${getReceiverSigUnsafe.id};ret:$getInstantiatedFieldTypeUnsafe>"
    else if isUnresolvable then s"$fieldId<unresolved>"
    else s"$fieldId<resol:?>"
  }
}
