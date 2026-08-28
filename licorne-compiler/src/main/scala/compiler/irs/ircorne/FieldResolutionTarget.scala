package compiler.irs.ircorne

import compiler.identifiers.FunOrVarId
import compiler.lang.{Field, RuntimeTypeSignature}
import compiler.lang.Types.Type

final class FieldResolutionTarget(val fieldId: FunOrVarId) {
  private var receiverSigOpt = Option.empty[RuntimeTypeSignature]
  private var instantiatedTypeOpt = Option.empty[Type]
  private var cannotResolveFlag = false

  def isResolved: Boolean = receiverSigOpt.isDefined

  def isResolvedAndPure: Boolean = isResolved && receiverSigOpt.exists(_.fields.get(fieldId).exists(_.isStable))

  def isUnresolvable: Boolean = cannotResolveFlag

  def isNotResolvedYet: Boolean = !isResolved && !isUnresolvable

  def resolve(receiverSig: RuntimeTypeSignature, instantiatedType: Type): Unit = {
    if (isUnresolvable) {
      throw AssertionError("trying to resolve a field resolution target marked as unresolvable")
    }
    receiverSigOpt = Some(receiverSig)
    instantiatedTypeOpt = Some(instantiatedType)
  }

  def getReceiverSigOpt: Option[RuntimeTypeSignature] = receiverSigOpt

  def getReceiverSigUnsafe: RuntimeTypeSignature = receiverSigOpt.get

  def getInstantiatedTypeUnsafe: Type = instantiatedTypeOpt.get
  
  def getFieldUnsafe: Field = getReceiverSigUnsafe.fields.apply(fieldId)

  def markUnresolvable(): Unit = {
    cannotResolveFlag = true
  }

  override def toString: String = {
    if isResolved then s"$fieldId<rec:${getReceiverSigUnsafe.id};ret:$getInstantiatedTypeUnsafe>"
    else if isUnresolvable then s"$fieldId<unresolved>"
    else s"$fieldId<resol:?>"
  }
}
