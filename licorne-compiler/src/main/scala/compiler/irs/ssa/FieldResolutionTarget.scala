package compiler.irs.ssa

import compiler.identifiers.FunOrVarId
import compiler.lang.Types.Type
import compiler.lang.{FunctionSignature, RuntimeTypeSignature}

final class FieldResolutionTarget(val fieldId: FunOrVarId) {
  private var receiverSigOpt = Option.empty[RuntimeTypeSignature]
  private var instantiatedTypeOpt = Option.empty[Type]
  private var accessorFunSigOpt = Option.empty[FunctionSignature]
  private var cannotResolveFlag = false

  def isResolved: Boolean = receiverSigOpt.isDefined

  def isResolvedAndPure: Boolean = isResolved && (accessorFunSigOpt match {
    case Some(accessorFunSig) => accessorFunSig.isPure
    case None => receiverSigOpt.exists(_.fields.get(fieldId).exists(_.isStable))
  })

  def isUnresolvable: Boolean = cannotResolveFlag

  def isNotResolvedYet: Boolean = !isResolved && !isUnresolvable

  def resolve(receiverSig: RuntimeTypeSignature, instantiatedType: Type, accessorSigOpt: Option[FunctionSignature]): Unit = {
    require(accessorSigOpt.forall(a => a.isPure))
    if (isResolved) {
      throw AssertionError("trying to resolve an already resolved field resolution target")
    } else if (isUnresolvable) {
      throw AssertionError("trying to resolve a field resolution target marked as unresolvable")
    }
    receiverSigOpt = Some(receiverSig)
    instantiatedTypeOpt = Some(instantiatedType)
    accessorFunSigOpt = accessorSigOpt
  }

  def getReceiverSigOpt: Option[RuntimeTypeSignature] = receiverSigOpt

  def getReceiverSigUnsafe: RuntimeTypeSignature = receiverSigOpt.get

  def getInstantiatedTypeUnsafe: Type = instantiatedTypeOpt.get

  def getAccessorSigOpt: Option[FunctionSignature] = accessorFunSigOpt

  def markUnresolvable(): Unit = {
    cannotResolveFlag = true
  }

  def asFreshInvocationTarget: Option[InvocationTarget] = for {
    accessorSig <- getAccessorSigOpt
    receiverSig <- receiverSigOpt
    retType <- instantiatedTypeOpt
  } yield {
    val invkTarget = InvocationTarget(fieldId)
    invkTarget.resolve(receiverSig, accessorSig, retType)
    invkTarget
  }

  override def toString: String = {
    if isResolved then s"$fieldId<rec:${getReceiverSigUnsafe.id};ret:$getInstantiatedTypeUnsafe;accessor=${getAccessorSigOpt.isDefined}>"
    else if isUnresolvable then s"$fieldId<unresolved>"
    else s"$fieldId<resol:?>"
  }
}
