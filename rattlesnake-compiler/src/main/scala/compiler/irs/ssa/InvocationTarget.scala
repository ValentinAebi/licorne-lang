package compiler.irs.ssa

import compiler.identifiers.FunOrVarId
import compiler.lang.{EncapsulatedTypeSig, FunctionSignature}
import compiler.lang.Types.Type

final class InvocationTarget(val funId: FunOrVarId) {
  private var receiverSigOpt = Option.empty[EncapsulatedTypeSig]
  private var funSigOpt = Option.empty[FunctionSignature]
  private var instantiatedReturnTypeOpt = Option.empty[Type]
  private var cannotResolveFlag = false

  def isResolved: Boolean = receiverSigOpt.isDefined

  def isResolvedAndPure: Boolean = funSigOpt.exists(_.isPure)

  def isUnresolvable: Boolean = cannotResolveFlag

  def isNotResolvedYet: Boolean = !isResolved && !isUnresolvable

  def resolve(receiverSig: EncapsulatedTypeSig, funSig: FunctionSignature, instantiatedReturnType: Type): Unit = {
    if (isResolved) {
      throw AssertionError("trying to resolve an already resolved field resolution target")
    } else if (isUnresolvable) {
      throw AssertionError("trying to resolve a field resolution target marked as unresolvable")
    }
    receiverSigOpt = Some(receiverSig)
    funSigOpt = Some(funSig)
    instantiatedReturnTypeOpt = Some(instantiatedReturnType)
  }

  def getReceiverSigUnsafe: EncapsulatedTypeSig = receiverSigOpt.get

  def getFunSigUnsafe: FunctionSignature = funSigOpt.get

  def getInstantiatedReturnTypeUnsafe: Type = instantiatedReturnTypeOpt.get

  def markUnresolvable(): Unit = {
    cannotResolveFlag = true
  }

  override def toString: String = {
    if isResolved then s"$funId<rec:${getFunSigUnsafe.ownerName};ret:$getInstantiatedReturnTypeUnsafe>"
    else if isUnresolvable then s"$funId<unresolved>"
    else s"$funId<resol:?>"
  }
}
