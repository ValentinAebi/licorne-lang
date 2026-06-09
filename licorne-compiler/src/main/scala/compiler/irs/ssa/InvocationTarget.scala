package compiler.irs.ssa

import compiler.identifiers.FunOrVarId
import compiler.lang.{EncapsulatedTypeSig, FunctionSignature, RuntimeTypeSignature}
import compiler.lang.Types.Type

final class InvocationTarget(val funId: FunOrVarId) extends CallableTarget {
  private var receiverSigOpt = Option.empty[RuntimeTypeSignature]
  private var funSigOpt = Option.empty[FunctionSignature]
  private var instantiatedReturnTypeOpt = Option.empty[Type]
  private var cannotResolveFlag = false

  override def isResolved: Boolean = receiverSigOpt.isDefined

  override def isResolvedAndPure: Boolean = funSigOpt.exists(_.isPure)

  override def isUnresolvable: Boolean = cannotResolveFlag

  def resolve(receiverSig: RuntimeTypeSignature, funSig: FunctionSignature, instantiatedReturnType: Type): Unit = {
    if (isResolved) {
      throw AssertionError("trying to resolve an already resolved field resolution target")
    } else if (isUnresolvable) {
      throw AssertionError("trying to resolve a field resolution target marked as unresolvable")
    }
    receiverSigOpt = Some(receiverSig)
    funSigOpt = Some(funSig)
    instantiatedReturnTypeOpt = Some(instantiatedReturnType)
  }

  def getReceiverSigUnsafe: RuntimeTypeSignature = receiverSigOpt.get
  
  def getFunSigOpt: Option[FunctionSignature] = funSigOpt

  def getFunSigUnsafe: FunctionSignature = funSigOpt.get

  def getInstantiatedReturnTypeUnsafe: Type = instantiatedReturnTypeOpt.get

  override def markUnresolvable(): Unit = {
    cannotResolveFlag = true
  }

  override def toString: String = {
    if isResolved then s"$funId<rec:${getFunSigUnsafe.ownerName};ret:$getInstantiatedReturnTypeUnsafe>"
    else if isUnresolvable then s"$funId<unresolved>"
    else s"$funId<resol:?>"
  }
}
