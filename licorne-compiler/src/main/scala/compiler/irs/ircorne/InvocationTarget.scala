package compiler.irs.ircorne

import compiler.identifiers.FunOrVarId
import compiler.lang.Types.Type
import compiler.lang.{FunctionSignature, RuntimeTypeSignature}

import java.util.Objects

final class InvocationTarget(val funId: FunOrVarId) extends CallableTarget {
  private var receiverSigOpt = Option.empty[RuntimeTypeSignature]
  private var funSigOpt = Option.empty[FunctionSignature]
  private var instantiatedReturnTypeOpt = Option.empty[Type]
  private var cannotResolveFlag = false

  override def isResolved: Boolean = receiverSigOpt.isDefined

  override def isResolvedAndPure: Boolean = funSigOpt.exists(_.isPure)

  override def isUnresolvable: Boolean = cannotResolveFlag

  def resolve(receiverSig: RuntimeTypeSignature, funSig: FunctionSignature, instantiatedReturnType: Type): Unit = {
    if (isUnresolvable) {
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

  override def equals(obj: Any): Boolean = obj match {
    case obj: InvocationTarget =>
      this.receiverSigOpt == obj.receiverSigOpt &&
        this.funSigOpt == obj.funSigOpt &&
        this.instantiatedReturnTypeOpt == obj.instantiatedReturnTypeOpt &&
        this.cannotResolveFlag == obj.cannotResolveFlag
    case _ => false
  }

  override def hashCode(): Int = Objects.hash(receiverSigOpt, funSigOpt, instantiatedReturnTypeOpt, cannotResolveFlag)

  override def toString: String = {
    if isResolved then s"$funId<rec:${getFunSigUnsafe.ownerName};ret:$getInstantiatedReturnTypeUnsafe>"
    else if isUnresolvable then s"$funId<unresolved>"
    else s"$funId<resol:?>"
  }
}
