package compiler.irs.ssa

import compiler.lang.Types.ClosureType

import java.util.Objects

final class ClosureTypingTarget extends CallableTarget {
  private var typeOpt = Option.empty[ClosureType]
  private var unresolvableFlag = false

  override def isResolved: Boolean = typeIfResolved.isDefined
  
  override def isResolvedAndPure: Boolean =
    typeIfResolved.exists(_.enforcedPure)

  override def isUnresolvable: Boolean = unresolvableFlag
  
  override def markUnresolvable(): Unit = {
    unresolvableFlag = true
  }

  def typeIfResolved: Option[ClosureType] = typeOpt
  
  def getTypeUnsafe: ClosureType = typeIfResolved.get

  def resolve(tpe: ClosureType): Unit = {
    if (isResolved) {
      throw IllegalStateException(classOf[ClosureTypingTarget].getSimpleName + " resolved more than once")
    }
    typeOpt = Some(tpe)
  }

  override def equals(obj: Any): Boolean = obj match {
    case obj: ClosureTypingTarget =>
      this.typeOpt == obj.typeOpt &&
        this.unresolvableFlag == obj.unresolvableFlag
    case _ => false
  }

  override def hashCode(): Int = Objects.hash(typeOpt, unresolvableFlag)

}
