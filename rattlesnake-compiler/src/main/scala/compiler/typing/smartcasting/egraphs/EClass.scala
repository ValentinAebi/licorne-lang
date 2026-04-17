package compiler.typing.smartcasting.egraphs

import compiler.lang.Formulas.Formula
import compiler.lang.Types.{IntersectionType, Type}
import compiler.smt.{MeetJoinComputer, Simplifier}

import scala.collection.mutable

final class EClass {
  private val nodes = mutable.LinkedHashSet.empty[ENode]
  private val currentRefs = mutable.LinkedHashSet.empty[EClass.Ref]
  private var smartcastTypeOpt: Option[Type] = None
  private val explicitFormulas = mutable.LinkedHashSet.empty[Formula]

  private[egraphs] def initFrom(nodes: IterableOnce[ENode],
                                refs: IterableOnce[EClass.Ref],
                                smartcastTypeOpt: Option[Type],
                                formulas: IterableOnce[Formula]): Unit = {
    if (this.nodes.nonEmpty || this.currentRefs.nonEmpty || this.smartcastTypeOpt.nonEmpty || this.explicitFormulas.nonEmpty) {
      throw IllegalStateException(s"trying to initialize an already initialized ${classOf[EClass].getSimpleName.toLowerCase}")
    }
    this.nodes.addAll(nodes)
    this.currentRefs.addAll(refs)
    this.smartcastTypeOpt = smartcastTypeOpt
    this.explicitFormulas.addAll(formulas)
  }

  def addNode(n: ENode): Unit = {
    nodes.add(n)
  }

  def nodesView: Iterable[ENode] = nodes

  def currentReferencesView: Iterable[EClass.Ref] = currentRefs

  def getSmartcastType: Option[Type] = smartcastTypeOpt

  def saveSmartcast(tpe: Type)(using simplifier: Simplifier): Option[Type] = {
    val newSmartcast = smartcastTypeOpt match {
      case Some(oldSmartcastType) =>
        simplifier.simplify(IntersectionType(oldSmartcastType, tpe))
      case None => tpe
    }
    if (smartcastTypeOpt.contains(newSmartcast)) {
      None
    } else {
      smartcastTypeOpt = Some(newSmartcast)
      smartcastTypeOpt
    }
  }

  def addExplicitFormula(f: Formula): Unit = {
    explicitFormulas.add(f)
  }

  def getExplicitFormulas: collection.Set[Formula] = explicitFormulas

}

object EClass {

  /**
   * WARNING: unstable equals and hashCode, use with care in HashMaps
   */
  final class Ref(initEClass: EClass) {
    private var target = Option.empty[EClass]
    private val nodesReferringToThis = mutable.Set.empty[ENode]

    setTarget(initEClass)

    def setTarget(newEClass: EClass): Unit = {
      target.foreach { target =>
        target.currentRefs.remove(this)
      }
      target = Some(newEClass)
      newEClass.currentRefs.add(this)
    }

    def getTarget: EClass = target.get

    def addNodeWithThisRefAsOperand(n: ENode): Unit = {
      nodesReferringToThis.add(n)
    }

    private[egraphs] def initNodesWithThisAsOperand(nodes: IterableOnce[ENode]): Unit = {
      if (this.nodesReferringToThis.nonEmpty) {
        throw new IllegalStateException("list of nodes referring to this reference has already been initialized")
      }
      this.nodesReferringToThis.addAll(nodes)
    }

    def getNodesWithThisRefAsOperand: Iterable[ENode] = nodesReferringToThis

    override def equals(that: Any): Boolean = that match {
      case that: Ref =>
        this.target == that.target
      case _ => false
    }

    override def hashCode(): Int = target.hashCode()

  }

}
