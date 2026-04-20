package compiler.typing.smartcasting.egraphs

import compiler.lang.Formulas.Formula
import compiler.lang.Types.{IntersectionType, Type}
import compiler.smt.Simplifier

import scala.collection.mutable

final class EClass(val uid: Long) {
  private val nodes = mutable.LinkedHashSet.empty[ENode]
  private var smartcastTypeOpt = Option.empty[Type]
  private val explicitFormulas = mutable.LinkedHashSet.empty[Formula]

  private[egraphs] def initializeWith(nodes: IterableOnce[ENode], smartcastOpt: Option[Type], formulas: IterableOnce[Formula]): Unit = {
    if (this.nodes.nonEmpty || this.smartcastTypeOpt.nonEmpty || this.explicitFormulas.nonEmpty) {
      throw new AssertionError("e-class is not empty")
    }
    this.nodes.addAll(nodes)
    this.smartcastTypeOpt = smartcastOpt
    this.explicitFormulas.addAll(formulas)
  }

  def addNode(node: ENode): Unit = {
    nodes.add(node)
  }

  def nodesView: Iterable[ENode] = nodes

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

  def getSmartcastType: Option[Type] = smartcastTypeOpt

  def addExplicitFormula(formula: Formula): Unit = {
    explicitFormulas.add(formula)
  }

  def addExplicitFormulas(formulas: Iterable[Formula]): Unit = {
    explicitFormulas.addAll(formulas)
  }

  def explicitFormulasView: Iterable[Formula] = explicitFormulas
  
  def shortDescr: String = s"*$uid"

}
