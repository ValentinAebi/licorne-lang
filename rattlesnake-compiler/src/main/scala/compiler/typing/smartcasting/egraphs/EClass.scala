package compiler.typing.smartcasting.egraphs

import compiler.lang.Formulas.Formula
import compiler.lang.Types.Type
import compiler.typing.MeetJoinComputer

import scala.collection.mutable

final class EClass {
  private val nodes = mutable.LinkedHashSet.empty[ENode]
  private var smartcastTypeOpt: Option[Type] = None
  private val explicitFormulas = mutable.LinkedHashSet.empty[Formula]

  def deepCopy: EClass = {
    val copy = EClass()
    copy.nodes.addAll(this.nodes)
    copy.smartcastTypeOpt = this.smartcastTypeOpt
    copy.explicitFormulas.addAll(this.explicitFormulas)
    copy
  }

  def addNode(n: ENode): Unit = {
    nodes.add(n)
  }

  def nodesView: Iterable[ENode] = nodes

  def getSmartcast: Option[Type] = smartcastTypeOpt

  def saveSmartcast(tpe: Type)(using meetJoin: MeetJoinComputer): Option[Type] = {
    val newSmartcast = smartcastTypeOpt match {
      case Some(oldSmartcastType) =>
        meetJoin.computeMeet(oldSmartcastType, tpe)
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

  def explicitFormulasView: collection.Set[Formula] = explicitFormulas

}

object EClass {

  final class Id

}
