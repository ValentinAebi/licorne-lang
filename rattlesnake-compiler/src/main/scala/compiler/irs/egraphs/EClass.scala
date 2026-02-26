package compiler.irs.egraphs

import scala.collection.mutable


final class EClass(egraph: EGraph) {
  private val nodes = mutable.LinkedHashSet.empty[ENode]
  private val upperBounds = mutable.LinkedHashSet.empty[EClassId]
  private val lowerBounds = mutable.LinkedHashSet.empty[EClassId]
  private val disequalities = mutable.LinkedHashSet.empty[EClassId]

  private var constValue = Option.empty[ConstNode]

  def copyTypingDataTo(dst: EClass): Unit = {
    dst.upperBounds.addAll(this.upperBounds)
    dst.lowerBounds.addAll(this.lowerBounds)
    dst.disequalities.addAll(this.disequalities)
    if (dst.constValue.isEmpty) {
      dst.constValue = this.constValue
    }
  }

  def asConst: Option[ConstNode] = constValue

  def addNode(node: ENode): Boolean = {
    nodes.add(node)
    node match {
      case node: ConstNode if constValue.isEmpty =>
        constValue = Some(node)
        true
      case node: ConstNode if node != constValue.get =>
        false
      case _ => true
    }
  }

  def saveUpperBound(ub: EClassId): Boolean = {
    upperBounds.add(ub)
  }

  def saveLowerBound(lb: EClassId): Boolean = {
    lowerBounds.add(lb)
  }

  def saveDisequality(disEq: EClassId): Boolean = {
    disequalities.add(disEq)
  }

  def currentNodes: Set[ENode] = Set.from(nodes)

  def currentUpperBounds: Set[EClassId] = Set.from(upperBounds)

  def currentLowerBounds: Set[EClassId] = Set.from(lowerBounds)

  def currentDisequalities: Set[EClassId] = Set.from(disequalities)

  export nodes.contains as containsNode
  export upperBounds.contains as hasDirectUpperBound
  export lowerBounds.contains as hasDirectLowerBound
  export disequalities.contains as hasDisequality

}
