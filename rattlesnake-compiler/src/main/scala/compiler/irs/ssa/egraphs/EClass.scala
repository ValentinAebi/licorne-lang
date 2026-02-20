package compiler.irs.ssa.egraphs

import scala.collection.mutable

final class EClass {
  private val nodes = mutable.LinkedHashSet.empty[ENode]
  private var deleted = false

  def addNode(node: ENode): Unit = {
    checkNotDestroyed()
    nodes.add(node)
  }

  def deleteAndTransferTo(target: EClass): Unit = {
    require(target != this)
    target.nodes.addAll(nodes)
    deleted = true
  }

  private def checkNotDestroyed(): Unit = {
    if (deleted) {
      throw IllegalStateException("attempt to access a deleted e-class")
    }
  }

}
