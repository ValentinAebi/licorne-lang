package compiler.egraphs

import compiler.util.SeqSet

import scala.collection.immutable.SortedSet
import scala.collection.mutable
import scala.reflect.ClassTag

final case class EClass(nodes: SeqSet[ENode], idAliases: SortedSet[EClassId], canonicalId: EClassId) {
  require(idAliases.contains(canonicalId))

  def withNewNode(node: ENode): EClass =
    copy(nodes = nodes.incl(node))
    
  def findNodesOfType[N <: ENode : ClassTag]: SeqSet[N] = {
    val resBuffer = mutable.ListBuffer.empty[N]
    nodes.foreach {
      case n: N =>
        resBuffer.addOne(n)
      case _ => ()
    }
    SeqSet(resBuffer)
  }

}
