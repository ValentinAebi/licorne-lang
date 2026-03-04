package compiler.egraphs

import scala.collection.immutable.SortedSet

final case class EClass(nodes: Set[ENode], idAliases: SortedSet[EClassId], canonicalId: EClassId) {
  require(idAliases.contains(canonicalId))

  def withNewNode(node: ENode): EClass =
    copy(nodes = nodes + node)

}
