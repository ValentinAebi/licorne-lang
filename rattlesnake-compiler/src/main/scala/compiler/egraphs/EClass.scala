package compiler.egraphs

final case class EClass(nodes: Set[ENode], idAliases: Set[EClassId], canonicalId: EClassId) {
  require(idAliases.contains(canonicalId))

  def withNewNode(node: ENode): EClass =
    copy(nodes = nodes + node)

}
