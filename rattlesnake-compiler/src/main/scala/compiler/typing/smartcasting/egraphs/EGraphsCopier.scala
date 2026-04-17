package compiler.typing.smartcasting.egraphs

import java.util

private[egraphs] final class EGraphsCopier {

  private type Copier[T] = util.IdentityHashMap[T, T]

  private val classCopier = new Copier[EClass]()
  private val refCopier = new Copier[EClass.Ref]()
  private val nodeCopier = new Copier[ENode]()

  def copyGraph(original: EGraph): EGraph = {
    val copy = EGraph.newEmpty
    copy.initNodeToClassMapping(original.getNodeToClassMapping.iterator.map {
      (node, clRef) => (copyOf(node), copyOf(clRef))
    })
    copy
  }

  private def copyOf(original: EClass): EClass = {
    if classCopier.containsKey(original) then classCopier.get(original)
    else {
      val copy = EClass()
      classCopier.put(original, copy)
      copy.initFrom(
        original.nodesView.iterator.map(copyOf),
        original.currentReferencesView.iterator.map(copyOf),
        original.getSmartcastType,
        original.getExplicitFormulas
      )
      copy
    }
  }

  private def copyOf(original: EClass.Ref): EClass.Ref = {
    if refCopier.containsKey(original) then refCopier.get(original)
    else {
      val copy = EClass.Ref(copyOf(original.getTarget))
      refCopier.put(original, copy)
      copy.initNodesWithThisAsOperand(original.getNodesWithThisRefAsOperand.iterator.map(copyOf))
      copy
    }
  }

  private def copyOf(original: ENode): ENode = {
    if nodeCopier.containsKey(original) then nodeCopier.get(original)
    else {
      val copy = original match {
        case idValNode@IdValNode(idValue) => idValNode
        case cstNode@ConstNode(cst) => cstNode
        case UnaryOpNode(op, operand) =>
          UnaryOpNode(op, copyOf(operand))
        case BinaryOpNode(lhs, op, rhs) =>
          BinaryOpNode(copyOf(lhs), op, copyOf(rhs))
        case CallNode(receiver, funId, args) =>
          CallNode(copyOf(receiver), funId, args.map(copyOf))
        case SelectNode(receiver, fieldId) =>
          SelectNode(copyOf(receiver), fieldId)
        case TypePredicateNode(subject, tpe) =>
          TypePredicateNode(copyOf(subject), tpe)
      }
      nodeCopier.put(original, copy)
      copy
    }
  }

}
