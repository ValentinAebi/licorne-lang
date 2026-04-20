package compiler.typing.smartcasting.egraphs

final class EGraphCopier {

  private type Copier[T] = java.util.IdentityHashMap[T, T]

  private val classCopier = new Copier[EClass]()
  private val nodeCopier = new Copier[ENode]()

  private def copyOf(original: EGraph): EGraph = {
    val copy = EGraph(original.currentClId)
    copy.initializeWith(
      original.uf.iterator.map((cl1, cl2) => (copyOf(cl1), copyOf(cl2))),
      original.nodeToClassMap.iterator.map((n, cl) => (copyOf(n), copyOf(cl)))
    )
    copy
  }

  private def copyOf(original: EClass): EClass = {
    if classCopier.containsKey(original) then classCopier.get(original)
    else {
      val copy = EClass(original.uid)
      classCopier.put(original, copy)
      copy.initializeWith(
        original.nodesView.iterator.map(copyOf),
        original.getSmartcastType,
        original.explicitFormulasView
      )
      copy
    }
  }

  private def copyOf(original: ENode): ENode = {
    if nodeCopier.containsKey(original) then nodeCopier.get(original)
    else {
      original match {
        case idValNode: IdValNode => idValNode
        case cstNode: ConstNode => cstNode
        case UnaryOpNode(op, operand) =>
          val copy = UnaryOpNode(op, null)
          nodeCopier.put(original, copy)
          copy.operand = copyOf(operand)
          copy
        case BinaryOpNode(lhs, op, rhs) =>
          val copy = BinaryOpNode(null, op, null)
          nodeCopier.put(original, copy)
          copy.lhs = copyOf(lhs)
          copy.rhs = copyOf(rhs)
          copy
        case CallNode(receiver, funId, args) =>
          val copy = CallNode(null, funId, null)
          nodeCopier.put(original, copy)
          copy.receiver = copyOf(receiver)
          copy.args = args.map(copyOf)
          copy
        case SelectNode(receiver, fieldId) =>
          val copy = SelectNode(null, fieldId)
          nodeCopier.put(original, copy)
          copy.receiver = copyOf(receiver)
          copy
        case TypePredicateNode(subject, tpe) =>
          val copy = TypePredicateNode(null, tpe)
          nodeCopier.put(original, copy)
          copy.subject = copyOf(subject)
          copy
      }
    }
  }

}

object EGraphCopier {
  
  def copyOf(eg: EGraph): EGraph =
    (new EGraphCopier).copyOf(eg)
  
}
