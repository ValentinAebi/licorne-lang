package compiler.irs.ssa.egraphs

import compiler.identifiers.FunOrVarId
import compiler.irs.ssa.SSA.IdValue
import compiler.util.SeqSet


sealed trait ENode {
  def subst(target: EClassId, repl: EClassId): ENode
  def children: SeqSet[EClassId]
}

case object TrueNode extends ENode {
  override def subst(target: EClassId, repl: EClassId): ENode = TrueNode

  override def children: SeqSet[EClassId] = SeqSet.empty
}

case object FalseNode extends ENode {
  override def subst(target: EClassId, repl: EClassId): ENode = FalseNode

  override def children: SeqSet[EClassId] = SeqSet.empty
}

final case class IntConstNode(value: Int) extends ENode {
  override def subst(target: EClassId, repl: EClassId): IntConstNode = this

  override def children: SeqSet[EClassId] = SeqSet.empty
}

final case class IdValNode(idVal: IdValue) extends ENode {
  override def subst(target: EClassId, repl: EClassId): IdValNode = this

  override def children: SeqSet[EClassId] = SeqSet.empty
}

final case class SelectNode(owner: EClassId, fieldId: FunOrVarId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): SelectNode =
    SelectNode(owner.subst(target, repl), fieldId)

  override def children: SeqSet[EClassId] = SeqSet(owner)
}

final case class SumNode(children: SeqSet[EClassId]) extends ENode {
  override def subst(target: EClassId, repl: EClassId): ENode =
    SumNode(children.map(_.subst(target, repl)))
}

final case class NegNode(child: EClassId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): ENode =
    NegNode(child.subst(target, repl))

  override def children: SeqSet[EClassId] = SeqSet(child)
}

final case class ProductNode(children: SeqSet[EClassId]) extends ENode {
  override def subst(target: EClassId, repl: EClassId): ENode =
    ProductNode(children.map(_.subst(target, repl)))
}

final case class DivNode(lhs: EClassId, rhs: EClassId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): ENode =
    DivNode(lhs.subst(target, repl), rhs.subst(target, repl))

  override def children: SeqSet[EClassId] = SeqSet(lhs, rhs)
}

final case class RemNode(lhs: EClassId, rhs: EClassId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): ENode =
    RemNode(lhs.subst(target, repl), rhs.subst(target, repl))

  override def children: SeqSet[EClassId] = SeqSet(lhs, rhs)
}

final case class NotNode(operand: EClassId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): ENode =
    NotNode(operand.subst(target, repl))

  override def children: SeqSet[EClassId] = SeqSet(operand)
}

// TODO possible optimization: create a new node only when at least one child differs
extension (classId: EClassId) private inline def subst(inline target: EClassId, inline repl: EClassId): EClassId =
  if classId == target then repl else classId
