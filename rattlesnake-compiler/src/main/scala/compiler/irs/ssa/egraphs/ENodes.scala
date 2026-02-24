package compiler.irs.ssa.egraphs

import compiler.identifiers.FunOrVarId
import compiler.irs.ssa.SSA.IdValue
import compiler.util.SeqSet


sealed trait ENode {
  def subst(target: EClassId, repl: EClassId): Unit
  def children: SeqSet[EClassId]
}

sealed trait ConstNode extends ENode {
  def compareTo(that: ConstNode): ConstNode.ComparisonResult
}

object ConstNode {
  
  enum ComparisonResult {
    case Lt
    case Eq
    case Gt
    case NotComparable

    def mayBeLessOrEq: Boolean = this == Lt || this == Eq

    def mayBeGreaterOrEq: Boolean = this == Gt || this == Eq

    def areEqual: Boolean = this == Eq

    def areDifferent: Boolean = this == Lt || this == Gt
  }
}

case object TrueNode extends ConstNode {
  override def subst(target: EClassId, repl: EClassId): ENode = TrueNode

  override def children: SeqSet[EClassId] = SeqSet.empty

  override def compareTo(that: ConstNode): ConstNode.ComparisonResult = {
    import ConstNode.ComparisonResult.*
    that match {
      case TrueNode => Eq
      case FalseNode => Gt
      case _ => NotComparable
    }
  }
}

case object FalseNode extends ConstNode {
  override def subst(target: EClassId, repl: EClassId): Unit = ()

  override def children: SeqSet[EClassId] = SeqSet.empty

  override def compareTo(that: ConstNode): ConstNode.ComparisonResult = {
    import ConstNode.ComparisonResult.*
    that match {
      case TrueNode => Lt
      case FalseNode => Eq
      case _ => NotComparable
    }
  }
}

final case class IntConstNode(value: Int) extends ConstNode {
  override def subst(target: EClassId, repl: EClassId): Unit = ()

  override def children: SeqSet[EClassId] = SeqSet.empty

  override def compareTo(that: ConstNode): ConstNode.ComparisonResult = {
    import ConstNode.ComparisonResult.*
    import this.value as l
    that match {
      case IntConstNode(r) =>
        if l < r then Lt
        else if l == r then Eq
        else Gt
      case _ => NotComparable
    }
  }
}

final case class StringConstNode(value: String) extends ConstNode {

  override def subst(target: EClassId, repl: EClassId): Unit = ()

  override def children: SeqSet[EClassId] = SeqSet.empty

  override def compareTo(that: ConstNode): ConstNode.ComparisonResult =
    ConstNode.ComparisonResult.NotComparable
}

final case class IdValNode(idVal: IdValue) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = ()

  override def children: SeqSet[EClassId] = SeqSet.empty
}

final case class SelectNode(var owner: EClassId, fieldId: FunOrVarId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = {
    owner = owner.subst(target, repl)
  }

  override def children: SeqSet[EClassId] = SeqSet(owner)
}

final case class SumNode(var children: SeqSet[EClassId]) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = {
    children = children.map(_.subst(target, repl))
  }
}

object SumNode {
  def apply(children: EClassId*): SumNode =
    new SumNode(SeqSet(children))
}

final case class NegNode(var child: EClassId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = {
    child = child.subst(target, repl)
  }

  override def children: SeqSet[EClassId] = SeqSet(child)
}

final case class ProductNode(var children: SeqSet[EClassId]) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = {
    children = children.map(_.subst(target, repl))
  }
}

object ProductNode {
  def apply(children: EClassId*): ProductNode =
    new ProductNode(SeqSet(children))
}

final case class DivNode(var lhs: EClassId, var rhs: EClassId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = {
    lhs = lhs.subst(target, repl)
    rhs = rhs.subst(target, repl)
  }

  override def children: SeqSet[EClassId] = SeqSet(lhs, rhs)
}

final case class RemNode(var lhs: EClassId, var rhs: EClassId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = {
    lhs = lhs.subst(target, repl)
    rhs = rhs.subst(target, repl)
  }

  override def children: SeqSet[EClassId] = SeqSet(lhs, rhs)
}

final case class NotNode(var operand: EClassId) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = {
    operand = operand.subst(target, repl)
  }

  override def children: SeqSet[EClassId] = SeqSet(operand)
}

extension (classId: EClassId) private inline def subst(inline target: EClassId, inline repl: EClassId): EClassId =
  if classId == target then repl else classId
