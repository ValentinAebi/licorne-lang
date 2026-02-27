package compiler.egraphs

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.Formulas.IdValue
import compiler.lang.Types.Type
import compiler.util.SeqSet

import scala.compiletime.uninitialized


sealed abstract class ENode {
  def subst(target: EClassId, repl: EClassId): Unit
  def children: SeqSet[EClassId]
  
  def deepCopy: ENode
  
  var classId: EClassId = uninitialized
}

sealed trait ConstNode extends ENode {
  def compareTo(that: ConstNode): ConstNode.ComparisonResult

  override def deepCopy: ENode = this

  override def subst(target: EClassId, repl: EClassId): Unit = ()

  override def children: SeqSet[EClassId] = SeqSet.empty
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
  override def compareTo(that: ConstNode): ConstNode.ComparisonResult =
    ConstNode.ComparisonResult.NotComparable
}

case object FalseNode extends ConstNode {
  override def compareTo(that: ConstNode): ConstNode.ComparisonResult =
    ConstNode.ComparisonResult.NotComparable
}

final case class IntConstNode(value: Int) extends ConstNode {
  override def subst(target: EClassId, repl: EClassId): Unit = ()

  override def children: SeqSet[EClassId] = SeqSet.empty

  override def compareTo(that: ConstNode): ConstNode.ComparisonResult = {
    import ConstNode.ComparisonResult.*
    val l = this.value
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

  override def deepCopy: ENode = this

  override def children: SeqSet[EClassId] = SeqSet.empty
}

sealed abstract class UnopNode extends ENode {
  var operand: EClassId

  override def subst(target: EClassId, repl: EClassId): Unit = {
    operand = operand.subst(target, repl)
  }

  override def children: SeqSet[EClassId] = SeqSet(operand)
}

sealed abstract class BinopNode extends ENode {
  var lhs: EClassId
  var rhs: EClassId

  override def subst(target: EClassId, repl: EClassId): Unit = {
    lhs = lhs.subst(target, repl)
    rhs = rhs.subst(target, repl)
  }

  override def children: SeqSet[EClassId] = SeqSet(lhs, rhs)
}

final case class SelectNode(var operand: EClassId, fieldId: FunOrVarId) extends UnopNode {
  override def deepCopy: ENode = copy()
}

final case class SumNode(var children: SeqSet[EClassId]) extends ENode {
  override def subst(target: EClassId, repl: EClassId): Unit = {
    children = children.map(_.subst(target, repl))
  }
  
  override def deepCopy: ENode = copy()
}

object SumNode {
  def apply(children: EClassId*): SumNode =
    new SumNode(SeqSet(children))
}

final case class NegNode(var operand: EClassId) extends UnopNode {
  override def deepCopy: ENode = copy()
}

final case class ProductNode(var children: SeqSet[EClassId]) extends ENode {
  
  override def subst(target: EClassId, repl: EClassId): Unit = {
    children = children.map(_.subst(target, repl))
  }

  override def deepCopy: ENode = copy()
}

object ProductNode {
  def apply(children: EClassId*): ProductNode =
    new ProductNode(SeqSet(children))
}

final case class DivNode(var lhs: EClassId, var rhs: EClassId) extends BinopNode {
  override def deepCopy: ENode = copy()
}

final case class RemNode(var lhs: EClassId, var rhs: EClassId) extends BinopNode {
  override def deepCopy: ENode = copy()
}

final case class NotNode(var operand: EClassId) extends UnopNode {
  override def deepCopy: ENode = copy()
}

final case class EqualityNode(var lhs: EClassId, var rhs: EClassId) extends BinopNode {
  override def deepCopy: ENode = copy()
}

final case class LessOrEqNode(var lhs: EClassId, var rhs: EClassId) extends BinopNode {
  override def deepCopy: ENode = copy()
}

final case class LessThanNode(var lhs: EClassId, var rhs: EClassId) extends BinopNode {
  override def deepCopy: ENode = copy()
}

final case class AndNode(var lhs: EClassId, var rhs: EClassId) extends BinopNode {
  override def deepCopy: ENode = copy()
}

final case class OrNode(var lhs: EClassId, var rhs: EClassId) extends BinopNode {
  override def deepCopy: ENode = copy()
}

final case class TypeTestNode(var operand: EClassId, tpe: TypeIdentifier) extends UnopNode {
  override def deepCopy: ENode = copy()
}

extension (inline classId: EClassId) private inline def subst(inline target: EClassId, inline repl: EClassId): EClassId =
  if classId == target then repl else classId
