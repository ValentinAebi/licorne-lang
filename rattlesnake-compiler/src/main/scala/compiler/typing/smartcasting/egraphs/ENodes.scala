package compiler.typing.smartcasting.egraphs

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.Formulas.IdValue
import compiler.lang.Operator

import java.util.Objects

sealed trait ENode {
  def operands: List[EClass]
}

final case class IdValNode(idValue: IdValue) extends ENode {
  override def operands: List[EClass] = List.empty

  override def toString: String = idValue.toString
}

final case class ConstNode(cst: Any) extends ENode {
  override def operands: List[EClass] = List.empty

  override def toString: String = cst.toString
}

final case class UnaryOpNode(op: Operator, var operand: EClass) extends ENode {
  override def operands: List[EClass] = List(operand)

  override def toString: String = s"$op(${operand.shortDescr})"
}

final case class BinaryOpNode(var lhs: EClass, op: Operator, var rhs: EClass) extends ENode {
  override def operands: List[EClass] = List(lhs, rhs)

  override def equals(that: Any): Boolean = that match {
    case that: BinaryOpNode =>
      this.op == that.op && {
        this.lhs == that.lhs && this.rhs == that.rhs ||
          op.isCommutative && this.lhs == that.rhs && this.rhs == that.lhs
      }
    case _ => false
  }

  override def hashCode(): Int = Objects.hash(op, Set(lhs, rhs))

  override def toString: String = s"$op(${lhs.shortDescr},${rhs.shortDescr})"
}

final case class CallNode(var receiver: EClass, funId: FunOrVarId, var args: List[EClass]) extends ENode {
  override def operands: List[EClass] = receiver :: args

  override def toString: String = s"${receiver.shortDescr}.$funId" ++ args.map(_.shortDescr).mkString("(", ",", ")")
}

final case class SelectNode(var receiver: EClass, fieldId: FunOrVarId) extends ENode {
  override def operands: List[EClass] = List(receiver)

  override def toString: String = s"${receiver.shortDescr}.$fieldId"
}

final case class TypePredicateNode(var subject: EClass, tpe: TypeIdentifier) extends ENode {
  override def operands: List[EClass] = List(subject)

  override def toString: String = s"${subject.shortDescr}-is-$tpe"
}
