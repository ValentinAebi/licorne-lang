package compiler.typing.smartcasting.egraphs

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.Formulas.IdValue
import compiler.lang.Operator

import java.util.Objects

sealed trait ENode {
  def operands: List[EClass.Ref]
}

final case class IdValNode(idValue: IdValue) extends ENode {
  override def operands: List[EClass.Ref] = List.empty
}

final case class ConstNode(cst: Any) extends ENode {
  override def operands: List[EClass.Ref] = List.empty
}

final case class UnaryOpNode(op: Operator, operand: EClass.Ref) extends ENode {
  override def operands: List[EClass.Ref] = List(operand)
}

final case class BinaryOpNode(lhs: EClass.Ref, op: Operator, rhs: EClass.Ref) extends ENode {
  override def operands: List[EClass.Ref] = List(lhs, rhs)

  override def equals(that: Any): Boolean = that match {
    case that: BinaryOpNode =>
      this.op == that.op && {
        this.lhs == that.lhs && this.rhs == that.rhs ||
          op.isCommutative && this.lhs == that.rhs && this.rhs == that.lhs
      }
    case _ => false
  }

  override def hashCode(): Int = Objects.hash(op, Set(lhs, rhs))
}

final case class CallNode(receiver: EClass.Ref, funId: FunOrVarId, args: List[EClass.Ref]) extends ENode {
  override def operands: List[EClass.Ref] = receiver :: args
}

final case class SelectNode(receiver: EClass.Ref, fieldId: FunOrVarId) extends ENode {
  override def operands: List[EClass.Ref] = List(receiver)
}

final case class TypePredicateNode(subject: EClass.Ref, tpe: TypeIdentifier) extends ENode {
  override def operands: List[EClass.Ref] = List(subject)
}
