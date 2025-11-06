package lang

import identifiers.FunOrVarId

object Values {

  sealed trait Formula
  sealed trait Capturable
  
  sealed trait Value extends Formula

  final class IdValue(uid: Long) extends Value, Capturable {
    override def toString: String = "$" + uid
  }

  sealed trait Constant extends Value

  case object True extends Constant
  case object False extends Constant
  case object NullPtr extends Constant
  final case class IntConstant(value: Int) extends Constant
  final case class DoubleConstant(value: Double) extends Constant
  final case class StringConstant(value: String) extends Constant

  sealed trait BinOp extends Formula {
    def lhs: Formula
    def rhs: Formula
  }

  sealed trait UnaryOp extends Formula {
    def operand: Formula
  }

  final case class Plus(lhs: Formula, rhs: Formula) extends BinOp
  final case class Minus(lhs: Formula, rhs: Formula) extends BinOp
  final case class Times(lhs: Formula, rhs: Formula) extends BinOp
  final case class Div(lhs: Formula, rhs: Formula) extends BinOp
  final case class Rem(lhs: Formula, rhs: Formula) extends BinOp
  final case class Neg(operand: Formula) extends UnaryOp

  final case class And(lhs: Formula, rhs: Formula) extends BinOp
  final case class Or(lhs: Formula, rhs: Formula) extends BinOp
  final case class Not(operand: Formula) extends UnaryOp

  final case class LessThan(lhs: Formula, rhs: Formula) extends BinOp
  final case class LessOrEq(lhs: Formula, rhs: Formula) extends BinOp
  final case class Equal(lhs: Formula, rhs: Formula) extends BinOp

  final case class Call(receiver: Formula, funId: FunOrVarId, args: List[Formula]) extends Formula, Capturable
  final case class Select(owner: Formula, fieldName: FunOrVarId) extends Formula, Capturable

  case object RootCapability extends Capturable

  extension (formula: Formula) def isPureSyntactically: Boolean = formula match {
    case value: Value => true
    case _ : Div | Rem => false
    case op: BinOp => op.lhs.isPureSyntactically && op.rhs.isPureSyntactically
    case op: UnaryOp => op.operand.isPureSyntactically
    case Call(receiver, funId, args) => false
    case Select(owner, fieldName) => owner.isPureSyntactically
  }

}
