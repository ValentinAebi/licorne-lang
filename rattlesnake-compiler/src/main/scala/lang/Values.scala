package lang

import identifiers.FunOrVarId
import lang.Types.Type

object Values {

  sealed trait Formula
  sealed trait Capturable
  
  sealed trait Value extends Formula

  final class IdValue(uid: Long) extends Value, Capturable {
    override def toString: String = "$" + uid
  }

  sealed trait Constant extends Value {
    def value: Any

    override def toString: String = value.toString
  }

  case object True extends Constant {
    override def value: Any = true
  }
  case object False extends Constant {
    override def value: Any = false
  }
  case object NullPtr extends Constant {
    override def value: Any = null
  }
  final case class IntConstant(value: Int) extends Constant
  final case class DoubleConstant(value: Double) extends Constant
  final case class StringConstant(value: String) extends Constant

  sealed trait BinOp(val operator: Operator) extends Formula {
    def lhs: Formula
    def rhs: Formula

    override def toString: String = s"$lhs $operator $rhs"
  }

  sealed trait UnaryOp(val operator: Operator) extends Formula {
    def operand: Formula
    
    override def toString: String = s"$operator$operand"
  }

  final case class Plus(lhs: Formula, rhs: Formula) extends BinOp(Operator.Plus)
  final case class Minus(lhs: Formula, rhs: Formula) extends BinOp(Operator.Minus)
  final case class Times(lhs: Formula, rhs: Formula) extends BinOp(Operator.Times)
  final case class Div(lhs: Formula, rhs: Formula) extends BinOp(Operator.Div)
  final case class Rem(lhs: Formula, rhs: Formula) extends BinOp(Operator.Modulo)
  final case class Neg(operand: Formula) extends UnaryOp(Operator.Minus)

  final case class And(lhs: Formula, rhs: Formula) extends BinOp(Operator.And)
  final case class Or(lhs: Formula, rhs: Formula) extends BinOp(Operator.Or)
  final case class Not(operand: Formula) extends UnaryOp(Operator.ExclamationMark)

  final case class LessThan(lhs: Formula, rhs: Formula) extends BinOp(Operator.LessThan)
  final case class LessOrEq(lhs: Formula, rhs: Formula) extends BinOp(Operator.LessOrEq)
  final case class Equal(lhs: Formula, rhs: Formula) extends BinOp(Operator.Equality)

  final case class Call(receiver: Formula, funId: FunOrVarId, args: List[Formula]) extends Formula, Capturable {
    override def toString: String = s"$receiver.$funId(${args.mkString(",")})"
  }
  final case class Select(owner: Formula, fieldName: FunOrVarId) extends Formula, Capturable {
    override def toString: String = s"$owner.$fieldName"
  }
  final case class HasType(formula: Formula, tpe: Type) extends Formula {
    override def toString: String = s"$formula is $tpe"
  }

  case object RootCapability extends Capturable {
    override def toString: String = "cap"
  }
  
  extension (formula: Formula) def asCst: Option[Constant] = formula match {
    case cst: Constant => Some(cst)
    case _ => None
  }

}
