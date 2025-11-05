package lang

import identifiers.FunOrVarId

object Values {

  sealed trait Formula
  sealed trait Capturable
  
  sealed trait Value extends Formula

  final class IdValue(uid: Long) extends Value, Capturable {
    override def toString: String = "$" + uid
  }

  case object True extends Value
  case object False extends Value
  case object NullPtr extends Value
  final case class IntConstant(value: Int) extends Value
  final case class DoubleConstant(value: Double) extends Value
  final case class StringConstant(value: String) extends Value

  final case class Plus(lhs: Formula, rhs: Formula) extends Formula
  final case class Minus(lhs: Formula, rhs: Formula) extends Formula
  final case class Times(lhs: Formula, rhs: Formula) extends Formula
  final case class Div(lhs: Formula, rhs: Formula) extends Formula
  final case class Rem(lhs: Formula, rhs: Formula) extends Formula
  final case class Neg(negated: Formula) extends Formula

  final case class And(lhs: Formula, rhs: Formula) extends Formula
  final case class Or(lhs: Formula, rhs: Formula) extends Formula
  final case class Not(negated: Formula) extends Formula

  final case class LessThan(lhs: Formula, rhs: Formula) extends Formula
  final case class LessOrEq(lhs: Formula, rhs: Formula) extends Formula
  final case class Equal(lhs: Formula, rhs: Formula) extends Formula

  final case class Call(receiver: Formula, funId: FunOrVarId, args: List[Formula]) extends Formula, Capturable
  final case class Select(owner: Formula, fieldName: FunOrVarId) extends Formula, Capturable

  case object RootCapability extends Capturable
  
  def formulaIsPure(formula: Formula): Boolean = ???

}
