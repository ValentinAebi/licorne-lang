package lang

import identifiers.FunOrVarId

object Values {

  sealed trait Formula
  sealed trait Capturable

  final class Value(uid: Long) extends Formula, Capturable

  case object True extends Formula
  case object False extends Formula
  case object NullPtr extends Formula
  final case class IntConstant(value: Int) extends Formula
  final case class DoubleConstant(value: Double) extends Formula
  final case class StringConstant(value: String) extends Formula

  final case class Plus(lhs: Formula, rhs: Formula) extends Formula
  final case class Minus(lhs: Formula, rhs: Formula) extends Formula
  final case class Times(lhs: Formula, rhs: Formula) extends Formula
  final case class Div(lhs: Formula, rhs: Formula) extends Formula
  final case class Rem(lhs: Formula, rhs: Formula) extends Formula

  final case class And(lhs: Formula, rhs: Formula) extends Formula
  final case class Or(lhs: Formula, rhs: Formula) extends Formula
  final case class Not(negated: Formula) extends Formula

  final case class LessThan(lhs: Formula, rhs: Formula) extends Formula
  final case class LessOrEq(lhs: Formula, rhs: Formula) extends Formula
  final case class Equal(lhs: Formula, rhs: Formula) extends Formula

  final case class Call(receiver: Formula, funId: FunOrVarId, args: List[Formula]) extends Formula, Capturable
  final case class Select(owner: Formula, fieldName: FunOrVarId) extends Formula, Capturable

  case object RootCapability extends Capturable

}
