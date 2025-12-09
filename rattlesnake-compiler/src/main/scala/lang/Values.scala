package lang

import identifiers.{FunOrVarId, Identifier, TypeIdentifier}
import lang.Types.Type

object Values {

  sealed trait Formula {
    final override def toString: String = formulaToString(this)(using _ => None)
    def str(using typeFunc: IdValue => Option[Type]): String = formulaToString(this)
  }

  sealed trait Capturable

  sealed trait Value extends Formula

  final case class IdValue(varId: String, idx: Long) extends Value, Capturable

  sealed trait Constant extends Value {
    def value: Any
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
  }

  sealed trait UnaryOp(val operator: Operator) extends Formula {
    def operand: Formula
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

  final case class Call(receiver: Formula, funId: FunOrVarId, typeArgs: List[Type], args: List[Formula]) extends Formula, Capturable

  final case class Select(owner: Formula, fieldName: FunOrVarId) extends Formula, Capturable

  final case class HasType(formula: Formula, tpe: TypeIdentifier) extends Formula

  case object RootCapability extends Capturable {
    override def toString: String = "cap"
  }

  extension (formula: Formula) def asCst: Option[Constant] = formula match {
    case cst: Constant => Some(cst)
    case _ => None
  }

  extension (formula: Formula) def substitute(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Formula = formula match {
    case value: IdValue => valsSubst.getOrElse(value, value)
    case constant: Constant => constant
    case Plus(lhs, rhs) => Plus(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Minus(lhs, rhs) => Minus(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Times(lhs, rhs) => Times(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Div(lhs, rhs) => Div(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Rem(lhs, rhs) => Rem(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case And(lhs, rhs) => And(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Or(lhs, rhs) => Or(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case LessThan(lhs, rhs) => LessThan(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case LessOrEq(lhs, rhs) => LessOrEq(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Equal(lhs, rhs) => Equal(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Neg(operand) => Neg(operand.substitute(typesSubst, valsSubst))
    case Not(operand) => Not(operand.substitute(typesSubst, valsSubst))
    case Call(receiver, funId, typeArgs, args) =>
      Call(receiver.substitute(typesSubst, valsSubst), funId,
        typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(typesSubst, valsSubst)))
    case Select(owner, fieldName) => Select(owner.substitute(typesSubst, valsSubst), fieldName)
    case HasType(formula, tpe) => HasType(formula.substitute(typesSubst, valsSubst), tpe)
  }

  def formulaToString(formula: Formula)(using typeFunc: (IdValue => Option[Type])): String = formula match {
    case idValue: IdValue =>
      val strWithoutType = s"${idValue.varId}$$${idValue.idx}"
      typeFunc(idValue) match {
        case Some(tpe) => s"($strWithoutType : $tpe)"
        case None => strWithoutType
      }
    case StringConstant(value) =>
      s"\"$value\""
    case constant: Constant =>
      constant.value.toString
    case op: BinOp =>
      s"${formulaToString(op.lhs)} ${op.operator} ${formulaToString(op.rhs)}"
    case op: UnaryOp =>
      s"${op.operator} ${formulaToString(op.operand)}"
    case Call(receiver, funId, typeArgs, args) =>
      val typeArgsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      s"${formulaToString(receiver)}.$funId(${args.map(formulaToString).mkString(", ")})"
    case Select(owner, fieldName) =>
      s"${formulaToString(owner)}.$fieldName"
    case HasType(formula, tpe) =>
      s"${formulaToString(formula)} is $tpe"
  }

}
