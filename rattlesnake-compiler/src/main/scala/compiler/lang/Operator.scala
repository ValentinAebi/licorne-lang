package compiler.lang

import Operator.Precedence
import Operator.Precedence.{Add, Comparison, Mul}

/**
 * Operator or separator
 */
enum Operator(val str: String, val precedenceLevelOpt: Option[Precedence], val isCommutative: Boolean = false) {

  case Assig extends Operator("=", None)

  case Plus extends Operator("+", Some(Precedence.Add), isCommutative = true)
  case Minus extends Operator("-", Some(Precedence.Add))
  case Times extends Operator("*", Some(Precedence.Mul), isCommutative = true)
  case Div extends Operator("/", Some(Precedence.Mul))
  case Modulo extends Operator("%", Some(Precedence.Mul))
  case Equality extends Operator("==", Some(Precedence.Comparison), isCommutative = true)
  case Inequality extends Operator("!=", Some(Precedence.Comparison), isCommutative = true)
  case LessThan extends Operator("<", Some(Precedence.Comparison))
  case LessOrEq extends Operator("<=", Some(Precedence.Comparison))
  case GreaterThan extends Operator(">", Some(Precedence.Comparison))
  case GreaterOrEq extends Operator(">=", Some(Precedence.Comparison))
  case And extends Operator("&&", Some(Precedence.And), isCommutative = true)
  case Or extends Operator("||", Some(Precedence.Or), isCommutative = true)

  case ExclamationMark extends Operator("!", None)

  case Dot extends Operator(".", None)

  case OpeningParenthesis extends Operator("(", None)
  case ClosingParenthesis extends Operator(")", None)
  case OpeningBracket extends Operator("[", None)
  case ClosingBracket extends Operator("]", None)
  case OpeningBrace extends Operator("{", None)
  case ClosingBrace extends Operator("}", None)

  case Colon extends Operator(":", None)
  case Semicolon extends Operator(";", None)
  case Comma extends Operator(",", None)
  
  case PlusEq extends Operator("+=", None)
  case MinusEq extends Operator("-=", None)
  case TimesEq extends Operator("*=", None)
  case DivEq extends Operator("/=", None)
  case ModuloEq extends Operator("%=", None)
  
  def isNamedOperator: Boolean = str.forall(_.isLetter)

  override def toString: String = str
}

object Operator {

  val operatorsByPriorityDecreasing: List[List[Operator]] = List(
    List(Times, Div, Modulo),
    List(Plus, Minus),
    List(GreaterThan, LessThan, GreaterOrEq, LessOrEq),
    List(Equality, Inequality),
    List(And),
    List(Or)
  )

  val priorities: Map[Operator, Int] = {
    val size = operatorsByPriorityDecreasing.size
    operatorsByPriorityDecreasing.flatten
      .map { op =>
        val subList = operatorsByPriorityDecreasing.find(_.contains(op)).get
        val idx = operatorsByPriorityDecreasing.indexOf(subList)
        val priority = size - idx
        (op, priority)
      }
      .toMap
  }
  
  enum Precedence {
    case Mul, Add, Comparison, And, Or
  }

}
