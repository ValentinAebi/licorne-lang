package lang

/**
 * Operator or separator
 */
enum Operator(val str: String) {

  case Assig extends Operator("=")

  case Plus extends Operator("+")
  case Minus extends Operator("-")
  case Times extends Operator("*")
  case Div extends Operator("/")
  case Modulo extends Operator("%")
  case Equality extends Operator("==")
  case Inequality extends Operator("!=")
  case LessThan extends Operator("<")
  case LessOrEq extends Operator("<=")
  case GreaterThan extends Operator(">")
  case GreaterOrEq extends Operator(">=")
  case And extends Operator("&&")
  case Or extends Operator("||")

  case ExclamationMark extends Operator("!")

  case Dot extends Operator(".")
  case At extends Operator("@")

  case OpeningParenthesis extends Operator("(")
  case ClosingParenthesis extends Operator(")")
  case OpeningBracket extends Operator("[")
  case ClosingBracket extends Operator("]")
  case OpeningBrace extends Operator("{")
  case ClosingBrace extends Operator("}")

  case Colon extends Operator(":")
  case Semicolon extends Operator(";")
  case Comma extends Operator(",")
  
  case PlusEq extends Operator("+=")
  case MinusEq extends Operator("-=")
  case TimesEq extends Operator("*=")
  case DivEq extends Operator("/=")
  case ModuloEq extends Operator("%=")
  
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

}
