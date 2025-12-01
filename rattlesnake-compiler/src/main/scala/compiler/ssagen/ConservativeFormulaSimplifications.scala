package compiler.ssagen

import lang.Values.*

object ConservativeFormulaSimplifications {

  def not(operand: Formula): Formula = operand match {
    case True => False
    case False => True
    case _ => Not(operand)
  }

  def neg(operand: Formula): Formula = operand match {
    case IntConstant(opVal) => IntConstant(-opVal)
    // TODO types other than Int
    case _ => Neg(operand)
  }

  def plus(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => IntConstant(lv + rv)
    case (l, IntConstant(0)) => l
    case (IntConstant(0), r) => r
    // TODO types other than Int
    case _ => Plus(l, r)
  }

  def minus(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => IntConstant(lv - rv)
    case (l, IntConstant(0)) => l
    case (IntConstant(0), r) => neg(r)
    // TODO types other than Int
    case _ => Minus(l, r)
  }

  def times(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => IntConstant(lv * rv)
    // TODO types other than Int
    case _ => Times(l, r)
  }

  def div(l: Formula, r: Formula): Formula = Div(l, r)

  def rem(l: Formula, r: Formula): Formula = Rem(l, r)

  def lessThan(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => if lv < rv then True else False
    // TODO types other than Int
    case _ => LessThan(l, r)
  }

  def lessOrEq(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => if lv <= rv then True else False
    // TODO types other than Int
    case _ => LessOrEq(l, r)
  }

  def equal(l: Formula, r: Formula): Formula = (l, r) match {
    case (l: Constant, r: Constant) => if l == r then True else False
    // TODO types other than Int
    case _ => Equal(l, r)
  }

  def and(l: Formula, r: Formula): Formula = (l, r) match {
    case (True, r) => r
    case (l, True) => l
    case _ => And(l, r)
  }

  def or(l: Formula, r: Formula): Formula = (l, r) match {
    case (False, r) => r
    case (l, False) => l
    case _ => Or(l, r)
  }

}
