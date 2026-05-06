package compiler.parser

import compiler.irs.asts.Asts.{BinaryOp, Expr}
import compiler.irs.tokens.Tokens.OperatorToken
import compiler.lang.Operator
import compiler.parser.ParseTree.^:
import compiler.parser.TreeParsers.*
import compiler.reporting.Errors.ErrorReporter

import scala.annotation.tailrec

object BinaryOperatorsParser {

  private def op(operators: List[Operator])(implicit errorReporter: ErrorReporter): FinalTreeParser[Operator] = {
    val descr = s"operator(s) ${operators.mkString(",")}"
    treeParser(descr) {
      case OperatorToken(operator) if operators.contains(operator) => operator
    } setName descr
  }

  /**
   * Builds a parser for expressions using the given operators, respecting their precedence
   * @param operand parser accepting the operands of the expressions that the resulting parser should admit
   */
  def buildFrom(operatorsByDecreasingPrecedence: List[List[Operator]], operand: AnyTreeParser[Expr])
               (implicit errorReporter: ErrorReporter): AnyTreeParser[Expr] = {

    @tailrec
    def recurse(currOperand: AnyTreeParser[Expr], remainingOps: List[List[Operator]], priorityLevel: Int)
               (implicit errorReporter: ErrorReporter): AnyTreeParser[Expr] = {
      remainingOps match {
        case Nil => currOperand
        case headOps :: tailOps =>
          val newParser = {
            currOperand ::: repeat(op(headOps) ::: currOperand) map {
              case leftOperand ^: Nil => leftOperand
              case leftOperand ^: opSeq =>
                opSeq.foldLeft(leftOperand) {
                  (left, opAndRight) => BinaryOp(left, opAndRight.left, opAndRight.right)
                }
            }
          }
          newParser.setName(s"priority $priorityLevel expression")
          recurse(newParser, tailOps, priorityLevel - 1)
      }
    }

    recurse(operand, operatorsByDecreasingPrecedence, priorityLevel = operatorsByDecreasingPrecedence.size)
  }

}
