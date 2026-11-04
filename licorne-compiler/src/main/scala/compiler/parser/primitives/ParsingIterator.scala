package compiler.parser.primitives

import compiler.irs.tokens.Tokens
import compiler.irs.tokens.Tokens.*
import compiler.lang.Keyword.*
import compiler.lang.Operator.*

import scala.util.boundary


final class ParsingIterator private(initTokensList: List[PositionedToken]) {
  require(initTokensList.nonEmpty)
  private var _curr: PositionedToken = PositionedToken(EndlToken, initTokensList.head.position)
  private var _remTokens: List[PositionedToken] = initTokensList.filterNot(_.token.isSpaceOrComment)
  moveForward()

  def current: PositionedToken = _curr

  def moveForward(): PositionedToken = {
    val prev = _curr

    var move = true
    while (move) {
      _remTokens match {
        case Nil =>
          _curr = PositionedToken(EndOfFileToken, _curr.endPosition)
          move = false
        case first :: follow =>
          first.token match {
            case tok if tok.isStatementSep && prev.token.isStatementSep => ()
            case EndlToken if
              prev.token.isClearlyNotStatementEnd || follow.headOption.exists(_.token.isBinop) || !follow.headOption.exists(_.token.isPossibleStatementStart)
            => ()
            case _ =>
              _curr = first
              move = false
          }
          _remTokens = follow
      }
    }

    prev
  }

  def remaining: List[PositionedToken] = _remTokens

  def lookahead(n: Int)(pf: PartialFunction[List[Token], Boolean]): Boolean = {
    require(n >= 1)
    pf.applyOrElse(_curr.token :: _remTokens.take(n-1).map(_.token), _ => false)
  }

  extension (tok: Token) {

    private def isStatementSep: Boolean = tok match {
      case OperatorToken(Semicolon) => true
      case EndlToken => true
      case _ => false
    }

    private def isBinop: Boolean = tok.isOperator(Plus, Minus, Times, Div, Modulo)

    private def isAssig: Boolean = tok.isOperator(Assig, PlusEq, MinusEq, TimesEq, DivEq, ModuloEq, PlusPlusEq)

    private def isClearlyNotStatementEnd: Boolean = isBinop || isAssig || tok.isOperator(Comma, OpeningBrace, OpeningParenthesis, OpeningBracket, RightArrow, Colon)

    private def isPossibleStatementStart: Boolean = tok match {
      case FirstUppercaseIdentifierToken(_) => true
      case FirstLowercaseIdentifierToken(_) => true
      case KeywordToken(It | This | Null | Return | Panic | If | While | For | Val | Var) => true
      case KeywordToken(_) => false
      case OperatorToken(OpeningParenthesis | OpeningBrace) => true
      case OperatorToken(_) => false
      case Tokens.UnitLitToken => true
      case IntLitToken(_) => true
      case DoubleLitToken(_) => true
      case BoolLitToken(_) => true
      case CharLitToken(_) => true
      case StringLitToken(_) => true
      case Tokens.SpaceToken => false
      case Tokens.EndlToken => false
      case ErrorToken(strValue) => false
      case CommentToken(strValue) => false
      case Tokens.EndOfFileToken => false
    }

    private def isSpaceOrComment: Boolean = tok match {
      case CommentToken(_) => true
      case SpaceToken => true
      case _ => false
    }

  }

}

object ParsingIterator {
  def from(tokensSeq: List[PositionedToken]): ParsingIterator = {
    new ParsingIterator(tokensSeq)
  }
}
