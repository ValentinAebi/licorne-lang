package compiler.parser

import compiler.irs.Tokens.*
import compiler.lang.Operator.Semicolon

import scala.compiletime.uninitialized

/**
 * Iterator allowing at most one lookahead
 */
final class LL1Iterator private(initTokensList: List[PositionedToken]) {
  require(initTokensList.nonEmpty)
  private var _curr: PositionedToken = uninitialized
  private var _remTokens: List[PositionedToken] = initTokensList
  moveForward()

  def current: PositionedToken = _curr

  def moveForward(): PositionedToken = {

    // save previous
    val prev = _curr

    val next = _remTokens.headOption.getOrElse(PositionedToken(EndOfFileToken, prev.endPosition))

    // move iterator
    _curr = next
    _remTokens = if _remTokens.nonEmpty then _remTokens.tail else Nil

    // ignore multiple semicolons and line breaks
    if (_curr.token == OperatorToken(Semicolon) || _curr.token == EndlToken) {
      _remTokens = _remTokens.dropWhile(posTok => posTok.token == OperatorToken(Semicolon) || posTok.token == EndlToken)
    }

    // ignore spaces, comments and line breaks
    if (_curr.token == SpaceToken || _curr.token.isInstanceOf[CommentToken] || _curr.token == EndlToken) {
      moveForward()
    }

    prev
  }

  def remaining: List[PositionedToken] = _remTokens

}

object LL1Iterator {
  def from(tokensSeq: List[PositionedToken]): LL1Iterator = {
    new LL1Iterator(tokensSeq)
  }
}
