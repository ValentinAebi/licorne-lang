package compiler.irs

import compiler.reporting.Position
import lang.Types.PrimitiveType
import lang.{Keyword, Operator}

object Tokens {

  /**
   * Token along with its position
   */
  final case class PositionedToken(token: Token, position: Position){
    def endPosition: Position = position.shiftedRightOf(token.strValue.length)
  }

  sealed trait Token {
    def strValue: String
    final def show: String = s"[$strValue]"
  }

  /**
   * Identifier starting with an uppercase
   */
  final case class FirstUppercaseIdentifierToken(strValue: String) extends Token

  /**
   * Identifier starting with a lowercase
   */
  final case class FirstLowercaseIdentifierToken(strValue: String) extends Token
  
  final case class KeywordToken(keyword: Keyword) extends Token {
    override def strValue: String = keyword.str
  }
  final case class OperatorToken(operator: Operator) extends Token {
    override def strValue: String = operator.str
  }

  final case class IntLitToken(value: Int) extends Token {
    override def strValue: String = value.toString
  }
  final case class DoubleLitToken(value: Double) extends Token {
    override def strValue: String = value.toString
  }
  final case class BoolLitToken(value: Boolean) extends Token {
    override def strValue: String = value.toString
  }
  final case class CharLitToken(value: Char) extends Token {
    override def strValue: String = s"'$value'"
  }
  final case class StringLitToken(value: String) extends Token {
    override def strValue: String = s"\"$value\""
  }

  case object SpaceToken extends Token {
    override def strValue: String = " "
  }
  case object EndlToken extends Token {
    override def strValue: String = "<endl>"
  }
  
  final case class ErrorToken(strValue: String) extends Token
  
  final case class CommentToken(strValue: String) extends Token

  case object EndOfFileToken extends Token {
    override def strValue: String = "<file-end>"
  }

}
