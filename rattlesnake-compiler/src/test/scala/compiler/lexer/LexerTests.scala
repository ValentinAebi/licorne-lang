package compiler.lexer

import compiler.io.SourceCodeProvider
import compiler.irs.tokens.Tokens.*
import compiler.lang.Keyword.*
import compiler.lang.Operator.*
import compiler.reporting.Errors.{CompilationError, ErrorReporter, ExitCode}
import compiler.reporting.Position
import org.junit.Assert.{assertArrayEquals, assertEquals, assertTrue, fail}
import org.junit.Test

import scala.collection.mutable.ListBuffer
import scala.util.{Success, Try}

class LexerTests {

  @Test
  def tokenizationTest(): Unit = {
    val mockSourceCodeProvider = new SourceCodeProvider {
      override def lines: Try[Seq[String]] = Success(List(
        "fn foo(x: Int): Bar = a(b(x))",
        "val p: T = foo(42)",
        "val s = \"ba\"+'r'"
      ))

      override def name: String = "mock"
    }

    var line = 1
    var col = 1

    def newTok(token: Token): PositionedToken = {
      val posTok = PositionedToken(token, Position(mockSourceCodeProvider, line = line, col = col))
      if token == EndlToken then {
        line += 1
        col = 1
      }
      else {
        col += token.strValue.length
      }
      posTok
    }

    val errorsCollector = ListBuffer.empty[CompilationError | String]
    val errorReporter = ErrorReporter(errorsCollector.addOne, failExit)

    val expectedTokSeq = List(
      KeywordToken(Fn),
      SpaceToken,
      FirstLowercaseIdentifierToken("foo"),
      OperatorToken(OpeningParenthesis),
      FirstLowercaseIdentifierToken("x"),
      OperatorToken(Colon),
      SpaceToken,
      FirstUppercaseIdentifierToken("Int"),
      OperatorToken(ClosingParenthesis),
      OperatorToken(Colon),
      SpaceToken,
      FirstUppercaseIdentifierToken("Bar"),
      SpaceToken,
      OperatorToken(Assig),
      SpaceToken,
      FirstLowercaseIdentifierToken("a"),
      OperatorToken(OpeningParenthesis),
      FirstLowercaseIdentifierToken("b"),
      OperatorToken(OpeningParenthesis),
      FirstLowercaseIdentifierToken("x"),
      OperatorToken(ClosingParenthesis),
      OperatorToken(ClosingParenthesis),
      EndlToken,
      KeywordToken(Val),
      SpaceToken,
      FirstLowercaseIdentifierToken("p"),
      OperatorToken(Colon),
      SpaceToken,
      FirstUppercaseIdentifierToken("T"),
      SpaceToken,
      OperatorToken(Assig),
      SpaceToken,
      FirstLowercaseIdentifierToken("foo"),
      OperatorToken(OpeningParenthesis),
      IntLitToken(42),
      OperatorToken(ClosingParenthesis),
      EndlToken,
      KeywordToken(Val),
      SpaceToken,
      FirstLowercaseIdentifierToken("s"),
      SpaceToken,
      OperatorToken(Assig),
      SpaceToken,
      StringLitToken("ba"),
      OperatorToken(Plus),
      CharLitToken('r'),
      EndlToken
    ).map(newTok)
    val actualTokSeq = Lexer(errorReporter)(mockSourceCodeProvider)._1
    assertEquals(expectedTokSeq, actualTokSeq)
    errorReporter.displayErrors()
    assertTrue(errorReporter.errorsCnt == 0)
    // consistency
    assertTrue(errorsCollector.size == errorReporter.errorsCnt + 1)
  }

  private def failExit(exitCode: ExitCode): Nothing = {
    fail(s"exit called, exit code: $exitCode")
    throw new AssertionError("cannot happen")
  }


}
