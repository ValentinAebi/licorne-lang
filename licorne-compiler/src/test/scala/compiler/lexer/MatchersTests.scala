package compiler.lexer

import compiler.lexer.Matchers.*
import org.junit.Assert.{assertEquals, fail}
import org.junit.Test

class MatchersTests {
  
  @Test
  def simpleTest(): Unit = {
    performTest(
      matcher = char('(') ++ string(_.isDigit) ++ char(')'),
      input = "(175)215a",
      expectedIdx = 5
    )
  }

  @Test
  def testOptTaken(): Unit = {
    performTest(
      matcher = string(_.isLetterOrDigit) ++ char('_') ++ opt(char('(') ++ string(_.isLetter) ++ char(')')) ++ char('#'),
      input = "a12C415U9210_(KwtzTRu)#akzw51",
      expectedIdx = "a12C415U9210_(KwtzTRu)#".length
    )
  }

  @Test
  def testOptNotTaken(): Unit = {
    performTest(
      matcher = string(_.isLetterOrDigit) ++ char('_') ++ opt(char('(') ++ string(_.isLetter) ++ char(')')) ++ char('#'),
      input = "a12C415U9210_#akzw51",
      expectedIdx = "a12C415U9210_#".length
    )
  }

  @Test
  def noMatchTest(): Unit = {
    val matcher = string(_.isDigit) ++ string(_.isLetter) ++ string(_.isDigit)
    performTest(
      matcher = matcher,
      input = "12345abcd",
      expectedIdx = None
    )
  }
  
  def performTest(matcher: Matcher, input: String, expectedIdx: Option[Int]): Unit = {
    val actualIdx = matcher.matches(input)
    assertEquals(expectedIdx, actualIdx)
  }

  def performTest(matcher: Matcher, input: String, expectedIdx: Int): Unit = {
    performTest(matcher, input, Some(expectedIdx))
  }

}
