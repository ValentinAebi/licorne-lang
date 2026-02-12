package compiler.ssaprinting

import compiler.identifiers.Identifier
import scala.collection.mutable

/**
 * Offers methods for pretty printing, especially for indentation
 */
final class PrettyPrintString(indentGranularity: Int) {
  require(indentGranularity > 0)

  // currIndentLevel*indentGranularity spaces will be added before each line
  private var currIndentLevel: Int = 0

  // buffer containing the lines, added one by one
  private val lines = new mutable.ListBuffer[String]()

  def incrementIndent(): PrettyPrintString = {
    currIndentLevel += 1
    this
  }

  def decrementIndent(): PrettyPrintString = {
    currIndentLevel -= 1
    this
  }

  def newLine(): PrettyPrintString = {
    lines.addOne(indentSpaces)
    this
  }

  def add(s: String): PrettyPrintString = {
    if (s.nonEmpty){
      val newLines = scala.io.Source.fromString(s).getLines()
      if (newLines.hasNext) {
        if (lines.nonEmpty){
          val lastLineIdx = lines.size - 1
          lines.update(lastLineIdx, lines(lastLineIdx) ++ newLines.next())
        }
        else {
          lines.addOne(newLines.next())
        }
      }
      lines.addAll(newLines.map(indentSpaces ++ _))
    }
    this
  }

  def add(identifier: Identifier): PrettyPrintString = {
    add(identifier.stringId)
  }

  def startBlock(): PrettyPrintString = {
    add("{")
    incrementIndent()
    newLine()
  }

  def endBlock(): PrettyPrintString = {
    decrementIndent()
    newLine()
    add("}")
    this
  }

  def addSpace(): PrettyPrintString = {
    add(" ")
    this
  }

  def built: String = lines.mkString("\n")

  private def indentSpaces: String = " ".repeat(indentGranularity * currIndentLevel)

}