package compiler.display

import compiler.identifiers.Identifier
import compiler.lang.Formulas.IdValue
import compiler.lang.Types.Type

import scala.collection.mutable

/**
 * Offers methods for pretty printing, especially for indentation
 */
final class PrettyPrintString(indentUnit: String) {
  require(indentUnit.nonEmpty)

  // currIndentLevel*indentGranularity spaces will be added before each line
  private var currIndentLevel: Int = 0

  // buffer containing the lines, added one by one
  private val lines = new mutable.ListBuffer[String]()

  def indent(action: => Unit): this.type = {
    currIndentLevel += 1
    newLine()
    val _ = action
    currIndentLevel -= 1
    this
  }
  
  def indentln(action: => Unit): this.type = {
    indent(action)
    newLine()
  }

  def block(action: => Unit): this.type = {
    add("{")
    indentln(action)
    add("}")
  }

  def newLine(): this.type = {
    lines.addOne(indentSpaces)
    this
  }

  def add(s: String): this.type = {
    if (s.nonEmpty) {
      val newLines = scala.io.Source.fromString(s).getLines()
      if (newLines.hasNext) {
        if (lines.nonEmpty) {
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

  def addAligned(s: String, alignmentGranularity: Int, padChar: Char = ' ', padIfExact: Boolean = true): this.type = {
    if (lines.nonEmpty) {
      val currLineLen = lines.last.length
      val paddingLen =
        if !padIfExact && currLineLen % alignmentGranularity == 0
        then 0
        else alignmentGranularity - currLineLen % alignmentGranularity
      add(padChar.toString.repeat(paddingLen))
    }
    add(s)
  }

  def addln(s: String): this.type = {
    add(s).newLine()
  }
  
  def add(i: Int): this.type = {
    add(i.toString)
  }
  
  def add(c: Char): this.type = {
    add(c.toString)
  }
  
  def add(l: Long): this.type = {
    add(l.toString)
  }

  def add(identifier: Identifier): this.type = {
    add(identifier.stringId)
  }
  
  def add(tpe: Type): this.type = {
    add(tpe.toString)
  }
  
  def add(idValue: IdValue): this.type = {
    add(idValue.toString)
  }

  def addSpace(): this.type = {
    add(" ")
  }

  def built: String = lines.mkString("\n")

  private def indentSpaces: String = indentUnit * currIndentLevel

}