package compiler.io

import scala.util.Try

/**
 * Object able to provide source code (typically a source file)
 */
trait SourceCodeProvider {
  def lines: Try[Seq[String]]
  def name: String
  
  def content: Try[String] = lines.map(_.mkString("\n"))

  override def toString: String = name
}
