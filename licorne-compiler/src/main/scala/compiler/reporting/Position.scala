package compiler.reporting

import compiler.io.SourceCodeProvider

/**
 * Position in a source (typically a source file)
 *
 * Ordered according to lexicographic ordering of srcCodeProviderName, then line, and finally column
 */
final case class Position(srcCodeProviderName: String, line: Int, col: Int) extends Ordered[Position] {
  require(srcCodeProviderName != null)
  require(line >= 1)
  require(col >= 1)
  
  private var isStdLibFlag: Boolean = false
  
  def isStdLib: Boolean = isStdLibFlag
  
  def raiseStdLibFlag(): Unit = {
    isStdLibFlag = true
  }
  
  def shiftedRightOf(n: Int): Position = copy(col = col + n)


  override def compare(that: Position): Int = {
    val fileNamesComp = this.srcCodeProviderName.compareTo(that.srcCodeProviderName)
    val lineComp = this.line.compareTo(that.line)
    val colComp = this.col.compareTo(that.col)
    if fileNamesComp != 0 then fileNamesComp
    else if lineComp != 0 then lineComp
    else colComp
  }
  
  def lineColonColumn: String = s"$line:$col"

  override def toString: String = s"$srcCodeProviderName:$lineColonColumn"

}

object Position {

  def apply(srcCodeProvider: SourceCodeProvider, line: Int, col: Int, isStdLib: Boolean): Position = {
    val pos = new Position(srcCodeProvider.name, line, col)
    if (isStdLib) {
      pos.raiseStdLibFlag()
    }
    pos
  }

}
