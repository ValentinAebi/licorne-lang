package compiler.io

import compiler.gennames.FileExtensions

import scala.util.{Try, Using}

final case class SourceFile(path: String, isStdLib: Boolean = false) extends SourceCodeProvider {
  require(path.endsWith(FileExtensions.licorne))

  override def name: String = path

  override def lines: Try[Seq[String]] = {
    Using(scala.io.Source.fromFile(path)) { bufSrc =>
      bufSrc.getLines().toSeq
    }
  }

}
