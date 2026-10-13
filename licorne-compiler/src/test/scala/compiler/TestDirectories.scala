package compiler

import compiler.gennames.FileExtensions
import compiler.io.SourceFile

import java.io.File
import java.nio.file.{Files, Path, Paths}

object TestDirectories {

  private val licorneRootDir =
    new File("")
      .getCanonicalFile
      .getParentFile
      .toPath

  val jarsDir: Path = licorneRootDir.resolve("jars")

  val stdLibRootPath: Path = Paths.get("../licorne-stdlib")

  def loadStdLib(): Array[SourceFile] = {
    Files.walk(stdLibRootPath)
      .map(_.toAbsolutePath.toString)
      .filter(_.endsWith(FileExtensions.dot(_.licorne)))
      .toArray(new Array[String](_))
      .map(SourceFile(_))
  }
}
