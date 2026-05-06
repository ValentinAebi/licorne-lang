package compiler

import java.io.File
import java.nio.file.Path

object TestRuntimePaths {

  private val licorneRootDir =
    new File("")
      .getCanonicalFile
      .getParentFile
      .toPath

  val jarsDir: Path = licorneRootDir.resolve("jars")
  
}
