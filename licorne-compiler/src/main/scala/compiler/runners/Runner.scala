package compiler.runners

import java.io.File
import java.nio.file.Path

final class Runner(errorCallback: String => Nothing, outDir: Path) {

  private val classPathsSep =
    if System.getProperty("os.name").startsWith("Windows")
    then ";"
    else ":"

  def runMain(mainClassName: String, inheritIO: Boolean, programArgs: Array[String]): Process = {
    val processBuilder = new ProcessBuilder()
      .directory(outDir.toFile)
      .command((Array("java", mainClassName) ++ programArgs) *)
    if (inheritIO) {
      processBuilder.inheritIO()
    }
    processBuilder.start()
  }

}
