package compiler.runners

import compiler.backend.JarFinder
import compiler.gennames.ClassesAndDirectoriesNames.{agentSubdirName, outDirName}
import compiler.identifiers.TypeIdentifier

import java.io.File
import java.nio.file.Path

final class Runner(errorCallback: String => Nothing, workingDirectoryPath: Path) {

  private val classPathsSep =
    if System.getProperty("os.name").startsWith("Windows")
    then ";"
    else ":"

  def runMain(mainClassName: TypeIdentifier, inheritIO: Boolean, programArgs: Array[String]): Process = {
    val outDirPath = workingDirectoryPath.resolve(outDirName)
    ???
  }

  private def findNameOfJarInDir(dir: File, jarNamePrefix: String, errorMsg: String): String = {
    JarFinder.findNameOfJarInDir(dir, jarNamePrefix)
      .getOrElse {
        errorCallback(errorMsg)
      }
  }

}
