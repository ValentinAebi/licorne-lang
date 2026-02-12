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
    val agentSubdirPath = outDirPath.resolve(agentSubdirName)
    val agentJarName = findNameOfJarInDir(agentSubdirPath.toFile, "rattlesnake-agent",
      "Rattlesnake agent not found")
    val runtimeJarName = findNameOfJarInDir(outDirPath.toFile, "rattlesnake-runtime",
      "Rattlesnake runtime not found")
    val agentJarFullPath = agentSubdirPath.resolve(agentJarName).toFile.getCanonicalFile
    val runtimeJarFullPath = outDirPath.resolve(runtimeJarName).toFile.getCanonicalFile
    val processBuilder = new ProcessBuilder()
      .directory(workingDirectoryPath.toFile)
      .command(
        (Array("java",
        "-cp", s"$runtimeJarFullPath$classPathsSep./$outDirName",
        s"-javaagent:$agentJarFullPath",
        mainClassName.stringId) ++ programArgs)*
      )
    if (inheritIO) {
      processBuilder.inheritIO()
    }
    processBuilder.start()
  }

  private def findNameOfJarInDir(dir: File, jarNamePrefix: String, errorMsg: String): String = {
    JarFinder.findNameOfJarInDir(dir, jarNamePrefix)
      .getOrElse {
        errorCallback(errorMsg)
      }
  }

}
