package compiler

import compiler.ExecutionTests.*
import compiler.gennames.FileExtensions
import compiler.io.SourceFile
import compiler.pipeline.TasksPipelines
import compiler.reasoning.ArithIntMode
import compiler.reporting.Errors.ErrorReporter
import compiler.runners.Runner
import org.junit.Assert.{assertEquals, assertNotEquals, assertTrue, fail}
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters

import java.io.InputStream
import java.nio.file.{Files, Path, Paths}
import java.util.Comparator
import scala.io.Source
import scala.util.Using


object ExecutionTests {

  private val rootPathStr: String = "./src/test/res/execution-tests/"
  private val stdoutFileName: String = "stdout.exp"
  private val stderrFileName: String = "stderr.exp"
  private val stacktraceFileName: String = "error-trace.exp"
  private val testOutSubdirName: String = "testout"
  private val stackTraceCommentMarker = "//>STACKTRACE"

  @Parameters(name = "{0}")
  def allDirectories(): java.lang.Iterable[Array[String]] = {
    Files.list(Paths.get(rootPathStr)).map(filePath => Array(filePath.getFileName.toString)).toList
  }

}

@RunWith(classOf[Parameterized])
class ExecutionTests(programDirName: String) {

  private val programDirPath = Path.of(rootPathStr).resolve(programDirName)

  @Test
  def runProgramTest(): Unit = {

    val testOutSubdirPath = programDirPath.resolve(testOutSubdirName)
    if (testOutSubdirPath.toFile.exists()) {
      deleteRecursively(testOutSubdirPath)
    }

    val expOut = getExpectedData(programDirPath.resolve(stdoutFileName))

    class ExitException extends RuntimeException

    val er = ErrorReporter(System.err.println, exit = throw new ExitException)
    val srcFiles = getAllSourcesInProgram(programDirPath).map(s => SourceFile(programDirPath.resolve(s).toString))
    val stdLibFiles =
      Files.walk(Paths.get("../licorne-stdlib"))
        .map(_.toAbsolutePath.toString)
        .filter(_.endsWith(FileExtensions.dot(_.licorne)))
        .toArray(new Array[String](_))
        .map(SourceFile(_))

    val mainClasses = try {
      TasksPipelines
        .compiler(testOutSubdirPath, Some(testOutSubdirPath), ArithIntMode, None, None, er)
        .apply(srcFiles ++ stdLibFiles)
    } catch {
      case e: Throwable =>
        er.displayErrors()
        throw e
    }

    def errorCallback(msg: String): Nothing = {
      throw AssertionError(msg)
    }

    assert(mainClasses.size == 1)
    val process = Runner(errorCallback, testOutSubdirPath).runMain(mainClasses.head, inheritIO = false, Array.empty)

    val exitCode = process.waitFor()
    val actOut = readProgramStream(process.getInputStream)
    val actErr = readProgramStream(process.getErrorStream)

    val msgOpt = maybeGetTraceMessage()
    val stacktraceEntries = getTraceEntries(srcFiles)
    assert(!(msgOpt.isDefined && stacktraceEntries.isEmpty),
      "no stacktrace entry provided for a test program that is expected to crash")
    assert(!(msgOpt.isEmpty && stacktraceEntries.nonEmpty),
      "test expects some lines to appear in a stacktrace but does not specify the error message")

    if (msgOpt.isDefined) {
      assertMatches(msgOpt.get, stacktraceEntries, actErr)
      assertNotEquals("expected an error, but got a zero exit code", 0, exitCode)
    } else {
      if (exitCode != 0) {
        System.err.println("Errors:")
        System.err.println(actErr)
      }
      assertEquals(s"unexpected output on stdout (exit code: $exitCode)", expOut, actOut)
      assertEquals(s"non-zero exit code", 0, exitCode)
    }
  }

  private def deleteRecursively(path: Path): Unit = {
    // code adapted from https://www.baeldung.com/java-delete-directory
    Using(Files.walk(path)) { paths =>
      paths.sorted(Comparator.reverseOrder())
        .map(_.toFile())
        .forEach(_.delete())
    }
  }

  private def readProgramStream(is: InputStream): String = {
    new String(is.readAllBytes())
      .lines()
      .toArray(new Array[String](_))
      .mkString("\n")
  }

  private def getExpectedData(path: Path): String = {
    Files.readAllLines(path).toArray.mkString("\n")
  }

  private def getAllSourcesInProgram(dirPath: Path): List[String] = {
    dirPath.toFile.list((_, name) => name.endsWith(FileExtensions.licorne)).toList
  }

  private def maybeGetTraceMessage(): Option[String] = {
    val traceFile = programDirPath.resolve(stacktraceFileName).toFile
    if (traceFile.exists()) {
      val lines = Using(Source.fromFile(traceFile))(_.getLines().mkString("\n")).get
      Some(lines)
    } else None
  }

  private def getTraceEntries(srcFiles: Seq[SourceFile]): Seq[(Filename, Int)] = {
    srcFiles.flatMap(getTraceEntries)
  }

  private def getTraceEntries(srcFile: SourceFile): Seq[(Filename, Int)] = {
    val srcFileName = nameFromPath(srcFile.name)
    val lines = srcFile.lines.get
    val entriesB = Seq.newBuilder[(Filename, Int)]
    var lineIdx = 1
    for line <- lines do {
      if (line.contains(stackTraceCommentMarker)) {
        entriesB.addOne((srcFileName, lineIdx))
      }
      lineIdx += 1
    }
    entriesB.result()
  }

  private type Filename = String

  private def assertMatches(expMsg: String, reqEntries: Seq[(Filename, Int)], actErr: String): Unit = {
    assertTrue("expected an error but stderr is empty", actErr.nonEmpty)
    val lines = actErr.lines().toArray(new Array[String](_))
    val actMsg = lines.head.split(':')(1)
    val actualEntries = extractEntriesFromStacktrace(lines.tail)
    assertEquals("Actual stderr: " + actErr, expMsg.trim, actMsg.trim)
    val missingEntries = reqEntries.filterNot { (fn, l) =>
      actualEntries.exists((afn, alo) => afn == fn && alo.contains(l))
    }
    if (missingEntries.nonEmpty) {
      fail(
        "Missing entries in stacktrace:\n"
          + missingEntries.map((fn, l) => s"$fn:$l").mkString("\n")
          + "\nActual stderr: "
          + actErr
      )
    }
  }

  private def extractEntriesFromStacktrace(lines: Array[String]): Array[(Filename, Option[Int])] = {
    lines.map { line =>
      val openParenthIdx = line.indexOf('(')
      val idxOfLastSep = line.lastIndexOf('/') max line.lastIndexOf('\\')
      val startIdx = (openParenthIdx max idxOfLastSep) + 1
      val fileAndLine = line.substring(startIdx, line.length - 1)
      fileAndLine.split(':') match {
        case Array(actualFileName) =>
          (nameFromPath(actualFileName), None)
        case Array(actualFileName, lineIdxStr) =>
          (nameFromPath(actualFileName), Some(lineIdxStr.toInt))
        case _ => assert(false, "Failed to extract entries from the following stacktrace: \n" + lines.mkString("\n"))
      }
    }
  }

  private def nameFromPath(p: String): String = Path.of(p).getFileName.toString

}