package compiler

import compiler.AnalyzerTests.*
import compiler.imports.ImportsChecker
import compiler.io.SourceFile
import compiler.irs.asts.Asts.ImportStat
import compiler.pipeline.{Concurrent, IdentityStep, Mapper, TasksPipelines}
import compiler.program.Program
import compiler.reporting.Errors.*
import compiler.smt.{AbstractInterpreter, Simplifier, Solver}
import compiler.ssagen.SSAGenerator
import compiler.typing.{HeapVarsTypeStore, TypeHintsStore}
import compiler.typing.contexts.TypeVariablesContext
import compiler.typing.phases.{DeclarationsChecker, MonotonicityAnalyzer, OverridesChecker, SubtypingChecker, TypeAliasesAnalyzer, TypeChecker, TypeHintsInserter}
import compiler.valproxies.ProxyStore
import org.junit.Assert.fail
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters

import java.io.File
import java.nio.file.{Files, Paths}
import scala.collection.mutable
import scala.runtime.BooleanRef


object AnalyzerTests {

  private val rootPathStr: String = "./src/test/res/analyzer-tests/"
  private val matcherMarker: String = "//>"
  private val matcherSep: String = "<//>"
  private val colMarker: String = "@col="
  private val ignoreAdditionalErrorsMarker: String = "allow-more-errors"

  @Parameters(name = "{0}")
  def allFiles(): java.lang.Iterable[Array[String]] = {
    Files.list(Paths.get(rootPathStr)).map(filePath => Array(filePath.getFileName.toString)).toList
  }

  private enum Level {
    case Error, Warning
  }

  private case class Matcher(
                              msg: String,
                              fileName: String,
                              oneBasedLineIdx: Int,
                              oneBasedColIdxOpt: Option[Int],
                              level: Level
                            ) {

    import Level.Warning

    def matches(err: CompilationError): Boolean = {
      err.msg.trim == msg.trim
        && err.posOpt.exists(_.srcCodeProviderName == fileName)
        && err.posOpt.exists(_.line == oneBasedLineIdx)
        && oneBasedColIdxOpt.forall(oneBasedColIdx => err.posOpt.exists(_.col == oneBasedColIdx))
        && (err.isWarning == (level == Warning))
    }

    override def toString: String = {
      val levelDescr = level.toString.toLowerCase
      val colDescr = oneBasedColIdxOpt.map(":" + _).getOrElse("")
      s"[$levelDescr] $fileName:$oneBasedLineIdx$colDescr : $msg"
    }

  }

}

@RunWith(classOf[Parameterized])
class AnalyzerTests(fileName: String) {

  @Test
  def checkFileTest(): Unit = {

    val testRootPathStr = rootPathStr + fileName
    val testRootFile = new File(testRootPathStr)
    val srcFileNames =
      if testRootFile.isDirectory
      then testRootFile.list().toList.map(testRootPathStr + "/" + _)
      else List(testRootPathStr)
    val srcFiles = srcFileNames.map(SourceFile(_))

    // error matcher -> boolean indicating whether a matching error has already been found
    val expectedErrors = mutable.LinkedHashMap.empty[Matcher, Boolean]
    val ignoreAdditionalErrorsFlag = BooleanRef.create(false)
    for (srcFile <- srcFiles) {
      readErrorsSpec(srcFile.lines.get, srcFile.name, expectedErrors, ignoreAdditionalErrorsFlag)
    }

    // error -> boolean indicating whether a matching matcher has been found
    val errors = mutable.LinkedHashMap.empty[CompilationError, Boolean]

    val errorsConsumer: ErrorsConsumer = {
      case err: CompilationError =>
        expectedErrors.find((matcher, alrMatched) => !alrMatched && matcher.matches(err))
          .map { (matcher, _) =>
            expectedErrors(matcher) = true
            errors.put(err, true)
          }.getOrElse {
            errors.put(err, false)
          }
      case _: String => ()
    }

    case object ExitException extends Exception

    var fatalErrorOccured = false

    def exitCalled(exitCode: ExitCode): Nothing = {
      fatalErrorOccured |= exitCode == fatalErrorExitCode
      throw ExitException
    }

    val typeVarsCtx = TypeVariablesContext()
    val proxyStore = ProxyStore()
    val typeHintsStore = TypeHintsStore()
    val heapVarsTypeStore = HeapVarsTypeStore()
    val er = ErrorReporter(errorsConsumer, exitCalled)
    val pipeline = TasksPipelines.multiFrontEnd(er)
      .andThen(SSAGenerator(typeVarsCtx, proxyStore, er))
      .andThen(Concurrent(
        Mapper[(Program, List[ImportStat]), Program]((program, imports) => program)
          .andThen(MonotonicityAnalyzer(proxyStore))
          .andThen(TypeAliasesAnalyzer(typeVarsCtx, proxyStore, typeHintsStore, heapVarsTypeStore, er))
          .andThen(SubtypingChecker(typeVarsCtx, proxyStore, er)),
        IdentityStep(),
        { case ((program, subtypingInfos), (_, imports)) => (program, subtypingInfos, imports) }
      ))
      .andThen(ImportsChecker(proxyStore, typeVarsCtx, er))
      .andThen(TypeHintsInserter(typeVarsCtx, proxyStore, typeHintsStore, er))
      .andThen(DeclarationsChecker(typeVarsCtx, proxyStore, typeHintsStore, heapVarsTypeStore, er))
      .andThen(TypeChecker(typeVarsCtx, proxyStore, typeHintsStore, heapVarsTypeStore, er))
      .andThen(OverridesChecker(typeVarsCtx, proxyStore, er))
    try {
      pipeline.apply(srcFiles)
    } catch {
      case ExitException => ()
    }

    val errorsAreMissing = expectedErrors.exists(!_._2)
    val existsUnexpectedErrors = errors.exists(!_._2)
    if (errorsAreMissing || (existsUnexpectedErrors && !ignoreAdditionalErrorsFlag.elem) || fatalErrorOccured) {
      fail(
        if fatalErrorOccured then "A fatal error occurred\n\n" else "" +
          "\nExpected errors:\n" +
          expectedErrors.map(markOkOrNot).mkString("\n") +
          "\n\nActual errors:\n" +
          errors.map(markOkOrNot).mkString("\n")
      )
    }
  }

  private def markOkOrNot[T](tAndOkFlag: (T, Boolean)): String = {
    val (t, okFlag) = tAndOkFlag
    val prefix =
      if okFlag
      then (colorGreen + " ✔ " + colorReset)
      else (colorRed + " ✘ " + colorReset)
    prefix + t
  }

  private def readErrorsSpec(lines: Seq[String], fileName: String,
                             matchers: mutable.Map[Matcher, Boolean], ignoreAdditionalErrorsFlag: BooleanRef): Unit = {
    for ((line, zeroBasedLineIdx) <- lines.zipWithIndex) {
      val markerIdx = line.indexOf(matcherMarker)
      val dataIdx = markerIdx + matcherMarker.length
      if (markerIdx != -1 && dataIdx < line.length) {
        val data = line.substring(dataIdx)
        if (data.trim.equals(ignoreAdditionalErrorsMarker)) {
          ignoreAdditionalErrorsFlag.elem = true
          assert(zeroBasedLineIdx == 0, s"$ignoreAdditionalErrorsMarker should only be used on the first line of the file")
        } else {
          val matchersStrings = data.split(matcherSep)
          for (matcherStr <- matchersStrings) {
            val splitMatcherStr = matcherStr.split(":", 2)
            assert(splitMatcherStr.size == 2, s"unrecognized matcher: $matcherStr")
            val Array(levelAndLineStr, msg) = splitMatcherStr.map(_.trim)
            val (levelStr, oneBasedColIdxOpt) = levelAndLineStr.split(colMarker, 2) match {
              case Array(lv, colStr) =>
                val colOpt = colStr.toIntOption.orElse(throw AssertionError(s"cannot parse column: $colStr"))
                (lv, colOpt)
              case Array(lv) => (lv, None)
            }
            matchers.addOne(Matcher(msg, fileName, zeroBasedLineIdx + 1, oneBasedColIdxOpt, parseLevel(levelStr)), false)
          }
        }
      }
    }
  }

  private def parseLevel(levelStr: String): Level = levelStr match {
    case "E" => Level.Error
    case "W" => Level.Warning
    case _ => throw AssertionError(s"unexpected level code: $levelStr")
  }

  private val colorRed = "\u001B[31m"
  private val colorGreen = "\u001B[32m"
  private val colorReset = "\u001B[0m"

}
