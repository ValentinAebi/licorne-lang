package compiler.pipeline

import compiler.backend.Backend
import compiler.display.SSAPrinter
import compiler.identifiers.TypeIdentifier
import compiler.io.{SourceCodeProvider, StringWriter}
import compiler.irs.asts.Asts
import compiler.lexer.Lexer
import compiler.parser.Parser
import compiler.program.Program
import compiler.reasoning.{CounterexampleBox, IntHandlingMode}
import compiler.reporting.Errors.{ErrorReporter, ExitCode}
import compiler.ssagen.{ImportsScanner, SSAGenerator}
import compiler.typing.contexts.TypeVariablesContext
import compiler.typing.phases.*
import compiler.typing.{HeapVarsTypeStore, SubtypingInfo, TypeCandidatesStore}
import compiler.valproxies.ProxyStore

import java.nio.file.Path

/**
 * Contains methods producing pipelines for different tasks, indicated by their name
 */
object TasksPipelines {

  def compiler(
                outputDirectoryPath: Path,
                ihm: IntHandlingMode[?],
                counterExBoxOpt: Option[CounterexampleBox],
                er: ErrorReporter = defaultErrorReporter
              ): CompilerStep[List[SourceCodeProvider], List[TypeIdentifier]] = {
    typeCheckerImpl(ihm, er, counterExBoxOpt, Some(Path.of("./temp/out"), "ssa.txt") /* FIXME should be an option */)
      .andThen(Backend(outputDirectoryPath))
  }

  def typeChecker(
                   ihm: IntHandlingMode[?],
                   counterExBoxOpt: Option[CounterexampleBox],
                   er: ErrorReporter = defaultErrorReporter,
                   okReporter: String => Unit = println
                 ): CompilerStep[List[SourceCodeProvider], Unit] = {
    typeCheckerImpl(ihm, er, counterExBoxOpt, Some(Path.of("./temp/out"), "ssa.txt") /* FIXME should be an option */)
      .andThen(_ => ())
  }

  def multiFrontEnd(er: ErrorReporter): CompilerStep[List[SourceCodeProvider], List[Asts.Source]] = MultiStep(frontend(er))

  def frontend(er: ErrorReporter): CompilerStep[SourceCodeProvider, Asts.Source] = {
    new Lexer(er).andThen(new Parser(er))
  }

  private def typeCheckerImpl(
                               ihm: IntHandlingMode[?],
                               er: ErrorReporter,
                               counterExBoxOpt: Option[CounterexampleBox],
                               ssaOutputInfoOpt: Option[(Path, String)]
                             ): CompilerStep[List[SourceCodeProvider], (Program, SubtypingInfo)] = {
    val typeVarsCtx = TypeVariablesContext()
    val proxyStore = ProxyStore()
    val typeCandidatesStore = TypeCandidatesStore()
    val heapVarsTypeStore = HeapVarsTypeStore()
    multiFrontEnd(er)
      .andThen(ImportsScanner())
      .andThen(SSAGenerator(typeVarsCtx, proxyStore, er, /* FIXME check that this check works */ srcRootsForPkgMismatchCheckOpt = None))
      .andThen(
        ssaOutputInfoOpt match {
          case Some(ssaOutDirPath, ssaFileName) => Concurrent(
            SSAPrinter(proxyStore, typeCandidatesStore, "  ", printTypes = false)
              .andThen(StringWriter(ssaOutDirPath, ssaFileName, er, _ => true)),
            IdentityStep(),
            (_, program) => program
          )
          case None => IdentityStep()
        }
      ).andThen(SubtypingChecker(proxyStore, er))
      .andThen(TypeAliasesAnalyzer(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt))
      .andThen(DeclarationsChecker(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt))
      .andThen(TypeCandidatesInferrer(ihm, proxyStore, typeCandidatesStore, er, counterExBoxOpt))
      .andThen(TypeChecker(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt))
      .andThen(OverridesChecker(ihm, proxyStore, er, counterExBoxOpt))
      .andThen(ssaOutputInfoOpt match {
        case Some(ssaOutDirPath, ssaFileName) => Concurrent(
          Mapper[(Program, SubtypingInfo), Program]((program, subtypingInfo) => program)
            .andThen(SSAPrinter(proxyStore, typeCandidatesStore, "  ", printTypes = true))
            .andThen(StringWriter(ssaOutDirPath, ssaFileName, er, _ => true)),
          IdentityStep(),
          (_, programData) => programData
        )
        case None => IdentityStep()
      })
  }

  private def caseClassesFormat(raw: String): String = {
    val sb = StringBuilder()
    var indentLevel = 0

    def mkNewLine(): Unit = {
      sb.append("\n").append("  " * indentLevel)
    }

    def addChar(c: Char): Unit = {
      c match {
        case '\n' =>
          mkNewLine()
        case '(' =>
          sb.append(c)
          indentLevel += 1
          mkNewLine()
        case ')' =>
          indentLevel -= 1
          mkNewLine()
          sb.append(c)
        case ',' =>
          sb.append(c)
          mkNewLine()
        case _ =>
          sb.append(c)
      }
    }

    var i = 0
    while (i < raw.length) {
      val c = raw.charAt(i)
      if (c == '(') {
        val closingParenthIdx = findClosingParenthesis(raw, i + 1, 20)
        if (closingParenthIdx >= 0) {
          sb.append(raw.substring(i, closingParenthIdx + 1))
          i += closingParenthIdx - i
        } else {
          addChar('(')
        }
      } else {
        addChar(c)
      }
      i += 1
    }
    sb.toString()
  }

  private def findClosingParenthesis(str: String, start: Int, maxLen: Int): Int = {
    var i = start
    var balance = 1
    while (i < start + maxLen) {
      val c = str.charAt(i)
      if (c == '(') {
        balance += 1
      } else if (c == ')') {
        balance -= 1
      }
      if (balance == 0) {
        return i
      }
      i += 1
    }
    -1
  }

  private def defaultErrorReporter: ErrorReporter =
    new ErrorReporter(errorsConsumer = System.err.print, exit = defaultExit)

  private def defaultExit(exitCode: ExitCode): Nothing = {
    System.exit(exitCode)
    throw new AssertionError("cannot happen")
  }

}
