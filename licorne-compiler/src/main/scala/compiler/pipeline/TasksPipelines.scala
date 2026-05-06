package compiler.pipeline

import compiler.display.SSAPrinter
import compiler.identifiers.TypeIdentifier
import compiler.io.{SourceCodeProvider, StringWriter}
import compiler.irs.asts.Asts
import compiler.irs.asts.Asts.ImportStat
import compiler.lexer.Lexer
import compiler.parser.Parser
import compiler.program.Program
import compiler.reporting.Errors.{ErrorReporter, ExitCode}
import compiler.ssagen.{ImportsScanner, SSAGenerator}
import compiler.typing.{HeapVarsTypeStore, TypeHintsStore}
import compiler.typing.contexts.TypeVariablesContext
import compiler.typing.phases.*
import compiler.valproxies.ProxyStore

import java.nio.file.Path

/**
 * Contains methods producing pipelines for different tasks, indicated by their name
 */
object TasksPipelines {

  /**
   * Pipeline for compilation (src file -> .class file)
   */
  def compiler(
                outputDirectoryPath: Path,
                runtimeDirPath: Path,
                agentDirPath: Path,
                er: ErrorReporter = defaultErrorReporter
              ): CompilerStep[List[SourceCodeProvider], List[TypeIdentifier]] = {
    compilerImpl(outputDirectoryPath, runtimeDirPath, agentDirPath, er)
  }

  /**
   * Pipeline for typechecker (src file -> side effects of error reporting)
   */
  def typeChecker(er: ErrorReporter = defaultErrorReporter,
                  okReporter: String => Unit = println): CompilerStep[List[SourceCodeProvider], Unit] = {
    ???
  }

  def multiFrontEnd(er: ErrorReporter): CompilerStep[List[SourceCodeProvider], List[Asts.Source]] = MultiStep(frontend(er))

  def frontend(er: ErrorReporter): CompilerStep[SourceCodeProvider, Asts.Source] = {
    new Lexer(er).andThen(new Parser(er))
  }

  private def compilerImpl(outputDirectoryPath: Path,
                           runtimeDirPath: Path,
                           agentDirPath: Path,
                           er: ErrorReporter) = {
    val typeVarsCtx = TypeVariablesContext()
    val proxyStore = ProxyStore()
    val typeHintsStore = TypeHintsStore()
    val heapVarsTypeStore = HeapVarsTypeStore()
    multiFrontEnd(er)
      .andThen(ImportsScanner())
      .andThen(SSAGenerator(typeVarsCtx, proxyStore, er, /* FIXME check that this check works */ srcRootsForPkgMismatchCheckOpt = None))
      .andThen(Concurrent(
        SSAPrinter(proxyStore, typeHintsStore, "  ", printTypes = false)
          .andThen(StringWriter(Path.of("./temp/out"), "ssa.txt", er, _ => true)),
        IdentityStep(),
        (_, program) => program
      )).andThen(MonotonicityAnalyzer(proxyStore))
      .andThen(TypeAliasesAnalyzer(typeVarsCtx, proxyStore, typeHintsStore, heapVarsTypeStore, er))
      .andThen(SubtypingChecker(proxyStore, er))
      .andThen(TypeHintsInserter(typeVarsCtx, proxyStore, typeHintsStore, er))
      .andThen(DeclarationsChecker(typeVarsCtx, proxyStore, typeHintsStore, heapVarsTypeStore, er))
      .andThen(TypeChecker(typeVarsCtx, proxyStore, typeHintsStore, heapVarsTypeStore, er, /*FIXME*/ continueIfErrors = true))
      .andThen(OverridesChecker(proxyStore, er, /*FIXME*/ continueIfErrors = true))
      .andThen((program, subtypingInfo) => program)
      .andThen(Concurrent(
        SSAPrinter(proxyStore, typeHintsStore, "  ", printTypes = true)
          .andThen(StringWriter(Path.of("./temp/out"), "ssa.txt", er, _ => true)),
        IdentityStep(),
        (_, program) => program
      ))
      // FIXME this implementation is temporary
      //.andThen(??? /* compilation to bytecode */)
      .andThen(MissingCompiler(er, printProgram = false))
  }

  private final class MissingCompiler(er: ErrorReporter, printProgram: Boolean) extends CompilerStep[Any, Nothing] {
    override def apply(input: Any): Nothing = {
      println("Compiler not implemented")
      if (printProgram) {
        println("Last representation of the program before exiting was:")
        println(caseClassesFormat(input.toString))
      }
      er.displayErrorsAndTerminate()
    }
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
