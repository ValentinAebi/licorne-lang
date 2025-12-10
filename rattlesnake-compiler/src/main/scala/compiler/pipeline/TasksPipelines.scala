package compiler.pipeline

import compiler.io.{SourceCodeProvider, StringWriter}
import compiler.irs.Asts
import compiler.lexer.Lexer
import compiler.parser.Parser
import compiler.reporting.Errors.{ErrorReporter, ExitCode}
import compiler.ssagen.SSAGenerator
import compiler.ssaprinter.SSAPrinter
import compiler.typechecking.Typer
import identifiers.TypeIdentifier

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
    multiFrontEnd(er)
      .andThen(SSAGenerator(er))
      // FIXME this implementation is temporary
      .andThen(Typer(er, /* FIXME */ continueIfErrors = true))
      .andThen(SSAPrinter(_._1, _._2))
      .andThen(StringWriter(Path.of("./temp/out"), "ssa.txt", er, _ => true))
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
