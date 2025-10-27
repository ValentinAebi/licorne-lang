package compiler.pipeline

import compiler.io.{SourceCodeProvider, StringWriter}
import compiler.irs.Asts
import compiler.lexer.Lexer
import compiler.parser.Parser
import compiler.reporting.Errors.{ErrorReporter, ExitCode}
import identifiers.TypeIdentifier
import org.objectweb.asm.ClassVisitor

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
                javaVersionCode: Int,
                runtimeDirPath: Path,
                agentDirPath: Path,
                er: ErrorReporter = defaultErrorReporter
              ): CompilerStep[List[SourceCodeProvider], List[TypeIdentifier]] = {
    compilerImpl(outputDirectoryPath, javaVersionCode, runtimeDirPath, agentDirPath, er)
  }

  /**
   * Pipeline for typechecker (src file -> side effects of error reporting)
   */
  def typeChecker(er: ErrorReporter = defaultErrorReporter,
                  okReporter: String => Unit = println): CompilerStep[List[SourceCodeProvider], Unit] = {
    MultiStep(frontend(er))
      .andThen(MissingCompiler) // TODO
  }

  private def compilerImpl[V <: ClassVisitor](outputDirectoryPath: Path,
                                              javaVersionCode: Int,
                                              runtimeDirPath: Path,
                                              agentDirPath: Path,
                                              er: ErrorReporter) = {
    MultiStep(frontend(er))
      .andThen(MissingCompiler)   // TODO
  }

  private object MissingCompiler extends CompilerStep[Any, Nothing] {
    override def apply(input: Any): Nothing = {
      println("Missing compiler. Last representation of the program before exiting is:")
      println(caseClassesFormat(input.toString))
      throw NotImplementedError("Compiler not yet implemented")
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
          sb.append(c)
        case ',' =>
          sb.append(c)
          mkNewLine()
        case _ =>
          sb.append(c)
      }
    }

    val linesIter = raw.lines().iterator()
    while (linesIter.hasNext){
      for (c <- linesIter.next()){
        addChar(c)
      }
      if (linesIter.hasNext){
        mkNewLine()
      }
    }
    sb.toString()
  }

  private def frontend(er: ErrorReporter): CompilerStep[SourceCodeProvider, Asts.Source] = {
    new Lexer(er).andThen(new Parser(er))
  }

  private def defaultErrorReporter: ErrorReporter =
    new ErrorReporter(errorsConsumer = System.err.print, exit = defaultExit)

  private def defaultExit(exitCode: ExitCode): Nothing = {
    System.exit(exitCode)
    throw new AssertionError("cannot happen")
  }

}
