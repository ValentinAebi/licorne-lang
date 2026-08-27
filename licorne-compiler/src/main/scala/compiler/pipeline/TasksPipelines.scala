package compiler.pipeline

import compiler.backend.Backend
import compiler.display.IRcornePrinter
import compiler.io.{SourceCodeProvider, StringWriter}
import compiler.irs.asts.Asts
import compiler.lexer.Lexer
import compiler.parser.Parser
import compiler.program.Program
import compiler.reasoning.{CounterexampleBox, IntHandlingMode}
import compiler.reporting.Errors.{ErrorReporter, ExitCode}
import compiler.ircornegen.{ImportsScanner, IRcorneGenerator}
import compiler.typing.contexts.TypeVariablesContext
import compiler.typing.phases.*
import compiler.typing.{HeapVarsTypeStore, SubtypingInfo, TypeCandidatesStore}
import compiler.valproxies.ProxyStore

import java.nio.file.Path

/**
 * Contains methods producing pipelines for different tasks, indicated by their name
 */
object TasksPipelines {

  private val irIndentUnit = "  "
  private val irPrintTypes = true

  def compiler(
                outputDirectoryPath: Path,
                irDirectoryPathOpt: Option[Path],
                ihm: IntHandlingMode[?],
                counterExBoxOpt: Option[CounterexampleBox],
                srcRootForPkgMismatchCheckOpt: Option[Path],
                er: ErrorReporter = defaultErrorReporter
              ): CompilerStep[List[SourceCodeProvider], List[String]] = {
    typeCheckerImpl(ihm, er, counterExBoxOpt, irDirectoryPathOpt, srcRootForPkgMismatchCheckOpt)
      .andThen(Backend(outputDirectoryPath, er))
  }

  def typeChecker(
                   irDirectoryPathOpt: Option[Path],
                   ihm: IntHandlingMode[?],
                   counterExBoxOpt: Option[CounterexampleBox],
                   srcRootForPkgMismatchCheckOpt: Option[Path],
                   er: ErrorReporter = defaultErrorReporter,
                   okReporter: String => Unit = println
                 ): CompilerStep[List[SourceCodeProvider], Unit] = {
    typeCheckerImpl(ihm, er, counterExBoxOpt, irDirectoryPathOpt, srcRootForPkgMismatchCheckOpt)
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
                               irDirPathOpt: Option[Path],
                               srcRootForPkgMismatchCheckOpt: Option[Path]
                             ): CompilerStep[List[SourceCodeProvider], (Program, SubtypingInfo)] = {
    val typeVarsCtx = TypeVariablesContext()
    val proxyStore = ProxyStore()
    val typeCandidatesStore = TypeCandidatesStore()
    val heapVarsTypeStore = HeapVarsTypeStore()
    multiFrontEnd(er)
      .andThen(ImportsScanner())
      .andThen(IRcorneGenerator(typeVarsCtx, proxyStore, er, srcRootForPkgMismatchCheckOpt))
      .andThen(MaybePrintIRcorne("ir1-after-ir-gen.ircorne", proxyStore, typeCandidatesStore, identity, er, irDirPathOpt))
      .andThen(SubtypingChecker(proxyStore, er))
      .andThen(TypeAliasesAnalyzer(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt))
      .andThen(DeclarationsChecker(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt))
      .andThen(TypeCandidatesInferrer(ihm, proxyStore, typeCandidatesStore, counterExBoxOpt))
      .andThen(MaybePrintIRcorne("ir2-after-candidates-inference.ircorne", proxyStore, typeCandidatesStore, (program, subtypingInfo) => program, er, irDirPathOpt))
      .andThen(TypeChecker(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt, handleErrors = _ => ()))
      .andThen(MaybePrintIRcorne("ir3-after-typecheck.ircorne", proxyStore, typeCandidatesStore, (program, subtypingInfo) => program, er, irDirPathOpt))
      .andThen(DisplayAndTerminateIfErrors(er))
      .andThen(OverridesChecker(ihm, proxyStore, er, counterExBoxOpt))
      .andThen(MaybePrintIRcorne("ir4-after-overrides-check.ircorne", proxyStore, typeCandidatesStore, (program, subtypingInfo) => program, er, irDirPathOpt))
  }

  private def defaultErrorReporter: ErrorReporter =
    new ErrorReporter(errorsConsumer = System.err.print, exit = defaultExit)

  private def defaultExit(exitCode: ExitCode): Nothing = {
    System.exit(exitCode)
    throw new AssertionError("cannot happen")
  }

  private final class MaybePrintIRcorne[T](
                                            irFileName: String,
                                            proxyStore: ProxyStore,
                                            typeCandidatesStore: TypeCandidatesStore,
                                            extractProgram: T => Program,
                                            er: ErrorReporter,
                                            irDirPathOpt: Option[Path]
                                          ) extends CompilerStep[T, T] {
    override def apply(input: T): T = {
      irDirPathOpt.foreach { irDirPath =>
        IRcornePrinter(proxyStore, typeCandidatesStore, irIndentUnit, irPrintTypes)
          .andThen(StringWriter(irDirPath, irFileName, er, overwriteFileCallback = _ => true))
          .apply(extractProgram(input))
      }
      input
    }
  }

  private final class DisplayAndTerminateIfErrors[T](er: ErrorReporter) extends CompilerStep[T, T] {
    override def apply(input: T): T = {
      er.displayAndTerminateIfErrors()
      input
    }
  }

}
