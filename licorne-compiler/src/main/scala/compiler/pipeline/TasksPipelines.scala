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

  private val ssaFileName = "ssa.txt"
  private val ssaIndentUnit = "  "
  private val ssaPrintTypes = true

  def compiler(
                outputDirectoryPath: Path,
                ssaDirectoryPathOpt: Option[Path],
                ihm: IntHandlingMode[?],
                counterExBoxOpt: Option[CounterexampleBox],
                er: ErrorReporter = defaultErrorReporter
              ): CompilerStep[List[SourceCodeProvider], List[String]] = {
    typeCheckerImpl(ihm, er, counterExBoxOpt, ssaDirectoryPathOpt)
      .andThen(Backend(outputDirectoryPath, er))
  }

  def typeChecker(
                   ssaDirectoryPathOpt: Option[Path],
                   ihm: IntHandlingMode[?],
                   counterExBoxOpt: Option[CounterexampleBox],
                   er: ErrorReporter = defaultErrorReporter,
                   okReporter: String => Unit = println
                 ): CompilerStep[List[SourceCodeProvider], Unit] = {
    typeCheckerImpl(ihm, er, counterExBoxOpt, ssaDirectoryPathOpt)
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
                               ssaDirPathOpt: Option[Path]
                             ): CompilerStep[List[SourceCodeProvider], (Program, SubtypingInfo)] = {
    val typeVarsCtx = TypeVariablesContext()
    val proxyStore = ProxyStore()
    val typeCandidatesStore = TypeCandidatesStore()
    val heapVarsTypeStore = HeapVarsTypeStore()
    multiFrontEnd(er)
      .andThen(ImportsScanner())
      .andThen(SSAGenerator(typeVarsCtx, proxyStore, er, /* FIXME check that this check works */ srcRootsForPkgMismatchCheckOpt = None))
      .andThen(MaybePrintSSA(proxyStore, typeCandidatesStore, identity, er, ssaDirPathOpt))
      .andThen(SubtypingChecker(proxyStore, er))
      .andThen(TypeAliasesAnalyzer(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt))
      .andThen(DeclarationsChecker(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt))
      .andThen(TypeCandidatesInferrer(ihm, proxyStore, typeCandidatesStore, er, counterExBoxOpt))
      .andThen(MaybePrintSSA(proxyStore, typeCandidatesStore, (program, subtypingInfo) => program, er, ssaDirPathOpt))
      .andThen(TypeChecker(ihm, typeVarsCtx, proxyStore, typeCandidatesStore, heapVarsTypeStore, er, counterExBoxOpt, handleErrors = _ => ()))
      .andThen(MaybePrintSSA(proxyStore, typeCandidatesStore, (program, subtypingInfo) => program, er, ssaDirPathOpt))
      .andThen(DisplayAndTerminateIfErrors(er))
      .andThen(OverridesChecker(ihm, proxyStore, er, counterExBoxOpt))
      .andThen(MaybePrintSSA(proxyStore, typeCandidatesStore, (program, subtypingInfo) => program, er, ssaDirPathOpt))
  }

  private def defaultErrorReporter: ErrorReporter =
    new ErrorReporter(errorsConsumer = System.err.print, exit = defaultExit)

  private def defaultExit(exitCode: ExitCode): Nothing = {
    System.exit(exitCode)
    throw new AssertionError("cannot happen")
  }

  private final class MaybePrintSSA[T](
                                        proxyStore: ProxyStore,
                                        typeCandidatesStore: TypeCandidatesStore,
                                        extractProgram: T => Program,
                                        er: ErrorReporter,
                                        ssaDirPathOpt: Option[Path]
                                      ) extends CompilerStep[T, T] {
    override def apply(input: T): T = {
      ssaDirPathOpt.foreach { ssaDirPath =>
        SSAPrinter(proxyStore, typeCandidatesStore, ssaIndentUnit, ssaPrintTypes)
          .andThen(StringWriter(ssaDirPath, ssaFileName, er, overwriteFileCallback = _ => true))
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
