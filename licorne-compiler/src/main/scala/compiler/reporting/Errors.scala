package compiler.reporting

import compiler.pipeline.CompilationStep

import scala.collection.mutable

object Errors {

  /**
   * Exit code used when aborting because of non fatal error(s)
   */
  val errorsExitCode: Int = -20

  /**
   * Exit code used when aborting because of a fatal error
   */
  val fatalErrorExitCode: Int = -21

  // Colors
  private val red = "\u001B[31m"
  private val yellow = "\u001B[33m"
  private val resetColor = "\u001B[0m"

  /**
   * Compilation error or warning
   *
   * Ordered according to their position in the program
   */
  sealed trait CompilationError {
    val compilationStep: CompilationStep
    val msg: String
    val posOpt: Option[Position]

    val errorLevelDescr: String
    val color: String

    val isWarning: Boolean = isInstanceOf[Warning]
    val isFatal: Boolean = isInstanceOf[Fatal]

    override def toString: String = {
      val positionDescr = posOpt.map(pos => s"at $pos ").getOrElse("")
      color ++ s"[$errorLevelDescr] " ++ positionDescr ++ s"$msg #$compilationStep" ++ resetColor
    }
  }

  /**
   * Non fatal error or warning
   */
  sealed trait NonFatal extends CompilationError

  /**
   * Fatal error, should terminate the compiler immediately
   */
  final case class Fatal(compilationStep: CompilationStep, msg: String, posOpt: Option[Position]) extends CompilationError {
    override val errorLevelDescr: String = "FATAL"
    override val color: String = red
  }

  object Fatal {
    def apply(compilationStep: CompilationStep, msg: String, pos: Position) =
      new Fatal(compilationStep, msg, Some(pos))
  }

  /**
   * Non fatal error, should terminate the compiler at the end of the current compilation step
   */
  final case class Err(compilationStep: CompilationStep, msg: String, posOpt: Option[Position]) extends NonFatal {
    override val errorLevelDescr: String = "error"
    override val color: String = red
  }

  object Err {
    def apply(compilationStep: CompilationStep, msg: String, pos: Position) =
      new Err(compilationStep, msg, Some(pos))
  }

  /**
   * Warning: should be reported to the user, but not terminate the compiler
   */
  final case class Warning(compilationStep: CompilationStep, msg: String, posOpt: Option[Position]) extends NonFatal {
    override val errorLevelDescr: String = "warning"
    override val color: String = yellow
  }

  object Warning {
    def apply(compilationStep: CompilationStep, msg: String, pos: Position) =
      new Warning(compilationStep, msg, Some(pos))
  }

  type ErrorsConsumer = (CompilationError | String) => Unit

  type ExitCode = Int

  /**
   * Container for errors found during compilation
   *
   * @param errorsConsumer to be called when errors need to be displayed
   */
  final class ErrorReporter(errorsConsumer: ErrorsConsumer, exit: => ExitCode => Nothing) {
    private val errors = mutable.ListBuffer.empty[NonFatal]
    private var suspended = false

    /**
     * Add an error to the stack of non fatal errors
     */
    def report(nonFatalError: NonFatal): Unit = if (!suspended) {
      errors.addOne(nonFatalError)
    }

    def reportError(msg: String, posOpt: Option[Position])
                   (using compilationStep: CompilationStep): Unit = {
      report(Err(compilationStep, msg, posOpt))
    }

    def warn(msg: String, posOpt: Option[Position])
            (using compilationStep: CompilationStep): Unit = {
      report(Warning(compilationStep, msg, posOpt))
    }

    def getErrors: List[CompilationError] = errors.toList

    def errorsCntInclWarnings: Int = errors.size

    def displayErrors(): Unit = {
      var errorsCnt = 0
      var warningsCnt = 0
      for error <- errors do {
        errorsConsumer(error)
        errorsConsumer("\n")
        error match {
          case Err(compilationStep, msg, posOpt) =>
            errorsCnt += 1
          case Warning(compilationStep, msg, posOpt) =>
            warningsCnt += 1
        }
      }
      errorsConsumer(s"\n${maybePlural(errorsCnt, "error", "errors")}, ${maybePlural(warningsCnt, "warning", "warnings")}\n")
    }

    /**
     * Display errors and exit
     */
    def displayErrorsAndTerminate(): Nothing = {
      displayErrors()
      displayExitMessage()
      exit(if errors.isEmpty then 0 else errorsExitCode)
    }

    /**
     * If there are errors, display them and terminate the program (o.w. display the warnings and delete them)
     */
    def displayAndTerminateIfErrors(): Unit = {
      if (errors.exists(!_.isWarning)) {
        displayErrors()
        displayExitMessage()
        exit(errorsExitCode)
      }
    }

    /**
     * Display the given fatal error as well as all errors found until now and exit
     */
    def reportFatal(fatalError: Fatal): Nothing = {
      errorsConsumer(fatalError)
      errorsConsumer("\n")
      if errors.nonEmpty then errorsConsumer("Previously found errors:\n")
      displayErrors()
      displayExitMessage()
      exit(fatalErrorExitCode)
    }

    def withReportingSuspended[T](action: => T): T = {
      suspended = true
      val res = action
      suspended = false
      res
    }

    def withReportingSuspendedIf[T](cond: Boolean)(action: => T): T = {
      if (cond) {
        withReportingSuspended(action)
      } else {
        action
      }
    }

    private def maybePlural(cnt: Int, sing: String, plur: String): String = s"$cnt ${if cnt == 1 then sing else plur}"

    private def displayExitMessage(): Unit = errorsConsumer("\nLicorne compiler exiting\n")

  }

}

