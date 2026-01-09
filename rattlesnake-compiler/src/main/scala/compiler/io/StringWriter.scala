package compiler.io

import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.reporting.Errors.{CompilationError, Err, ErrorReporter}

import java.io.FileWriter
import java.nio.file.{Files, Path}
import scala.util.{Failure, Success, Using}

final class StringWriter(directoryPath: Path, filename: String, errorReporter: ErrorReporter, overwriteFileCallback: String => Boolean) extends CompilerStep[String, Unit] {

  override def apply(input: String): Unit = {
    Files.createDirectories(directoryPath)
    val path = directoryPath.resolve(filename)
    if (path.toFile.exists()){
      val overwrite = overwriteFileCallback(s"file ${path.toString} already exists, do you want to overwrite it?")
      if (!overwrite){
        return
      }
    } else {
      Files.createFile(path)
    }
    val status = Using(new FileWriter(path.toFile))(_.write(input))
    status match
      case Failure(exception) =>
        errorReporter.report(Err(CompilationStep.StringWriting, exception.getMessage, None))
      case Success(_) => ()
  }

}