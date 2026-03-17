package compiler.typing.contexts

import compiler.lang.Types.{Type, TypeVariable}
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position

import scala.collection.mutable

final class TypeVariablesContext {
  private val allTypeVariables = mutable.ListBuffer.empty[(TypeVariable, Option[Position])]
  
  def newTypeVariable(name: String, posOpt: Option[Position]): TypeVariable =
    newTypeVariable(name, None, None, posOpt)
  
  def newTypeVariable(name: String, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type], posOpt: Option[Position]): TypeVariable =
    TypeVariable(name, upperBoundOpt, lowerBoundOpt)(saveTypeVariable(_, posOpt))

  def saveTypeVariable(tv: TypeVariable, posOpt: Option[Position]): Unit = {
    allTypeVariables.addOne((tv, posOpt))
  }

  def checkAllTypeVariablesHaveBeenResolved(errorsCallback: (String, Option[Position]) => Unit): Unit = {
    for ((tv, posOpt) <- allTypeVariables) {
      if (!tv.isResolved) {
        errorsCallback(s"type variable $tv could not be resolved", posOpt)
      }
    }
  }

}
