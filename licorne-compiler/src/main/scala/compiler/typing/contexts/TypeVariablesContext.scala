package compiler.typing.contexts

import compiler.identifiers.{Identifier, TypeIdentifier}
import compiler.lang.Types.{Type, TypeVariable}
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.Typer

import scala.collection.mutable

final class TypeVariablesContext {
  private val allTypeVariables = mutable.ListBuffer.empty[TypeVariable]
  
  def newTypeVariable(id: Identifier, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type], typeParamsCtx: TypeParamsContext, instantiationPosOpt: Option[Position], ignoreRefinementOnResolve: Boolean = false): TypeVariable =
    TypeVariable(id, upperBoundOpt, lowerBoundOpt, typeParamsCtx, instantiationPosOpt, ignoreRefinementOnResolve)(saveTypeVariable)

  def saveTypeVariable(tv: TypeVariable): Unit = {
    allTypeVariables.addOne(tv)
  }

  def checkAllTypeVariablesHaveBeenResolved(typer: Typer, er: ErrorReporter)(using CompilationStep): Unit = {
    for (tv <- allTypeVariables) {
      tv.actualTypeIfResolved match {
        case Some(tpe) =>
          typer.checkTypeIsInBounds(tpe, tv.upperBoundOpt, tv.lowerBoundOpt, tv.instantiationPosOpt, tv.id)(using tv.typeParamsCtx)
        case None =>
          er.reportError(s"type variable $tv could not be resolved", tv.instantiationPosOpt)
      }
    }
  }
  
  def forgetTypeVar(tv: TypeVariable): Unit = {
    allTypeVariables.filterInPlace(_ != tv)
  }

}
