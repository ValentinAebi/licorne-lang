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
  
  def newTypeVariable(id: Identifier, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type], typeParamsCtx: TypeParamsContext, instantiationPosOpt: Option[Position]): TypeVariable =
    TypeVariable(id, upperBoundOpt, lowerBoundOpt, typeParamsCtx, instantiationPosOpt)(saveTypeVariable)

  def saveTypeVariable(tv: TypeVariable): Unit = {
    allTypeVariables.addOne(tv)
  }

  def checkAllTypeVariablesHaveBeenResolved(typer: Typer, er: ErrorReporter)(using CompilationStep): Unit = {
    val subst = mutable.Map.empty[TypeIdentifier, Type]
    for (tv <- allTypeVariables) {
      tv.actualTypeIfResolved match {
        case Some(tpe) =>
          val ub = tv.upperBoundOpt.map(_.substitute(subst, Map.empty))
          val lb = tv.lowerBoundOpt.map(_.substitute(subst, Map.empty))
          typer.checkTypeIsInBounds(tpe, ub, lb, tv.instantiationPosOpt, tv.id)(using tv.typeParamsCtx)
          tv.id match {
            case tid: TypeIdentifier =>
              subst.put(tid, tpe)
            case _ => ()
          }
          
        case None =>
          er.reportError(s"type variable $tv could not be resolved", tv.instantiationPosOpt)
      }
    }
  }

}
