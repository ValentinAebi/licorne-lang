package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.{Formula, IdValue}
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.{DatatypeSignature, Encapsulated, RecordSignature, Unencapsulated}
import compiler.program.Program
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult.*
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.boundary

final class ControlFlowInfo(subtypingCtx: SubtypingContext) {
  private val unencapsulatedTypesData = mutable.Map.empty[Formula, UnencapsulatedSmartcastingData]
  private val encapsulatedTypesData = mutable.Map.empty[Formula, EncapsulatedSmartcastingData]

  def smartcastFor(formula: Formula): Option[Type] = {
    unencapsulatedTypesData.get(formula).flatMap { smartcastData =>
      smartcastData.mostPreciseType().flatMap { targetTypeName =>
        subtypingCtx.checkDowncastTarget(smartcastData.rawType, targetTypeName).asOption
      }
    }.orElse {
      encapsulatedTypesData.get(formula).map(_.mostPreciseType)
    }
  }
  
  def canProveHasType(formula: Formula, tpe: Type): Boolean = {
    (unencapsulatedTypesData.get(formula), tpe) match {
      case (Some(smartcastData), tpe: NamedType) =>
        subtypingCtx.checkDowncastTarget(tpe, tpe.typeName) == CanDowncast(tpe)
          && smartcastData.canProveIs(tpe.typeName)
      case _ => false
    }
  }
  
  def hasExited: Boolean =
    unencapsulatedTypesData.exists((_, smartcastInfo) => smartcastInfo.canProveIsNothing)

}

object ControlFlowInfo {

  def empty(subtypingCtx: SubtypingContext): ControlFlowInfo =
    new ControlFlowInfo(subtypingCtx)

}
