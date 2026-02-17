package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.{Formula, IdValue}
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.{DatatypeSignature, Encapsulated, Formulas, RecordSignature, Unencapsulated}
import compiler.program.Program
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult.*
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}
import compiler.lang.Formulas.*
import compiler.typing.PurityChecking

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.boundary

trait ControlFlowInfo {

  def smartcastFor(formula: Formula): Option[Type]

  def hasExited: Boolean

  def afterCondition(cond: Formula): (this.type, this.type)
}

final class EnabledControlFlowInfo(
                                    unencapsulatedTypesData: Map[Formula, UnencapsulatedSmartcastingData],
                                    encapsulatedTypesData: Map[Formula, EncapsulatedSmartcastingData],
                                    subtypingCtx: SubtypingContext
                                  ) extends ControlFlowInfo {

  def smartcastFor(formula: Formula): Option[Type] = {
    unencapsulatedTypesData.get(formula)
      .orElse(encapsulatedTypesData.get(formula))
      .flatMap { smartcastData =>
        smartcastData.mostPreciseTypeId
      }.flatMap { targetTid =>
        subtypingCtx.checkDowncastTarget(smartcastData.rawType, targetTid).asOption
      }
  }

  def hasExited: Boolean =
    unencapsulatedTypesData.exists((_, smartcastInfo) => smartcastInfo.canProveIsNothing)

  def afterCondition(cond: Formula): (EnabledControlFlowInfo, EnabledControlFlowInfo) = {
    ???
  }

}

object DisabledControlFlowInfo extends ControlFlowInfo {
  override def smartcastFor(formula: Formula): Option[Type] = None

  override def hasExited: Boolean = false

  override def afterCondition(cond: Formula): (this.type, this.type) =
    (DisabledControlFlowInfo, DisabledControlFlowInfo)
}

object ControlFlowInfo {

  def emptyEnabled(subtypingCtx: SubtypingContext): EnabledControlFlowInfo =
    new EnabledControlFlowInfo(Map.empty, Map.empty, subtypingCtx)

  def disabled: DisabledControlFlowInfo.type = DisabledControlFlowInfo

}
