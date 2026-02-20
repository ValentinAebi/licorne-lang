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
import compiler.typing.smartcasting.SmartcastingData.DataAddition

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
    for {
      smartcastData <- unencapsulatedTypesData.get(formula).orElse(encapsulatedTypesData.get(formula))
      targetTid <- smartcastData.mostPreciseTypeIdOpt
      castResultType <- subtypingCtx.checkDowncastTarget(smartcastData.rawType, targetTid).asOption
    } yield castResultType
  }

  def hasExited: Boolean =
    unencapsulatedTypesData.exists((_, smartcastInfo) => smartcastInfo.canProveIsNothing)

  def afterCondition(cond: Formula): (EnabledControlFlowInfo, EnabledControlFlowInfo) = {
    val (infoWhenCondTrue, infoWhenCondFalse) = extractTypeInfos(cond)
    val allSubjects = encapsulatedTypesData.keySet ++ infoWhenCondTrue.map(_.subject) ++ infoWhenCondFalse.map(_.subject)
    val unencapsulatedKnownIs = Map.newBuilder[Formula, ]
    for (subject <- allSubjects) {
      ???
    }
    ???
  }

  /**
   * @return (info when cond, info when !cond)
   */
  private def extractTypeInfos(cond: Formula): (Set[DataAddition], Set[DataAddition]) = cond match {
    case And(lhs, rhs) =>
      val (infoWhenLhs, infoWhenNotLhs) = extractTypeInfos(lhs)
      val (infoWhenRhs, infoWhenNotRhs) = extractTypeInfos(rhs)
      (infoWhenLhs ++ infoWhenRhs, Set.empty)
    case Or(lhs, rhs) =>
      val (infoWhenLhs, infoWhenNotLhs) = extractTypeInfos(lhs)
      val (infoWhenRhs, infoWhenNotRhs) = extractTypeInfos(rhs)
      (Set.empty, infoWhenNotLhs ++ infoWhenNotRhs)
    case Not(operand) =>
      val (infoWhenOperand, infoWhenNotOperand) = extractTypeInfos(operand)
      (infoWhenNotOperand, infoWhenOperand)
    case HasType(formula: TypedFormula, testedType) if PurityChecking.isPure(formula) =>
      formula.tpe match {
        case NamedType(tid, _, _) =>
          (Set(DataAddition(formula, List(tid), List.empty)),
            Set(DataAddition(formula, List.empty, List(tid))))
      }
    case _ => (Set.empty, Set.empty)
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
