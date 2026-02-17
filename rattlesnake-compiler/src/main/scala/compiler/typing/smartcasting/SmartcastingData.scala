package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.lang.Types.{NamedType, Type}
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}

trait SmartcastingData(resolutionCtx: ResolutionContext, subtypingCtx: SubtypingContext) {
  val subject: Formula
  val rawType: NamedType

  def canProveIs(tid: TypeIdentifier): Boolean

  def mostPreciseTypeIdOpt: Option[TypeIdentifier]

  def canProveIs(tpe: NamedType): Boolean = tpe match {
    case tpe@NamedType(typeName, _, _) =>
      canProveIs(typeName) && subtypingCtx.isValidDowncastTarget(tpe, rawType)
    case _ => false
  }

  def mostPreciseType: Option[NamedType] = {
    for {
      mostPreciseTypeId <- mostPreciseTypeIdOpt
      castType <- subtypingCtx.checkDowncastTarget(rawType, mostPreciseTypeId).asOption
    } yield castType
  }
  
}

object SmartcastingData {
  
  final case class DataAddition(formula: Formula, knownIs: Set[TypeIdentifier], knownIsNot: Set[TypeIdentifier])
  
}
