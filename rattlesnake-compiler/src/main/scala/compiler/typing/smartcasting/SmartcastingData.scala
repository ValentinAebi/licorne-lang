package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.{Formula, TypedFormula}
import compiler.lang.Types.{NamedType, Type}
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}
import compiler.typing.smartcasting.SmartcastingData.DataAddition

trait SmartcastingData(resolutionCtx: ResolutionContext, subtypingCtx: SubtypingContext) {
  val rawTypedSubject: TypedFormula
  
  def rawType: Type = rawTypedSubject.tpe
  def subjectWithoutType: Formula = rawTypedSubject.formula

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

  def withMoreInfo(knownIs: Seq[TypeIdentifier], knownIsNot: Seq[TypeIdentifier]): this.type
  
  def withMoreInfo(dataAddition: DataAddition): this.type = {
    require(dataAddition.subject == this.subject)
    withMoreInfo(dataAddition.knownIs, dataAddition.knownIsNot)
  }
  
}

object SmartcastingData {
  
  final case class DataAddition(subject: TypedFormula, knownIs: Seq[TypeIdentifier], knownIsNot: Seq[TypeIdentifier])
  
}
