package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.{Formula, TypedFormula}
import compiler.lang.Types.{NamedType, Type}
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}

final class EncapsulatedSmartcastingData(
                                          val rawTypedSubject: TypedFormula,
                                          val mostPreciseTypeId: TypeIdentifier,
                                          knownTypes: Set[TypeIdentifier],
                                          resolutionCtx: ResolutionContext,
                                          subtypingCtx: SubtypingContext
                                        ) extends SmartcastingData(resolutionCtx, subtypingCtx) {

  override def mostPreciseTypeIdOpt: Option[TypeIdentifier] =
    Some(mostPreciseTypeId)

  def canProveIs(tid: TypeIdentifier): Boolean = {
    tid == rawType.typeName || tid == mostPreciseTypeIdOpt || knownTypes.contains(tid)
  }

  def withMoreInfo(knownIs: Seq[TypeIdentifier], knownIsNot: Seq[TypeIdentifier]): EncapsulatedSmartcastingData = {
    val newMostPreciseTypeId = knownIs.lastOption.getOrElse(mostPreciseTypeId)
    EncapsulatedSmartcastingData(subject, rawType, mostPreciseTypeId, knownTypes ++ knownIs, resolutionCtx, subtypingCtx)
  }
  
}
