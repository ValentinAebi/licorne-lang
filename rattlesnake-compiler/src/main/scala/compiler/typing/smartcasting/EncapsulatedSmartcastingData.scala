package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.lang.Types.{NamedType, Type}
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}

final class EncapsulatedSmartcastingData(
                                          val subject: Formula,
                                          val rawType: NamedType,
                                          val mostPreciseTypeId: TypeIdentifier,
                                          knownTypes: Set[TypeIdentifier],
                                          resolutionCtx: ResolutionContext,
                                          subtypingCtx: SubtypingContext
                                        ) extends SmartcastingData(resolutionCtx, subtypingCtx) {

  def canProveIs(tid: TypeIdentifier): Boolean = {
    tid == rawType.typeName || tid == mostPreciseTypeId || knownTypes.contains(tid)
  }
  
}
