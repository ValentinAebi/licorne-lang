package compiler.typing.smartcasting

import compiler.lang.Formulas.Formula
import compiler.lang.Types.Type

final class EncapsulatedSmartcastingData(
                                          val subject: Formula,
                                          rawType: Type,
                                          val mostPreciseType: Type,
                                          knownTypes: Set[Type]
                                        ) {

  def canProveIs(tpe: Type): Boolean =
    tpe == rawType || tpe == mostPreciseType || knownTypes.contains(tpe)

}
