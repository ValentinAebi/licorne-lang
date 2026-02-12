package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.lang.{DatatypeSignature, Unencapsulated}
import compiler.typing.contexts.ResolutionContext
import compiler.lang.Types.NamedType

import scala.collection.mutable

final class UnencapsulatedSmartcastingData(
                                            val subject: Formula,
                                            rawType: TypeIdentifier,
                                            knownIs: Set[TypeIdentifier],
                                            knownIsNot: Set[TypeIdentifier],
                                            resolutionCtx: ResolutionContext
                                          ) extends SmartcastingData {
  private val canProveIsCache = mutable.Map.empty[TypeIdentifier, Boolean]
  private var mostPreciseTypeCache = Option.empty[Option[TypeIdentifier]]

  def canProveIs(tid: TypeIdentifier): Boolean = {

    def computeCanProveIs(tid: TypeIdentifier): Boolean = {
      knownIs.contains(tid) || (resolutionCtx.resolveSignatureAs[Unencapsulated](tid) match {
        case Some(tSig) =>
          tSig.directSupertypes.exists {
            case NamedType(superTid, _, _) =>
              canProveIs(superTid) && (resolutionCtx.resolveSignatureAs[DatatypeSignature](superTid) match {
                case Some(superTSig) => superTSig.directSubtypes.diff(knownIsNot) == Set(tid)
                case None => false
              })
          }
        case None => false
      })
    }

    canProveIsCache.getOrElseUpdate(tid, computeCanProveIs(tid))
  }

  def mostPreciseType(): Option[TypeIdentifier] = {
    mostPreciseTypeCache match {
      case Some(value) => value
      case None =>
        val mostPreciseTypeOpt =
          resolutionCtx.typesReasoningCache
            .developUnencapsulated(rawType)
            .flatMap { recordSignatures =>
              recordSignatures.find(sig => canProveIs(sig.id)).map(_.id)
            }
        mostPreciseTypeCache = Some(mostPreciseTypeOpt)
        mostPreciseTypeOpt
    }
  }
  
  def withMoreInfo(knownIs: Set[TypeIdentifier], knownIsNot: Set[TypeIdentifier]): UnencapsulatedSmartcastingData =
    UnencapsulatedSmartcastingData(
      subject,
      rawType,
      this.knownIs ++ knownIs,
      this.knownIsNot ++ knownIsNot,
      resolutionCtx
    )

}
