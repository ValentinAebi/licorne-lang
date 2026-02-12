package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.{DatatypeSignature, Unencapsulated}
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}

import scala.collection.mutable

final class UnencapsulatedSmartcastingData(
                                            val subject: Formula,
                                            val rawType: NamedType,
                                            knownIs: Set[TypeIdentifier],
                                            knownIsNot: Set[TypeIdentifier],
                                            resolutionCtx: ResolutionContext,
                                            subtypingCtx: SubtypingContext
                                          ) extends SmartcastingData {
  private val canProveIsCache = mutable.Map.empty[TypeIdentifier, Boolean]
  private var mostPreciseTypeCache = Option.empty[Option[TypeIdentifier]]
  private var canProveIsNothingCache = Option.empty[Boolean]

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
            .developUnencapsulated(rawType.typeName)
            .flatMap { recordSignatures =>
              recordSignatures.find(sig => canProveIs(sig.id)).map(_.id)
            }
        mostPreciseTypeCache = Some(mostPreciseTypeOpt)
        mostPreciseTypeOpt
    }
  }
  
  def canProveIsNothing: Boolean = {
    canProveIsNothingCache match {
      case Some(value) => value
      case None =>
        val result =
          resolutionCtx.typesReasoningCache.developUnencapsulated(rawType.typeName) match {
            case Some(signatures) =>
              signatures.forall(sig => subtypingCtx.subToSuperSubst(sig.id, rawType.typeName).isEmpty)
            case None => false
          }
        canProveIsNothingCache = Some(result)
        result
    }
  }
  
  def withMoreInfo(knownIs: Set[TypeIdentifier], knownIsNot: Set[TypeIdentifier]): UnencapsulatedSmartcastingData =
    UnencapsulatedSmartcastingData(
      subject,
      rawType,
      this.knownIs ++ knownIs,
      this.knownIsNot ++ knownIsNot,
      resolutionCtx,
      subtypingCtx
    )

}
