package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.{Formula, TypedFormula}
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.{DatatypeSignature, Unencapsulated}
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}

import scala.collection.mutable

final class UnencapsulatedSmartcastingData(
                                            val rawTypedSubject: TypedFormula,
                                            knownIs: Set[TypeIdentifier],
                                            knownIsNot: Set[TypeIdentifier],
                                            resolutionCtx: ResolutionContext,
                                            subtypingCtx: SubtypingContext
                                          ) extends SmartcastingData(resolutionCtx, subtypingCtx) {
  private val canProveIsCache = mutable.Map.empty[TypeIdentifier, Boolean]
  private var mostPreciseTypeCache = Option.empty[Option[TypeIdentifier]]
  private var canProveIsNothingCache = Option.empty[Boolean]

  override def canProveIs(tid: TypeIdentifier): Boolean = {

    def computeCanProveIs(tid: TypeIdentifier): Boolean = {
      knownIs.contains(tid) || (resolutionCtx.resolveTypeSigAs[Unencapsulated](tid) match {
        case Some(tSig) =>
          tSig.directSupertypes.exists {
            case NamedType(superTid, _, _) =>
              canProveIs(superTid) && (resolutionCtx.resolveTypeSigAs[DatatypeSignature](superTid) match {
                case Some(superTSig) => superTSig.directSubtypes.diff(knownIsNot) == Set(tid)
                case None => false
              })
          }
        case None => false
      })
    }

    canProveIsCache.getOrElseUpdate(tid, computeCanProveIs(tid))
  }

  def mostPreciseTypeIdOpt: Option[TypeIdentifier] = {
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
  
  def withMoreInfo(knownIs: Seq[TypeIdentifier], knownIsNot: Seq[TypeIdentifier]): UnencapsulatedSmartcastingData =
    UnencapsulatedSmartcastingData(
      subject,
      rawType,
      this.knownIs ++ knownIs,
      this.knownIsNot ++ knownIsNot,
      resolutionCtx,
      subtypingCtx
    )

}
