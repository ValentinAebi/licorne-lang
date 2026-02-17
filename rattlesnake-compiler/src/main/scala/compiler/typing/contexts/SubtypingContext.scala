package compiler.typing.contexts

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.lang.{RuntimeTypeSignature, TypeTypeParamInfo}
import compiler.lang.Types.{NamedType, PrincipalType, Type}
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult.{CanDowncast, CannotDowncast}
import compiler.typing.contexts.SubtypingContext.{DowncastTargetCheckResult, SupertypesSubst}

import scala.collection.mutable

final class SubtypingContext(
                              subtypingGraph: Graph[TypeIdentifier],
                              flattenedSupertypesSubstitutions: SupertypesSubst,
                              dealiasingCtx: DealiasingContext,
                              resolutionCtx: ResolutionContext,
                              er: ErrorReporter
                            )(using CompilationStep) {

  def subToSuperSubst(subT: TypeIdentifier, superT: TypeIdentifier): Option[Map[TypeIdentifier, Type]] = {
    if subT == superT then resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](subT).map {
      _.typeParams.map {
        case TypeTypeParamInfo(tid, variance, upperBounds, lowerBounds) =>
          tid -> NamedType(tid, List.empty, List.empty)
      }.toMap
    } else for {
      subTSupers <- flattenedSupertypesSubstitutions.get(subT)
      superSubst <- subTSupers.get(superT)
    } yield superSubst
  }

  def isEnumCaseOf(subId: TypeIdentifier, superId: TypeIdentifier): Boolean =
    subToSuperSubst(subId, superId).isDefined

  // TODO when adding refinements on NamedTypes (typically, non-nullity), add cases for them here
  def checkDowncastTarget(originalType: Type, targetId: TypeIdentifier): DowncastTargetCheckResult = {
    originalType match {
      case NamedType(originId, originTypeArgs, Nil) =>
        resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](targetId) match {
          case None =>
            CannotDowncast(s"type $targetId not found")
          case Some(targetSig) =>
            subToSuperSubst(targetId, originId) match {
              case None => CannotDowncast(s"$targetId does not subtype $originId")
              case Some(targetToOrigSubst) =>
                val origSig = resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](originId).get
                val siteSubst = origSig.typeParams.map(_._1).zip(originTypeArgs).toMap
                val newTargetSubstB = Map.newBuilder[TypeIdentifier, Type]
                for ((tInOrig, tInTarget) <- targetToOrigSubst) {
                  tInTarget match {
                    case NamedType(tInTarget, Nil, Nil) =>
                      for {
                        varianceInOrig <- origSig.varianceOf(tInOrig)
                        varianceInTarget <- targetSig.varianceOf(tInTarget)
                        if varianceInOrig == varianceInTarget
                      } do {
                        newTargetSubstB.addOne(tInTarget -> siteSubst.apply(tInOrig))
                      }
                    case _ => ()
                  }
                }
                val newTargetSubst = newTargetSubstB.result()
                val uncoveredTypeParams = targetSig.typeParams.map(_._1).toSet -- newTargetSubst.keySet
                if (uncoveredTypeParams.isEmpty) {
                  targetSig.toType(newTargetSubst, Map.empty) match {
                    case namedType: NamedType => CanDowncast(namedType)
                    case tpe => CannotDowncast(s"type $tpe is not eligible for downcasting")
                  }
                } else {
                  CannotDowncast(s"cannot infer type argument(s) for type parameter(s) ${uncoveredTypeParams.mkString(", ")} of tested type $targetId")
                }
            }
        }
      case _ =>
        CannotDowncast(s"tested type $originalType is unresolved or primitive")
    }
  }

  def isValidDowncastTarget(downcastTarget: NamedType, regularType: NamedType): Boolean =
    checkDowncastTarget(regularType, downcastTarget.typeName).isPositive(downcastTarget)

  // TODO memoize? But we need to take smartcasts into account
  def isSubtype(subT: Type, superT: Type): Boolean = (subT, superT) match {
    case (_, _) => ???
  }

  def enforceIsSubtype(subT: Type, superT: Type, msg: String, posOpt: Option[Position]): Unit = {
    if (!isSubtype(subT, superT)) {
      er.reportError(msg, posOpt)
    }
  }
  
  def enforceIsSubtypeExpAct(subT: Type, superT: Type, posDescr: String, posOpt: Option[Position]): Unit =
    enforceIsSubtype(subT, superT, s"$posDescr: expected $superT, found $subT", posOpt)

}

object SubtypingContext {

  type SupertypesSubst = mutable.SeqMap[TypeIdentifier, mutable.SeqMap[TypeIdentifier, Map[TypeIdentifier, Type]]]

  enum DowncastTargetCheckResult {
    case CanDowncast(tpe: NamedType)
    case CannotDowncast(reason: String)

    def asOption: Option[NamedType] = this match {
      case CanDowncast(tpe) => Some(tpe)
      case CannotDowncast(reason) => None
    }

    def isPositive(tpe: Type): Boolean = this match {
      case CanDowncast(actType) => actType == tpe
      case CannotDowncast(reason) => false
    }

  }

}
