package compiler.typing.contexts

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.IdValue
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.*
import compiler.lang.Variance.*
import compiler.lang.{RuntimeTypeSignature, TypeParamInfo, TypeTypeParamInfo}
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.smt.Solver
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult.{CanDowncast, CannotDowncast}
import compiler.typing.contexts.SubtypingContext.{DowncastTargetCheckResult, SupertypesSubst}
import compiler.valproxies.ProxyStore

import scala.collection.mutable

final class SubtypingContext(
                              subtypingGraph: Graph[TypeIdentifier],
                              flattenedSupertypesSubstitutions: SupertypesSubst,
                              dealiasingCtx: DealiasingContext,
                              resolutionCtx: ResolutionContext,
                              solver: Solver,
                              proxyStore: ProxyStore,
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
                  CanDowncast(targetSig.toType(newTargetSubst))
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
    case _ if subT == superT => true
    case (NothingType, _) => true
    case (_, AnyType) => true
    case (_, UnitType) => true
    case (subT: NamedType, superT: NamedType) => isSubtype(subT, superT)
    case (IntRangeType(_, _), IntType) => true
    case (IntRangeType(subLbOpt, subUbOpt), IntRangeType(superLbOpt, superUbOpt)) =>
      superLbOpt.forall(superLb => subLbOpt.exists(subLb => solver.canProveLeq(superLb, subLb)))
        && superUbOpt.forall(superUb => subUbOpt.exists(subUb => solver.canProveLeq(subUb, superUb)))
    case (ClosureType(subParams, subResult), ClosureType(superParams, superResult)) =>
      subParams.size == superParams.size && subParams.zip(superParams).forall((subP, superP) => isSubtype(superP, subP)) && isSubtype(subResult, superResult)
    case (IntersectionType(subtypes), superT) =>
      subtypes.exists(isSubtype(_, superT))
    case (subT, IntersectionType(supertypes)) =>
      supertypes.forall(isSubtype(subT, _))
    case (UnionType(subtypes), superT) =>
      subtypes.forall(isSubtype(_, superT))
    case (subT, UnionType(supertypes)) =>
      supertypes.exists(isSubtype(subT, _))
    case _ => false
  }

  def isSubtype(subject: IdValue, subT: Type, superT: Type): Boolean = superT match {
    case IntRangeType(lowerBoundOpt, upperBoundOpt)
      if lowerBoundOpt.forall(lb => solver.canProveLeq(lb, subject))
        && upperBoundOpt.forall(ub => solver.canProveLeq(subject, ub)) => true
    case _ => isSubtype(subT, superT)
  }

  def isSubtype(subT: NamedType, superT: NamedType): Boolean = {
    val NamedType(subTId, subTTypeArgs, subTArgs) = subT
    val NamedType(superTId, superTTypeArgs, superTArgs) = superT
    subTArgs.isEmpty && superTArgs.isEmpty && (subToSuperSubst(subTId, superTId) match {
      case None => false
      case Some(subst) =>
        resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](superTId) match {
          case None => false
          case Some(superTSig) =>
            superTSig.typeParams.zip(superTTypeArgs).forall { (tParam, tArg) =>
              val expType = subst.apply(tParam.tid)
              tParam.variance match {
                case Invariant => tArg == expType
                case Covariant => isSubtype(tArg, expType)
                case Contravariant => isSubtype(expType, tArg)
              }
            }
        }
    })
  }

  def enforceIsSubtype(subT: Type, superT: Type, msg: String, posOpt: Option[Position]): Unit = {
    if (!isSubtype(subT, superT)) {
      er.reportError(msg, posOpt)
    }
  }

  def enforceIsSubtype(subject: IdValue, subT: Type, superT: Type, msg: String, posOpt: Option[Position]): Unit = {
    if (!isSubtype(subject, subT, superT)) {
      er.reportError(msg, posOpt)
    }
  }

  def enforceIsSubtypeExpAct(subT: Type, superT: Type, posDescr: String, posOpt: Option[Position]): Unit =
    enforceIsSubtype(dealiasingCtx.dealiasType(subT), dealiasingCtx.dealiasType(superT), s"$posDescr: expected $superT, found $subT", posOpt)

  def enforceIsSubtypeExpAct(subject: IdValue, subT: Type, superT: Type, posDescr: String, posOpt: Option[Position]): Unit = {
    val proxyDescr = proxyStore.getProxy(subject) match {
      case Some(proxy) => s"$proxy : "
      case None => ""
    }
    enforceIsSubtype(subject, dealiasingCtx.dealiasType(subT), dealiasingCtx.dealiasType(superT), s"$posDescr: expected $proxyDescr$superT, found $subT", posOpt)
  }

  def checkBounds(tParam: TypeParamInfo, tArg: Type): Boolean = {
    tParam.lowerBoundOpt.forall(lb => isSubtype(lb, tArg))
      && tParam.upperBoundOpt.forall(ub => isSubtype(tArg, ub))
  }

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
