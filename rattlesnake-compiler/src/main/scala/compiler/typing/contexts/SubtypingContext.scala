package compiler.typing.contexts

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.{ConstFormula, Formula, IdValue, IntermediateIdValue}
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
import compiler.util.zipCommons
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
    dealiasingCtx.dealiasType(originalType).principalType match {
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

  // TODO memoize? But we need to take smartcasts into account
  def isSubtype(subT: Type, superT: Type): Boolean = (dealiasingCtx.dealiasType(subT), dealiasingCtx.dealiasType(superT)) match {
    case (tv: TypeVariable, superT) =>
      if (tv.isResolved) {
        tv.lock()
        isSubtype(tv.substitutedIfResolved, superT)
      } else {
        tv.resolve(superT)
        tv.lock()
        true
      }
    case (subT, tv: TypeVariable) =>
      if (tv.isResolved){
        tv.lock()
        isSubtype(subT, tv.substitutedIfResolved)
      } else {
        tv.resolve(subT)
        tv.lock()
        true
      }
    case (subT, superT) if subT == superT => true
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

  def isSubtype(subject: Formula, subT: Type, superT: Type): Boolean =
    isSubtype(subT, superT) || canProveHasType(subject, superT)

  def canProveHasType(subject: Formula, tpe: Type): Boolean = tpe match {
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      val subjectProxyOpt = proxyStore.getProxyIfIdValue(subject)
      lowerBoundOpt.forall(lb => solver.canProveLeq(lb, subject) || subjectProxyOpt.exists(subjectProxy => solver.canProveLeq(lb, subjectProxy)))
        && upperBoundOpt.forall(ub => solver.canProveLeq(subject, ub) || subjectProxyOpt.exists(subjectProxy => solver.canProveLeq(subjectProxy, ub)))
    case UnionType(types) =>
      types.exists(canProveHasType(subject, _))
    case IntersectionType(types) =>
      types.forall(canProveHasType(subject, _))
    case _ => false
  }

  def isSubtype(subT: NamedType, superT: NamedType): Boolean = {
    val NamedType(subTId, subTTypeArgs, subTArgs) = subT
    val NamedType(superTId, superTTypeArgs, superTArgs) = superT
    subTArgs.isEmpty && superTArgs.isEmpty && (subToSuperSubst(subTId, superTId) match {
      case None => false
      case Some(subToSuperParamsSubst) =>
        (resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](subTId), resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](superTId)) match {
          case (Some(subTSig), Some(superTSig)) =>
            val subTSubst = subTSig.typeParams.zipCommons(subTTypeArgs).toMap
            val subst = Map.from(
              for ((paramInSuper, argInSuper) <- subToSuperParamsSubst) yield
                paramInSuper -> (argInSuper match {
                  case NamedType(argInSuperId, Nil, Nil) =>
                    subTSubst.find((tParam, tArg) => tParam.tid == argInSuperId) match {
                      case Some(_, tArg) => tArg
                      case None => argInSuper
                    }
                  case _ => argInSuper
                })
            )
            superTTypeArgs.zip(superTSig.typeParams).forall { (expTypeArg, tParam) =>
              val actTypeArg = subst.apply(tParam.tid)
              tParam.variance match {
                case Invariant => actTypeArg.withTypeVarsExpanded == expTypeArg.withTypeVarsExpanded
                case Covariant => isSubtype(actTypeArg, expTypeArg)
                case Contravariant => isSubtype(expTypeArg, actTypeArg)
              }
            }
          case _ => false
        }
    })
  }

  def enforceIsSubtype(subT: Type, superT: Type, msg: => String, posOpt: Option[Position]): Unit = {
    if (!isSubtype(subT, superT)) {
      er.reportError(msg, posOpt)
    }
  }

  def enforceIsSubtype(subject: Formula, subT: Type, superT: Type, msg: => String, posOpt: Option[Position]): Unit = {
    if (!isSubtype(subject, subT, superT)) {
      er.reportError(msg, posOpt)
    }
  }

  def enforceIsSubtypeExpAct(subT: Type, superT: Type, posDescr: String, posOpt: Option[Position]): Unit =
    enforceIsSubtype(dealiasingCtx.dealiasType(subT), dealiasingCtx.dealiasType(superT), s"$posDescr: expected $superT, found $subT", posOpt)

  def enforceIsSubtypeExpAct(subject: Formula, subT: Type, superT: Type, posDescr: String, posOpt: Option[Position]): Unit = {
    lazy val foundDescr = subject match {
      case subject: IntermediateIdValue =>
        proxyStore.getProxy(subject) match {
          case Some(proxy: ConstFormula) => proxy.toString
          case Some(proxy) => s"$proxy : $subT"
          case None => subT.toString
        }
      case subject => s"$subject : $subT"
    }
    enforceIsSubtype(subject, dealiasingCtx.dealiasType(subT), dealiasingCtx.dealiasType(superT), s"$posDescr: expected $superT, found $foundDescr", posOpt)
  }

  def enforceIsSubtypeExpAct(subjectOpt: Option[Formula], subT: Type, superT: Type, posDescr: String, posOpt: Option[Position]): Unit = subjectOpt match {
    case Some(subject) => enforceIsSubtypeExpAct(subject, subT, superT, posDescr, posOpt)
    case None => enforceIsSubtypeExpAct(subT, superT, posDescr, posOpt)
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
