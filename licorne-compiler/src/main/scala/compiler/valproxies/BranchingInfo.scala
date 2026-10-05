package compiler.valproxies

import compiler.identifiers.TypeIdentifier
import compiler.irs.ircorne.Formulas.*
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.reasoning.{MeetJoinComputer, Solver}
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult.*
import compiler.typing.contexts.{ResolutionContext, SubtypingContext, TypeParamsContext}
import compiler.typing.smartcasting.TypesReasoningCache
import compiler.util.*
import compiler.valproxies.BoundMode.*
import compiler.valproxies.BranchingInfo.SmartcastData
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.SeqMap
import scala.util.boundary

final case class BranchingInfo(
                                smartcasts: SeqMap[Formula, SmartcastData],
                                assumptions: SeqSet[Formula]
                              ) {

  def ++(that: BranchingInfo): BranchingInfo = BranchingInfo(
    this.smartcasts.mergeCombineInOrder(that.smartcasts)(_ ++ _),
    this.assumptions.concat(that.assumptions)
  )

  def boundFor(subject: IdValue, boundMode: BoundMode, solver: Solver): Option[Formula] = boundary {
    import compiler.irs.ircorne.FormulasDsl.*
    // TODO try to find best bound instead of stopping at first bound found?
    assumptions.foreach {
      case LessOrEq(lhs, rhs) if boundMode == Upper && lhs == subject =>
        boundary.break(Some(rhs))
      case LessThan(lhs, rhs) if boundMode == Upper && lhs == subject =>
        boundary.break(Some(rhs - 1))
      case LessOrEq(lhs, rhs) if boundMode == Lower && rhs == subject =>
        boundary.break(Some(lhs))
      case LessThan(lhs, rhs) if boundMode == Lower && rhs == subject =>
        boundary.break(Some(lhs + 1))
      case _ => ()
    }
    None
  }

  def crossData(using globalValsCtx: GlobalValuesContext): BranchingInfo = {
    val newAssumptions = for {
      (subject, SmartcastData(knownIs, knownIsNot)) <- smartcasts
      tid <- knownIs
      objVal <- globalValsCtx.resolveObjectIfKnown(tid)
    } yield Equality(subject, objVal)
    val itVal = globalValsCtx.itValue
    val newKnownIs = (assumptions.toList.flatMap {
      case Equality(lhs: IdValue, rhs) =>
        globalValsCtx.getNameOfObject(lhs).map(rhs -> _)
      case _ => None
    } ++ assumptions.toList.flatMap {
      case Equality(lhs, rhs: IdValue) =>
        globalValsCtx.getNameOfObject(rhs).map(lhs -> _)
      case _ => None
    }).valuesGroupedByKey.mapVals(SmartcastData(_, Iterable.empty))
    val newKnownIsNot = (assumptions.toList.flatMap {
      case LogicalNot(Equality(lhs: IdValue, rhs)) =>
        globalValsCtx.getNameOfObject(lhs).map(rhs -> _)
      case _ => None
    } ++ assumptions.toList.flatMap {
      case LogicalNot(Equality(lhs, rhs: IdValue)) =>
        globalValsCtx.getNameOfObject(rhs).map(lhs -> _)
      case _ => None
    }).valuesGroupedByKey.mapVals(SmartcastData(Iterable.empty, _))
    this ++ BranchingInfo(SeqMap.from(newKnownIs), SeqSet.empty) ++ BranchingInfo(SeqMap.from(newKnownIsNot), SeqSet.empty) ++ BranchingInfo(SeqMap.empty, SeqSet(newAssumptions))
  }

}

object BranchingInfo {

  val empty: BranchingInfo = BranchingInfo(SeqMap.empty, SeqSet.empty)

  def ofPositiveSmartcast(subject: Formula, tpe: TypeIdentifier): BranchingInfo =
    BranchingInfo(SeqMap(subject -> SmartcastData(SeqSet(tpe), SeqSet.empty)), SeqSet.empty)

  def ofNegativeSmartcast(subject: Formula, tpe: TypeIdentifier): BranchingInfo =
    BranchingInfo(SeqMap(subject -> SmartcastData(SeqSet.empty, SeqSet(tpe))), SeqSet.empty)

  def ofAssumption(assumption: Formula): BranchingInfo =
    BranchingInfo(SeqMap.empty, SeqSet(assumption))

  final case class SmartcastData(knownIs: SeqSet[TypeIdentifier], knownIsNot: SeqSet[TypeIdentifier]) {

    def ++(that: SmartcastData): SmartcastData = SmartcastData(
      this.knownIs.concat(that.knownIs),
      this.knownIsNot.concat(that.knownIsNot)
    )

    def tryToSmartcast(originalType: Type, typesReasoningCache: TypesReasoningCache)
                      (using tpCtx: TypeParamsContext, subtypingCtx: SubtypingContext, resolCtx: ResolutionContext, meetJoin: MeetJoinComputer): Option[Type] = {

      def tryToSmartcastByExclusion(tids: List[TypeIdentifier]): Option[Type] = boundary {
        val candidates =
          tids.flatMap { tid =>
            typesReasoningCache.developUnencapsulated(tid) match {
              case Some(records) => records.map(_.id)
              case None => List(tid)
            }
          }.filterNot(tid => knownIsNot.exists(forbiddenSuper => subtypingCtx.subToSuperSubst(tid, forbiddenSuper).isDefined))
        candidates match {
          case Nil => Some(NothingType)
          case List(candidate) =>
            subtypingCtx.checkDowncastTarget(originalType, candidate, acceptTypeParamTarget = true).asOption.filter(_ != originalType)
          case _ => None
        }
      }

      def tryToSmartcastByInclusion: Option[Type] = boundary {
        for (tpe <- knownIs.reverse) {
          subtypingCtx.checkDowncastTarget(originalType, tpe, acceptTypeParamTarget = true) match {
            case CanDowncast(tpe) => boundary.break(Some(tpe))
            case CannotDowncast(reason) => ()
          }
        }
        None
      }

      def tryToSmartcast(tids: List[TypeIdentifier]): Option[Type] =
        tryToSmartcastByExclusion(tids).orElse(tryToSmartcastByInclusion)

      originalType match {
        case NamedType(typeName, typeArgs, Nil) => tryToSmartcast(List(typeName))
        case UnionType(types) =>
          types.asIterableOfType[NamedType]
            .flatMap(namedTypes => tryToSmartcast(namedTypes.map(_.typeName).toList))
        case _ => None
      }
    }

  }
  
  object SmartcastData {
    def apply(knownIs: Iterable[TypeIdentifier], knownIsNot: Iterable[TypeIdentifier]): SmartcastData =
      SmartcastData(SeqSet(knownIs), SeqSet(knownIsNot))
  }

}
