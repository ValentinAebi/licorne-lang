package compiler.valproxies

import compiler.identifiers.TypeIdentifier
import compiler.irs.ssa.Formulas.*
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.reasoning.Solver
import compiler.typing.contexts.SubtypingContext
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult.*
import compiler.typing.smartcasting.TypesReasoningCache
import compiler.util.{SeqSet, mergeCombineInOrder}
import compiler.valproxies.BoundMode.*
import compiler.valproxies.BranchingInfo.SmartcastData

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
    import compiler.irs.ssa.FormulasDsl.*
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

    def tryToSmartcast(originalType: Type, typesReasoningCache: TypesReasoningCache, subtypingCtx: SubtypingContext): Option[Type] = originalType match {
      case NamedType(typeName, typeArgs, args) =>
        val candidatesOpt =
          typesReasoningCache.developUnencapsulated(typeName).map { records =>
            records.filterNot(r => knownIsNot.exists(forbiddenSuper => subtypingCtx.subToSuperSubst(r.id, forbiddenSuper).isDefined))
          }
        (candidatesOpt match {
          case Some(Nil) => Some(NothingType)
          case Some(recordSig :: Nil) =>
            subtypingCtx.checkDowncastTarget(originalType, recordSig.id).asOption
          case _ => None
        }) orElse boundary {
          for (tpe <- knownIs.reverse) {
            subtypingCtx.checkDowncastTarget(originalType, tpe) match {
              case CanDowncast(tpe) => boundary.break(Some(tpe))
              case CannotDowncast(reason) => ()
            }
          }
          None
        }
      case originalType => None
    }

  }

}
