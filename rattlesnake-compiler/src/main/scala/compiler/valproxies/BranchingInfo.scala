package compiler.valproxies

import compiler.identifiers.TypeIdentifier
import compiler.irs.SSA.Scope
import compiler.lang.Formulas.{Formula, IdValue}
import compiler.smt.Solver
import compiler.typing.Typer
import compiler.util.{SeqSet, mergeCombineInOrder}
import compiler.lang.Formulas.*
import compiler.valproxies.BoundMode.*

import scala.collection.SeqMap
import scala.util.boundary

final case class BranchingInfo(
                                smartcasts: SeqMap[Formula, SeqSet[TypeIdentifier]],
                                assumptions: SeqSet[Formula]
                              ) {

  def ++(that: BranchingInfo): BranchingInfo = BranchingInfo(
    this.smartcasts.mergeCombineInOrder(that.smartcasts)(_.concat(_)),
    this.assumptions.concat(that.assumptions)
  )

  def filteredStable(typer: Typer): BranchingInfo = BranchingInfo(
    smartcasts.filter((subject, _) => subject.isStable),
    assumptions.filter(_.isStable)
  )

  def boundFor(subject: IdValue, boundMode: BoundMode, solver: Solver): Option[Formula] = boundary {
    import compiler.lang.FormulasDsl.*
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

  def ofSmartcast(subject: Formula, tpe: TypeIdentifier): BranchingInfo =
    BranchingInfo(SeqMap(subject -> SeqSet(tpe)), SeqSet.empty)

  def ofAssumption(assumption: Formula): BranchingInfo =
    BranchingInfo(SeqMap.empty, SeqSet(assumption))


}
