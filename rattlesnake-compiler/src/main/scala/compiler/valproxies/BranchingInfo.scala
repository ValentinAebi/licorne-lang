package compiler.valproxies

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.typing.Typer
import compiler.util.{SeqSet, mergeCombineInOrder}

import scala.collection.SeqMap

final case class BranchingInfo(
                                smartcasts: SeqMap[Formula, SeqSet[TypeIdentifier]],
                                assumptions: SeqSet[Formula]
                              ) {

  def ++(that: BranchingInfo): BranchingInfo = BranchingInfo(
    this.smartcasts.mergeCombineInOrder(that.smartcasts)(_.concat(_)),
    this.assumptions.concat(that.assumptions)
  )

  def filteredStable(typer: Typer): BranchingInfo = BranchingInfo(
    smartcasts.filter((subject, _) => typer.isStable(subject)),
    assumptions.filter(typer.isStable)
  )

}

object BranchingInfo {

  val empty: BranchingInfo = BranchingInfo(SeqMap.empty, SeqSet.empty)

  def ofSmartcast(subject: Formula, tpe: TypeIdentifier): BranchingInfo =
    BranchingInfo(SeqMap(subject -> SeqSet(tpe)), SeqSet.empty)

  def ofAssumption(assumption: Formula): BranchingInfo =
    BranchingInfo(SeqMap.empty, SeqSet(assumption))

}
