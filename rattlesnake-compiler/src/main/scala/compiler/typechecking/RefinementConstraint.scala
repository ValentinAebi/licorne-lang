package compiler.typechecking

import compiler.reporting.Position
import lang.Values.{Formula, IdValue}

import scala.collection.mutable

final case class RefinementConstraint(subItVal: Option[IdValue], subRefinement: Formula,
                                      superItVal: Option[IdValue], superRefinement: Formula,
                                      errorMsg: String, posOpt: Option[Position])

object RefinementConstraint {

  final class Collector {
    private val constraints = mutable.ListBuffer.empty[RefinementConstraint]

    def saveConstraint(constraint: RefinementConstraint): Unit = {
      constraints.addOne(constraint)
    }

  }

}
