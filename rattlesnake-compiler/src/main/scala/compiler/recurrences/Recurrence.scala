package compiler.recurrences

import compiler.lang.Formulas.{Formula, IdValue}
import compiler.recurrences.Recurrence.Monotonicity
import compiler.recurrences.Recurrence.Monotonicity.*
import compiler.smt.Solver


final case class Recurrence(init: Formula, induct: Formula, inductVal: IdValue) {
  private var monotonicityOpt: Option[Monotonicity] = None

  // FIXME
  def computeMonotonicity(solver: Solver): Monotonicity = monotonicityOpt match {
    case Some(monotonicity) => monotonicity
    case None =>
      val monotonicity =
        if isProvablyNonIncreasing(solver) then NonIncreasing
        else if isProvablyNonDecreasing(solver) then NonDecreasing
        else NonMonotonous
      monotonicityOpt = Some(monotonicity)
      monotonicity
  }

  private def isProvablyNonDecreasing(solver: Solver): Boolean = solver.checkSat() && solver.onNewFrame {
    solver.assertLt(induct, inductVal)
    solver.checkUnsat()
  }

  private def isProvablyNonIncreasing(solver: Solver): Boolean = solver.checkSat() && solver.onNewFrame {
    solver.assertLt(inductVal, induct)
    solver.checkUnsat()
  }

  override def toString: String = {
    val baseStr = s"[init = $init, induct($inductVal) = $induct]"
    monotonicityOpt match {
      case Some(monotonicity) =>
        s"$baseStr ($monotonicity)"
      case None => baseStr
    }
  }

}

object Recurrence {

  enum Monotonicity {
    case NonIncreasing, NonDecreasing, NonMonotonous
  }

}
