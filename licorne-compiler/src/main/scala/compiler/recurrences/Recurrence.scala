package compiler.recurrences

import compiler.irs.ssa.Formulas.{Formula, IdValue}
import compiler.recurrences.Recurrence.Monotonicity
import compiler.recurrences.Recurrence.Monotonicity.*
import compiler.smt.Solver


final case class Recurrence(init: Formula, induct: Formula, inductVal: IdValue) {
  private var monotonicityOpt: Option[Monotonicity] = None
  
  def computeMonotonicity(solver: Solver): Monotonicity = monotonicityOpt match {
    case Some(monotonicity) => monotonicity
    case None =>
      val nonIncreasing = isProvablyNonIncreasing(solver)
      val nonDecreasing = isProvablyNonDecreasing(solver)
      val monotonicity =
        if nonIncreasing && nonDecreasing then Constant
        else if nonDecreasing then NonDecreasing
        else if nonIncreasing then NonIncreasing
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
    case Constant, NonDecreasing, NonIncreasing, NonMonotonous
  }

}
