package compiler.reasoning

import compiler.irs.ircorne.Formulas.{Formula, IdValue}
import compiler.irs.ircorne.IRcorne.Scope
import compiler.reasoning.Solver
import Recurrence.Monotonicity
import Recurrence.Monotonicity.*
import compiler.typing.Typer
import compiler.typing.contexts.{ResolutionContext, TypeParamsContext}
import compiler.valproxies.ProxyStore


final case class Recurrence(init: Formula, induct: Formula, inductVal: IdValue) {
  private var monotonicityOpt: Option[Monotonicity] = None

  def computeMonotonicity(typer: Typer, solver: Solver, scope: Scope)(using TypeParamsContext, ResolutionContext, ProxyStore): Monotonicity = monotonicityOpt match {
    case Some(monotonicity) => monotonicity
    case None =>
      val nonIncreasing = isProvablyNonIncreasing(typer, solver, scope)
      val nonDecreasing = isProvablyNonDecreasing(typer, solver, scope)
      val monotonicity =
        if nonIncreasing && nonDecreasing then Constant
        else if nonDecreasing then NonDecreasing
        else if nonIncreasing then NonIncreasing
        else NonMonotonous
      monotonicityOpt = Some(monotonicity)
      monotonicity
  }

  private def isProvablyNonDecreasing(typer: Typer, solver: Solver, scope: Scope)
                                     (using TypeParamsContext, ResolutionContext, ProxyStore): Boolean =
    solver.checkSat() && solver.onNewFrame {
      solver.acceptingPhisForInts {
        typeAllSubformulas(induct, typer, scope)
        solver.assertLt(induct, inductVal)
        solver.checkUnsat()
      }
    }

  private def isProvablyNonIncreasing(typer: Typer, solver: Solver, scope: Scope)
                                     (using TypeParamsContext, ResolutionContext, ProxyStore): Boolean =
    solver.checkSat() && solver.onNewFrame {
      solver.acceptingPhisForInts {
        typeAllSubformulas(induct, typer, scope)
        solver.assertLt(inductVal, induct)
        solver.checkUnsat()
      }
    }

  private def typeAllSubformulas(formula: Formula, typer: Typer, scope: Scope)(using typeParamsCtx: TypeParamsContext, resolCtx: ResolutionContext, proxyStore: ProxyStore) = {
    typer.typeFormula(proxyStore.developDeep(formula, acceptPhis = true).getOrElse(formula), scope, None, suspendReporting = true)
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
