package compiler.reasoning

import compiler.irs.ircorne.Formulas.{Formula, IdValue, Phi}
import compiler.irs.ircorne.IRcorne.Scope
import compiler.reasoning.Solver
import compiler.irs.ircorne.Formulas
import compiler.typing.Typer
import compiler.typing.contexts.{ResolutionContext, TypeParamsContext}
import compiler.util.SeqSet
import compiler.valproxies.ProxyStore


final case class Recurrence private(bases: SeqSet[Formula], induct: Formula, inductVal: IdValue) {
  private var boundsOpt: Option[Option[(Iterable[Formula], Iterable[Formula])]] = None

  def computeMonotonicity(typer: Typer, solver: Solver, body: Scope)
                         (using tpCtx: TypeParamsContext, resolCtx: ResolutionContext, proxyStore: ProxyStore): Option[(Iterable[Formula], Iterable[Formula])] = boundsOpt match {
    case Some(bounds) => bounds
    case None =>
      val expandedBases = bases.map(b => proxyStore.developDeep(b).getOrElse(b))
      val nonDecreasing = inductIsProvablyNonDecreasing(typer, solver, body)
      val nonIncreasing = inductIsProvablyNonIncreasing(typer, solver, body)
      val mins = if nonDecreasing then solver.discardNonMins(expandedBases) else List.empty
      val maxs = if nonIncreasing then solver.discardNonMaxs(expandedBases) else List.empty
      val bounds = Option.when(nonIncreasing || nonDecreasing)(mins, maxs)
      boundsOpt = Some(bounds)
      bounds
  }

  private def inductIsProvablyNonDecreasing(typer: Typer, solver: Solver, body: Scope)
                                     (using TypeParamsContext, ResolutionContext, ProxyStore): Boolean =
    solver.checkSat() && solver.onNewFrame {
      solver.acceptingPhisForInts {
        solver.assertLt(expandedAndTyped(induct, typer, body), inductVal)
        solver.checkUnsat()
      }
    }

  private def inductIsProvablyNonIncreasing(typer: Typer, solver: Solver, body: Scope)
                                     (using TypeParamsContext, ResolutionContext, ProxyStore): Boolean =
    solver.checkSat() && solver.onNewFrame {
      solver.acceptingPhisForInts {
        solver.assertLt(inductVal, expandedAndTyped(induct, typer, body))
        solver.checkUnsat()
      }
    }

  private def expandedAndTyped(formula: Formula, typer: Typer, body: Scope)(using typeParamsCtx: TypeParamsContext, resolCtx: ResolutionContext, proxyStore: ProxyStore): Formula = {
    val expanded = proxyStore.developDeep(formula, acceptPhis = true).getOrElse(formula)
    typer.typeFormula(expanded, body, None, suspendReporting = true)
    expanded
  }

  override def toString: String = {
    val invariantDescr = s"[bases = ${bases.mkString(",")}, induct($inductVal) = $induct]"
    boundsOpt match {
      case Some(Some(lowerBounds, upperBounds)) =>
        s"$invariantDescr (lower: ${lowerBounds.mkString(",")} ; upper: ${upperBounds.mkString(",")})"
      case _ => invariantDescr
    }
  }

}

object Recurrence {

  def computeFrom(init: Formula, induct: Formula, inductVal: IdValue): Recurrence = {
    val (inducts, otherInits) = induct.flattenPhis.partition(_.idValsDependencies.contains(inductVal))
    Recurrence(SeqSet(init :: otherInits).filter(_ != inductVal), inducts.filter(_ != inductVal) match {
      case List(singleInduct) => singleInduct
      case inducts => Phi(inducts)
    }, inductVal)
  }

}
