package compiler.reasoning

import compiler.irs.ircorne.Formulas.{Formula, IdValue, IntConst, Phi, Plus, Times}
import compiler.irs.ircorne.IRcorne.Scope
import compiler.reasoning.Solver
import compiler.irs.ircorne.Formulas
import compiler.typing.Typer
import compiler.typing.contexts.{ResolutionContext, TypeParamsContext}
import compiler.util.SeqSet
import compiler.valproxies.ProxyStore


final case class VariableEvolution private(bases: SeqSet[Formula], induct: Formula, inductVal: IdValue, isRecurrence: Boolean) {
  require(bases.nonEmpty)
  require(!isRecurrence || bases.size == 1)

  private var boundsOpt: Option[Option[(Iterable[Formula], Iterable[Formula])]] = None
  private var lastClosedFormCacheForToString: Option[(IdValue, Formula)] = None

  def isTrivialIncByOne: Boolean = isRecurrence && bases.head == IntConst(0) && {
    val lin = FormulasSimplification.linearize(induct)
    lin.size == 2 && lin.get(inductVal).contains(1) && lin.get(IntConst(1)).contains(1)
  }

  def computeMonotonicity(typer: Typer, solver: Solver, body: Scope)
                         (using tpCtx: TypeParamsContext, resolCtx: ResolutionContext, proxyStore: ProxyStore): Option[(Iterable[Formula], Iterable[Formula])] = boundsOpt match {
    case Some(bounds) => bounds
    case None =>
      val expandedBases = bases.map(b => proxyStore.developDeep(b))
      val nonDecreasing = inductIsProvablyNonDecreasing(typer, solver, body)
      val nonIncreasing = inductIsProvablyNonIncreasing(typer, solver, body)
      val mins = if nonDecreasing then solver.discardNonMins(expandedBases) else List.empty
      val maxs = if nonIncreasing then solver.discardNonMaxs(expandedBases) else List.empty
      val bounds = Option.when(nonIncreasing || nonDecreasing)(mins, maxs)
      boundsOpt = Some(bounds)
      bounds
  }

  def asClosedForm(iterIdx: IdValue): Option[Formula] = {
    val closedFormOpt = computeClosedForm(iterIdx)
    closedFormOpt.foreach { closedForm =>
      lastClosedFormCacheForToString = Some(iterIdx, closedForm)
    }
    closedFormOpt
  }

  private def computeClosedForm(iterIdx: IdValue): Option[Formula] = if (isRecurrence) {
    val init = bases.head
    // TODO this could maybe be extended to reason about powers of program terms
    val linInduct = FormulasSimplification.linearize(induct)
    Option.when(linInduct.get(inductVal).contains(1) && linInduct.count(_._1.idValsDependencies.contains(inductVal)) == 1) {
      // induction: i -> i + cst
      val cstTerms = linInduct.filter(_._1 != inductVal)
      if cstTerms.isEmpty then init
      else {
        val cst = cstTerms.map((f, arity) => Times(f, IntConst(arity))).reduceLeft[Formula](Plus(_, _))
        FormulasSimplification.simplifyFormula(Plus(init, Times(cst, iterIdx)))
      }
    }
  } else None

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
    val expanded = proxyStore.developDeep(formula, acceptPhis = true)
    typer.typeFormula(expanded, body, None, suspendReporting = true)
    expanded
  }

  override def toString: String = {
    val recurDescr = if isRecurrence then " (recurrence)" else ""
    s"[bases = ${bases.mkString(",")}, induct($inductVal) = $induct]$recurDescr" ++ (boundsOpt match {
      case Some(Some(lowerBounds, upperBounds)) =>
        s" (lower: ${lowerBounds.mkString(",")} ; upper: ${upperBounds.mkString(",")})"
      case _ => ""
    }) ++ (lastClosedFormCacheForToString match {
      case Some(iterIdx, closedForm) => s" closed-form($iterIdx): $closedForm"
      case _ => ""
    })
  }

}

object VariableEvolution {

  def computeFrom(init: Formula, induct: Formula, inductVal: IdValue): VariableEvolution = {
    val (inducts, otherInits) = induct.flattenPhis.partition(_.idValsDependencies.contains(inductVal))
    VariableEvolution(SeqSet(init :: otherInits).filter(_ != inductVal), inducts.filter(_ != inductVal) match {
      case List(singleInduct) => singleInduct
      case inducts => Phi(inducts)
    }, inductVal, isRecurrence = !induct.isInstanceOf[Phi] && otherInits.isEmpty)
  }

}
