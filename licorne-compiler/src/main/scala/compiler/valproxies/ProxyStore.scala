package compiler.valproxies

import compiler.irs.ssa.Formulas
import compiler.irs.ssa.SSA.Scope
import Formulas.*
import compiler.typing.Typer
import compiler.typing.contexts.DealiasingContext

import scala.collection.mutable


final class ProxyStore {
  private val proxies = mutable.Map.empty[IdValue, Formula]
  private val possiblyImpureClosures = mutable.Map.empty[IdValue, PureClosureValue]

  def hasProxyFor(idVal: IdValue): Boolean = proxies.contains(idVal)

  def saveProxy(idVal: IdValue, proxyOpt: Option[Formula]): Unit = proxyOpt.foreach { proxy =>
    saveProxy(idVal, proxy)
  }

  def saveProxy(idVal: IdValue, proxy: Formula): Unit = {
    if (proxies.contains(idVal)) {
      throw IllegalStateException(s"proxy already set for value $idVal")
    }
    proxies(idVal) = proxy
  }

  def savePossiblyImpureClosure(idVal: IdValue, closure: PureClosureValue): Unit = {
    possiblyImpureClosures.put(idVal, closure)
  }

  def validateClosurePurity(idVal: IdValue): Unit = {
    possiblyImpureClosures.get(idVal).foreach { closure =>
      proxies.put(idVal, closure)
    }
  }

  def developDeep(formula: Formula, bypassPurityChecks: Boolean = false): Option[Formula] =
    dev(formula, developLocals = true, bypassPurityChecks)

  def developNearest(formula: Formula, bypassPurityChecks: Boolean = false): Option[Formula] =
    dev(formula, developLocals = false, bypassPurityChecks)

  // TODO memoize
  private def dev(formula: Formula, developLocals: Boolean, bypassPurityChecks: Boolean): Option[Formula] = {
    val stepRes: Option[Formula] = formula match {
      case idValue: (ParamIdValue | UninterpretedConstIdValue) => Some(idValue)
      case idValue: (ValIdValue | VarIdValue) if !developLocals => Some(idValue)
      case idValue: IdValue if proxies.contains(idValue) => Some(proxies.apply(idValue))
      case idValue: IdValue => None
      case cst: ConstFormula => Some(cst)
      case Select(owner, field) if bypassPurityChecks || field.isResolvedAndStable => for {
        owp <- dev(owner, developLocals, bypassPurityChecks)
      } yield Select(owp, field)
      case FunCall(receiver, func, typeArgs, args) if bypassPurityChecks || func.isResolvedAndPure =>
        for {
          rcp <- dev(receiver, developLocals, bypassPurityChecks)
          argsp <- devAll(args, developLocals, bypassPurityChecks)
        } yield FunCall(rcp, func, typeArgs, argsp)
      case ClosureCall(callee, closureTypingTarget, args) if bypassPurityChecks || closureTypingTarget.isResolvedAndPure =>
        for {
          clp <- dev(callee, developLocals, bypassPurityChecks)
          argsp <- devAll(args, developLocals, bypassPurityChecks)
        } yield ClosureCall(clp, closureTypingTarget, argsp)
      case pureClosureValue: PureClosureValue => Some(pureClosureValue)
      case Plus(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield Plus(lp, rp)
      case Neg(operand) => for {
        op <- dev(operand, developLocals, bypassPurityChecks)
      } yield Neg(op)
      case Times(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield Times(lp, rp)
      case DivBy(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield DivBy(lp, rp)
      case Modulo(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield Modulo(lp, rp)
      case LogicalAnd(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield LogicalAnd(lp, rp)
      case LogicalNot(operand) => for {
        op <- dev(operand, developLocals, bypassPurityChecks)
      } yield LogicalNot(op)
      case LogicalOr(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield LogicalOr(lp, rp)
      case Equality(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield Equality(lp, rp)
      case LessOrEq(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield LessOrEq(lp, rp)
      case LessThan(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks)
        rp <- dev(rhs, developLocals, bypassPurityChecks)
      } yield LessThan(lp, rp)
      case TypePredicate(subject, tpe) => for {
        sp <- dev(subject, developLocals, bypassPurityChecks)
      } yield TypePredicate(sp, tpe)
      case _ => None
    }
    stepRes.flatMap {
      case res if res == formula => Some(res)
      case res => dev(res, developLocals, bypassPurityChecks)
    } orElse {
      Option.when(formula.isInstanceOf[ValIdValue | VarIdValue]) {
        formula
      }
    }
  }

  private def devAll(ls: List[Formula], developLocals: Boolean, bypassPurityChecks: Boolean): Option[List[Formula]] = {
    ls.foldRight(Option(List.empty[Formula])) {
      case (curr, Some(acc)) => dev(curr, developLocals, bypassPurityChecks).map(_ :: acc)
      case _ => None
    }
  }

  def extractRawBranchingInfos(cond: IdValue, ambientBranchingInfo: BranchingInfo, outerScope: Scope)
                              (using typer: Typer, dealiasingCtx: DealiasingContext): (BranchingInfo, BranchingInfo) = {
    val (infoIfTrueNearest, infoIfFalseNearest) =
      developNearest(cond).map(infosFor(_)(using outerScope))
        .getOrElse((BranchingInfo.empty, BranchingInfo.empty))
    val (infoIfTrueDeep, infoIfFalseDeep) =
      developDeep(cond).map(infosFor(_)(using outerScope))
        .getOrElse((BranchingInfo.empty, BranchingInfo.empty))
    (ambientBranchingInfo ++ infoIfTrueNearest ++ infoIfTrueDeep,
      ambientBranchingInfo ++ infoIfFalseNearest ++ infoIfFalseDeep)
  }

  def rawInfosFor(cond: Formula, outerScope: Scope)(using dealiasingCtx: DealiasingContext): (BranchingInfo, BranchingInfo) =
    infosFor(cond)(using outerScope)

  private def infosFor(cond: Formula)(using outerScope: Scope, dealiasingCtx: DealiasingContext): (BranchingInfo, BranchingInfo) = {
    cond match {
      case LogicalAnd(lhs, rhs) =>
        val (leftTrueInfos, leftFalseInfos) = infosFor(lhs)
        val (rightTrueInfos, rightFalseInfos) = infosFor(rhs)
        (leftTrueInfos ++ rightTrueInfos, BranchingInfo.empty)
      case LogicalOr(lhs, rhs) =>
        val (leftTrueInfos, leftFalseInfos) = infosFor(lhs)
        val (rightTrueInfos, rightFalseInfos) = infosFor(rhs)
        (BranchingInfo.empty, leftFalseInfos ++ rightFalseInfos)
      case LogicalNot(operand) =>
        val (operandTrueInfos, operandFalseInfos) = infosFor(operand)
        (operandFalseInfos, operandTrueInfos)
      // TODO maybe add a reference equality operator? or force overrides of equal to only work on two objects of exact same type
      case eq@Equality(lhs, rhs) =>
        (BranchingInfo.ofAssumption(eq), BranchingInfo.ofAssumption(LogicalNot(eq)))
      case leq@LessOrEq(lhs, rhs) =>
        (BranchingInfo.ofAssumption(leq), BranchingInfo.ofAssumption(LessThan(rhs, lhs)))
      case lt@LessThan(lhs, rhs) =>
        (BranchingInfo.ofAssumption(lt), BranchingInfo.ofAssumption(LessOrEq(rhs, lhs)))
      case TypePredicate(subject, tpe) =>
        (BranchingInfo.ofPositiveSmartcast(subject, tpe), BranchingInfo.ofNegativeSmartcast(subject, tpe))
      case cond => (BranchingInfo.ofAssumption(cond), BranchingInfo.ofAssumption(LogicalNot(cond)))
    }
  }

  override def toString: String = "ProxyStore {\n" ++ proxies.mkString("\n").indent(2) ++ "}"

}
