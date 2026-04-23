package compiler.valproxies

import compiler.irs.SSA.Scope
import compiler.lang.Formulas
import compiler.lang.Formulas.*
import compiler.typing.Typer
import compiler.typing.contexts.DealiasingContext

import scala.collection.mutable


final class ProxyStore {
  private val proxies = mutable.Map.empty[IdValue, Formula]

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

  def getProxy(idVal: IdValue): Option[Formula] = proxies.get(idVal)

  def getProxyIfIdValue(formula: Formula): Option[Formula] = formula match {
    case value: IdValue => getProxy(value)
    case _ => None
  }

  def develop(formula: Formula): Formula = {
    val oneStepRes = formula match {
      case value: IdValue => getProxy(value).getOrElse(value)
      case formula: ConstFormula => formula
      case Select(owner, field) => Select(develop(owner), field)
      case Call(receiver, func, typeArgs, args) =>
        Call(develop(receiver), func, typeArgs, args.map(develop))
      case Plus(lhs, rhs) => Plus(develop(lhs), develop(rhs))
      case Neg(operand) => Neg(develop(operand))
      case Times(lhs, rhs) => Times(develop(lhs), develop(rhs))
      case DivBy(lhs, rhs) => DivBy(develop(lhs), develop(rhs))
      case Modulo(lhs, rhs) => Modulo(develop(lhs), develop(rhs))
      case LogicalAnd(lhs, rhs) => LogicalAnd(develop(lhs), develop(rhs))
      case LogicalNot(operand) => LogicalNot(develop(operand))
      case LogicalOr(lhs, rhs) => LogicalOr(develop(lhs), develop(rhs))
      case Equality(lhs, rhs) => Equality(develop(lhs), develop(rhs))
      case LessOrEq(lhs, rhs) => LessOrEq(develop(lhs), develop(rhs))
      case LessThan(lhs, rhs) => LessThan(develop(lhs), develop(rhs))
      case TypePredicate(subject, tpe) => TypePredicate(develop(subject), tpe)
    }
    if oneStepRes == formula then oneStepRes
    else develop(oneStepRes)
  }

  def extractRawBranchingInfos(cond: IdValue, ambientBranchingInfo: BranchingInfo, outerScope: Scope)(using typer: Typer, dealiasingCtx: DealiasingContext): (BranchingInfo, BranchingInfo) = {
    val (directInfoIfTrue, directInfoIfFalse) = infosFor(cond)(using outerScope)
    val (proxyInfoIfTrue, proxyInfoIfFalse) = getProxy(cond) match {
      case Some(proxy) if proxy.isPure =>
        val (infoIfTrue, infoIfFalse) = infosFor(proxy)(using outerScope)
        (infoIfTrue.filteredPure(typer), infoIfFalse.filteredPure(typer))
      case _ => (BranchingInfo.empty, BranchingInfo.empty)
    }
    (ambientBranchingInfo ++ directInfoIfTrue ++ proxyInfoIfTrue,
      ambientBranchingInfo ++ directInfoIfFalse ++ proxyInfoIfFalse)
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
      case _ => (BranchingInfo.empty, BranchingInfo.empty)
    }
  }
  
  def isNullOrItsProxy(value: IdValue, scope: Scope): Boolean = {
    val nullVal = scope.valuesCtx.globalCtx.nullVal
    value == nullVal || getProxy(value).contains(nullVal)
  }

  override def toString: String = "ProxyStore {\n" ++ proxies.mkString("\n").indent(2) ++ "}"

}
