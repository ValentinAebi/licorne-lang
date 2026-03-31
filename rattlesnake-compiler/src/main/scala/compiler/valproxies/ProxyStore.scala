package compiler.valproxies

import compiler.lang.Formulas
import compiler.lang.Formulas.*

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

  def extractRawBranchingInfos(cond: IdValue, ambientBranchingInfo: BranchingInfo): (BranchingInfo, BranchingInfo) = getProxy(cond) match {
    case Some(proxy) => infosFor(proxy, ambientBranchingInfo)
    case None => (BranchingInfo.empty, BranchingInfo.empty)
  }

  private def infosFor(cond: Formula, ambientBranchingInfo: BranchingInfo): (BranchingInfo, BranchingInfo) = {
    val (newIfTrue, newIfFalse) = cond match {
      case LogicalAnd(lhs, rhs) =>
        val (leftTrueInfos, leftFalseInfos) = infosFor(lhs, ambientBranchingInfo)
        val (rightTrueInfos, rightFalseInfos) = infosFor(rhs, ambientBranchingInfo)
        (leftTrueInfos ++ rightTrueInfos, BranchingInfo.empty)
      case LogicalOr(lhs, rhs) =>
        val (leftTrueInfos, leftFalseInfos) = infosFor(lhs, ambientBranchingInfo)
        val (rightTrueInfos, rightFalseInfos) = infosFor(rhs, ambientBranchingInfo)
        (BranchingInfo.empty, leftFalseInfos ++ rightFalseInfos)
      case LogicalNot(operand) =>
        val (operandTrueInfos, operandFalseInfos) = infosFor(operand, ambientBranchingInfo)
        (operandFalseInfos, operandTrueInfos)
      case leq@LessOrEq(lhs, rhs) =>
        (BranchingInfo.ofAssumption(leq), BranchingInfo.ofAssumption(LessThan(rhs, lhs)))
      case lt@LessThan(lhs, rhs) =>
        (BranchingInfo.ofAssumption(lt), BranchingInfo.ofAssumption(LessOrEq(rhs, lt)))
      case TypePredicate(subject, tpe) =>
        (BranchingInfo.ofPositiveSmartcast(subject, tpe), BranchingInfo.ofNegativeSmartcast(subject, tpe))
      case _ => (BranchingInfo.empty, BranchingInfo.empty)
    }
    (ambientBranchingInfo ++ newIfTrue, ambientBranchingInfo ++ newIfFalse)
  }

  override def toString: String = "ProxyStore {\n" ++ proxies.mkString("\n").indent(2) ++ "}"

}
