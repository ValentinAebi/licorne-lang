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

  def extractRawBranchingInfos(cond: IdValue): Option[(BranchingInfo, BranchingInfo)] = getProxy(cond).map(infosFor)

  private def infosFor(cond: Formula): (BranchingInfo, BranchingInfo) = cond match {
    case LogicalAnd(lhs, rhs) =>
      val (leftTrueInfos, leftFalseInfos) = infosFor(lhs)
      val (rightTrueInfos, rightFalseInfos) = infosFor(rhs)
      (leftTrueInfos ++ rightTrueInfos, BranchingInfo.empty)
    case LogicalOr(lhs, rhs) =>
      val (leftTrueInfos, leftFalseInfos) = infosFor(lhs)
      val (rightTrueInfos, rightFalseInfos) = infosFor(rhs)
      (BranchingInfo.empty, leftFalseInfos ++ rightFalseInfos)
    case leq@LessOrEq(lhs, rhs) =>
      (BranchingInfo.ofAssumption(leq), BranchingInfo.ofAssumption(LessThan(rhs, lhs)))
    case lt@LessThan(lhs, rhs) =>
      (BranchingInfo.ofAssumption(lt), BranchingInfo.ofAssumption(LessOrEq(rhs, lt)))
    case TypePredicate(subject, tpe) =>
      (BranchingInfo.ofSmartcast(subject, tpe), BranchingInfo.empty)
    case _ => (BranchingInfo.empty, BranchingInfo.empty)
  }

  override def toString: String = "ProxyStore {\n" ++ proxies.mkString("\n").indent(2) ++ "}"

}
