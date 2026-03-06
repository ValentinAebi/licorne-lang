package compiler.egraphs.rewrites.rules

import compiler.egraphs.*
import compiler.egraphs.rewrites.EqualitySaturationRewriteRule
import compiler.lang.Operator

object ConstPropagation extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] =
    ENodes.alreadyInstantiatedNodeClassesBut(classOf[EConstNode], classOf[EIdValNode])

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: java.util.LinkedHashSet[EClass]): EGraph = {

    def cstFound(cst: Any): EGraph = {
      val cstNode = EConstNode(cst)
      eGraph.withEquality(rootNode, cstNode)
    }

    rootNode match {
      case rootNode: BinaryOperatorENode =>
        val lhsClass = eGraph.classes(rootNode.lhs)
        val rhsClass = eGraph.classes(rootNode.rhs)
        // TODO propagate Double values as well
        simplifyIntBinop(lhsClass.asConstOfType[Int], rootNode.op, rhsClass.asConstOfType[Int]) match {
          case Some(resCst) => cstFound(resCst)
          case None => eGraph
        }
      case rootNode: ENegNode =>
        val operandClass = eGraph.classes(rootNode.operand)
        simplifyIntUnop(rootNode.op, operandClass.asConstOfType[Int]) match {
          case Some(resCst) => cstFound(resCst)
          case None => eGraph
        }
      case _ => eGraph
    }
  }

  private def simplifyIntBinop(lhsCstOpt: Option[Int], op: Operator, rhsCstOpt: Option[Int]): Option[Int] =
    (lhsCstOpt, op, rhsCstOpt) match {
      case (Some(l), Operator.Plus, Some(r)) => Some(l + r)
      case (Some(l), Operator.Times, Some(r)) => Some(l * r)
      case (Some(l), Operator.Div, Some(r)) if r != 0 => Some(l / r)
      case (Some(l), Operator.Modulo, Some(r)) if r != 0 => Some(l % r)
      case _ => None
    }

  private def simplifyIntUnop(op: Operator, operandOpt: Option[Int]): Option[Int] =
    (op, operandOpt) match {
      case (Operator.Minus, Some(operandVal)) => Some(-operandVal)
      case _ => None
    }

}
