package compiler.egraphs.rewrites.rules

import compiler.egraphs.rewrites.EqualitySaturationRewriteRule
import compiler.egraphs.*

import java.util

object NegationPush extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classOf[ENegNode])

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: util.LinkedHashSet[EClass]): EGraph = rootNode match {
    case rootNode: ENegNode =>
      val graphB = MutEGraphWrapper(eGraph)

      def mkSimplification[B <: BinaryOperatorENode](n: B, mkNode: (EClassId, EClassId) => B): Unit = {
        val nLhsNegNode = ENegNode(n.lhs)
        val nLhsNegClId = graphB.addNode(nLhsNegNode)
        val lNegTimesNode = mkNode(nLhsNegClId, n.rhs)
        graphB.assertEquality(rootNode, lNegTimesNode)
        newTargetNodesCollector.addLast(graphB.ownerClassOf(nLhsNegNode))
        newTargetNodesCollector.addLast(graphB.ownerClassOf(lNegTimesNode))
      }

      graphB.getCurrentState.classes(rootNode.operand).nodes.foreach {
        case n: ETimesNode =>
          mkSimplification(n, ETimesNode(_, _))
        case n: EDivNode =>
          mkSimplification(n, EDivNode(_, _))
        case _ => ()
      }
      graphB.getCurrentState
    case _ => eGraph
  }
}
