package compiler.egraphs.rewrites.rules

import compiler.egraphs.rewrites.EqualitySaturationRewriteRule
import compiler.egraphs.*

import java.util

/**
 * -(a + b)  ==>  (-a) + (-b)
 *
 * `-(a*b)  ==> (-a)*b`
 *
 * `-(a/b)  ==>  (-a)/b`
 */
object NegationPush extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classOf[ENegNode])

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: util.LinkedHashSet[EClass]): EGraph = rootNode match {
    case rootNode: ENegNode =>
      val graphB = MutEGraphWrapper(eGraph)

      def mkPlusSimplification(plus: EPlusNode): Unit = {
        val nLhsNegNode = ENegNode(plus.lhs)
        val nLhsNegClId = graphB.addNode(nLhsNegNode)
        val nRhsNegNode = ENegNode(plus.rhs)
        val nRhsNegClId = graphB.addNode(nRhsNegNode)
        val sumOfNegNode = EPlusNode(nLhsNegClId, nRhsNegClId)
        val sumOfNegId = graphB.addNode(sumOfNegNode)
        graphB.assertEquality(rootNode, sumOfNegNode)
        newTargetNodesCollector.addLast(graphB.ownerClassOf(nLhsNegNode))
        newTargetNodesCollector.addLast(graphB.ownerClassOf(nRhsNegNode))
        newTargetNodesCollector.addLast(graphB.ownerClassOf(sumOfNegNode))
      }

      def mkLeftOnlySimplification[B <: BinaryOperatorENode](n: B, mkNode: (EClassId, EClassId) => B): Unit = {
        val nLhsNegNode = ENegNode(n.lhs)
        val nLhsNegClId = graphB.addNode(nLhsNegNode)
        val lNegTimesNode = mkNode(nLhsNegClId, n.rhs)
        graphB.assertEquality(rootNode, lNegTimesNode)
        newTargetNodesCollector.addLast(graphB.ownerClassOf(nLhsNegNode))
        newTargetNodesCollector.addLast(graphB.ownerClassOf(lNegTimesNode))
      }

      graphB.getCurrentState.classes(rootNode.operand).nodes.foreach {
        case n: EPlusNode =>
          mkPlusSimplification(n)
        case n: ETimesNode =>
          mkLeftOnlySimplification(n, ETimesNode(_, _))
        case n: EDivNode =>
          mkLeftOnlySimplification(n, EDivNode(_, _))
        case _ => ()
      }
      graphB.getCurrentState
    case _ => eGraph
  }
}
