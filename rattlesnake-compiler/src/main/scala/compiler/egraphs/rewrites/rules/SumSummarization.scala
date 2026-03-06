package compiler.egraphs.rewrites.rules

import compiler.egraphs.*
import compiler.egraphs.rewrites.EqualitySaturationRewriteRule

/**
 * `a*x + b*x  ==>  (a + b) * x`
 *
 * `x + b*x  ==>  (b + 1) * x`
 *
 * `a*x + x  ==>  (a + 1) * x`
 *
 * `x + x  ==>  2 * x`
 */
object SumSummarization extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classOf[EPlusNode])

  private val oneNode = EConstNode(1)
  private val twoNode = EConstNode(2)

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: java.util.LinkedHashSet[EClass]): EGraph = {
    rootNode match {
      case rootNode: EPlusNode =>

        val graphB = MutEGraphWrapper(eGraph)
        val oneNodeId = graphB.addNode(oneNode)

        def mkSummarizedNode(mClassId: EClassId, nClassId: EClassId, xClassId: EClassId): Unit = {
          val newPlusNode = EPlusNode(mClassId, nClassId)
          val newPlusNodeId = graphB.addNode(newPlusNode)
          val newTimesNode = ETimesNode(newPlusNodeId, xClassId)
          graphB.assertEquality(rootNode, newTimesNode)
          newTargetNodesCollector.addLast(graphB.ownerClassOf(newPlusNode))
          newTargetNodesCollector.addLast(graphB.ownerClassOf(newTimesNode))
        }

        val lhsTimesNodes = graphB.getCurrentState.classes(rootNode.lhs).findNodesOfType[ETimesNode]
        val rhsTimesNodes = graphB.getCurrentState.classes(rootNode.rhs).findNodesOfType[ETimesNode]

        for {
          ETimesNode(mClassId, xClassId1) <- lhsTimesNodes
          ETimesNode(nClassId, xClassId2) <- rhsTimesNodes
          if graphB.equalityQuery(xClassId1, xClassId2)
        } do {
          mkSummarizedNode(mClassId, nClassId, xClassId1)
        }

        for {
          ETimesNode(mClassId, xClassId) <- lhsTimesNodes
          if xClassId == rootNode.rhs
        } do {
          val oneNodeId = graphB.addNode(oneNode)
          mkSummarizedNode(mClassId, oneNodeId, xClassId)
        }

        for {
          ETimesNode(nClassId, xClassId) <- rhsTimesNodes
          if xClassId == rootNode.lhs
        } do {
          val oneNodeId = graphB.addNode(oneNode)
          mkSummarizedNode(oneNodeId, nClassId, xClassId)
        }

        if (rootNode.lhs == rootNode.rhs) {
          val twoNodeId = graphB.addNode(twoNode)
          val twoTimesXNode = ETimesNode(twoNodeId, rootNode.lhs)
          graphB.addNode(twoTimesXNode)
          newTargetNodesCollector.addLast(graphB.ownerClassOf(twoTimesXNode))
          graphB.assertEquality(rootNode, twoTimesXNode)
        }

        graphB.getCurrentState

      case _ => eGraph
    }
  }

}
