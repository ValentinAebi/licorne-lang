package compiler.egraphs.rewrites.rules

import compiler.egraphs.{EClass, EGraph, ENegNode, ENode, MutEGraphWrapper}
import compiler.egraphs.rewrites.EqualitySaturationRewriteRule

import java.util

/**
 * `-(-a)  ==>  a`
 */
object NegNegCancellation extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classOf[ENegNode])

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: util.LinkedHashSet[EClass]): EGraph = rootNode match {
    case rootNode: ENegNode =>
      val graphB = MutEGraphWrapper(eGraph)
      graphB.getCurrentState.classes(rootNode.operand).nodes.foreach {
        case n: ENegNode =>
          val rootNodeId = graphB.addNode(rootNode)
          graphB.assertEquality(rootNodeId, n.operand)
        case _ => ()
      }
      graphB.getCurrentState
    case _ => eGraph
  }
}
