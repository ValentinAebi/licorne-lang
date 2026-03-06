package compiler.egraphs.rewrites.rules

import compiler.egraphs.*
import compiler.egraphs.rewrites.EqualitySaturationRewriteRule

import scala.collection.mutable
import scala.reflect.{ClassTag, classTag}

/**
 * `op(op(x,y),z)  ==>  op(x,op(y,z))`
 */
final class AssociativityDirection1[B <: BinaryOperatorENode : ClassTag](mkBinop: (EClassId, EClassId) => B) extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classTag[B].runtimeClass)

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: java.util.LinkedHashSet[EClass]): EGraph = rootNode match {
    case rootNode: B =>
      val graphB = MutEGraphWrapper(eGraph)
      for (lhsNode <- eGraph.classes(rootNode.lhs).findNodesOfType[B]) {
        val x = lhsNode.lhs
        val y = lhsNode.rhs
        val z = rootNode.rhs
        val y_op_z = mkBinop(y, z)
        val newRhs = graphB.addNode(y_op_z)
        val x_op_newRhs = mkBinop(x, newRhs)
        val newTerm = graphB.addNode(x_op_newRhs)
        val oldTerm = graphB.addNode(rootNode)
        graphB.assertEquality(oldTerm, newTerm)
        newTargetNodesCollector.addLast(graphB.ownerClassOf(y_op_z))
        newTargetNodesCollector.addLast(graphB.ownerClassOf(rootNode))
      }
      graphB.getCurrentState
    case _ => eGraph
  }

}
