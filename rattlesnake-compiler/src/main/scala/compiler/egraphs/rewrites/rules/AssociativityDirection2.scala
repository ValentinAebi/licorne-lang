package compiler.egraphs.rewrites.rules

import compiler.egraphs.rewrites.EqualitySaturationRewriteRule
import compiler.egraphs.*

import scala.collection.mutable
import scala.reflect.{ClassTag, classTag}

/**
 * `op(x,op(y,z))  ==>  op(op(x,y),z)`
 */
final class AssociativityDirection2[B <: BinaryOperatorENode : ClassTag](mkBinop: (EClassId, EClassId) => B) extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classTag[B].runtimeClass)
  
  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: java.util.LinkedHashSet[EClass]): EGraph = rootNode match {
    case rootNode: B =>
      val graphB = MutEGraphWrapper(eGraph)
      for (rhsNode <- eGraph.classes(rootNode.rhs).findNodesOfType[B]) {
        val x = rootNode.lhs
        val y = rhsNode.lhs
        val z = rhsNode.rhs
        val x_op_y = mkBinop(x, y)
        val newLhs = graphB.addNode(x_op_y)
        val newLhs_op_z = mkBinop(newLhs, z)
        val newTerm = graphB.addNode(newLhs_op_z)
        val oldTerm = graphB.addNode(rootNode)
        graphB.assertEquality(oldTerm, newTerm)
        newTargetNodesCollector.addLast(graphB.ownerClassOf(x_op_y))
        newTargetNodesCollector.addLast(graphB.ownerClassOf(newLhs_op_z))
      }
      graphB.getCurrentState
    case _ => eGraph
  }

}
