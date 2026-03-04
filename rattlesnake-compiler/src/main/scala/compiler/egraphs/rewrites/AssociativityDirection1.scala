package compiler.egraphs.rewrites

import compiler.egraphs.{BinaryOperatorENode, EClassId, EGraph, ENode, EPlusNode, MutEGraphWrapper}
import compiler.util.SeqSet

import scala.reflect.ClassTag

/**
 * `op(op(x,y),z)  ==>  op(x,op(y,z))`
 */
final class AssociativityDirection1[B <: BinaryOperatorENode : ClassTag](mkBinop: (EClassId, EClassId) => B) extends EqualitySaturationRewriteRule {

  override def rewrite(eGraph: EGraph, rootNode: ENode): (EGraph, List[ENode]) = rootNode match {
    case rootNode: B =>
      val graphB = MutEGraphWrapper(eGraph)
      val newNodesB = List.newBuilder[ENode]
      for (lhsNode <- eGraph.classes(rootNode.lhs).findNodesOfType[B]){
        val x = lhsNode.lhs
        val y = lhsNode.rhs
        val z = rootNode.rhs
        val y_op_z = mkBinop(y, z)
        val newRhs = graphB.addNode(y_op_z)
        val x_op_newRhs = mkBinop(x, newRhs)
        val newTerm = graphB.addNode(x_op_newRhs)
        val oldTerm = graphB.addNode(rootNode)
        graphB.assertEquality(oldTerm, newTerm)
        newNodesB.addOne(y_op_z)
        newNodesB.addOne(x_op_newRhs)
      }
      (graphB.getCurrentState, newNodesB.result())
    case _ => (eGraph, List.empty)
  }

}
