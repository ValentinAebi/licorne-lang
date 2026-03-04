package compiler.egraphs.rewrites

import compiler.egraphs.{BinaryOperatorENode, EClassId, EGraph, ENode, MutEGraphWrapper}

import scala.reflect.ClassTag

/**
 * `op(x,op(y,z))  ==>  op(op(x,y),z)`
 */
final class AssociativityDirection2[B <: BinaryOperatorENode : ClassTag](mkBinop: (EClassId, EClassId) => B) extends EqualitySaturationRewriteRule {
  
  override def rewrite(eGraph: EGraph, rootNode: ENode): (EGraph, List[ENode]) = rootNode match {
      case rootNode: B =>
        val graphB = MutEGraphWrapper(eGraph)
        val newNodesB = List.newBuilder[ENode]
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
          newNodesB.addOne(x_op_y)
          newNodesB.addOne(newLhs_op_z)
        }
        (graphB.getCurrentState, newNodesB.result())
      case _ => (eGraph, List.empty)
    }
  
}
