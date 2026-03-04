package compiler.egraphs.rewrites

import compiler.egraphs.{BinaryOperatorENode, EClassId, EGraph, ENode}

import scala.reflect.ClassTag

final class Commutativity[B <: BinaryOperatorENode : ClassTag](mkBinop: (EClassId, EClassId) => B) extends EqualitySaturationRewriteRule {

  override def rewrite(eGraph: EGraph, rootNode: ENode): (EGraph, List[ENode]) = rootNode match {
    case rootNode: B =>
      val revBinop = mkBinop(rootNode.rhs, rootNode.lhs)
      val graphAfter = eGraph.withEquality(rootNode, revBinop)
      (graphAfter, List(revBinop))
    case _ => (eGraph, List.empty)
  }
  
}
