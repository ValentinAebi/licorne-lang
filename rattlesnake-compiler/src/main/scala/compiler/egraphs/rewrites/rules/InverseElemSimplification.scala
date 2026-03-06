package compiler.egraphs.rewrites.rules

import compiler.egraphs.*
import compiler.egraphs.rewrites.EqualitySaturationRewriteRule

import scala.collection.mutable
import scala.reflect.ClassTag

object InverseElemSimplification extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classOf[EPlusNode], classOf[EDivNode])

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: java.util.LinkedHashSet[EClass]): EGraph = rootNode match {
    case EPlusNode(lhs, rhs)
      if eGraph.classes(rhs).findNodesOfType[ENegNode].exists(n => eGraph.equalityQuery(lhs, n.operand)) =>
      eGraph.withEquality(rootNode, EConstNode(0))
    case EDivNode(lhs, rhs) if eGraph.equalityQuery(lhs, rhs) =>
      eGraph.withEquality(rootNode, EConstNode(1))
    case _ => eGraph
  }

}
