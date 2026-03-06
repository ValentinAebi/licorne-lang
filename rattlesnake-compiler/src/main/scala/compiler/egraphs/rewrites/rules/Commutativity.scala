package compiler.egraphs.rewrites.rules

import compiler.egraphs.rewrites.EqualitySaturationRewriteRule
import compiler.egraphs.*

import scala.collection.mutable
import scala.reflect.{ClassTag, classTag}

final class Commutativity[B <: BinaryOperatorENode : ClassTag](mkBinop: (EClassId, EClassId) => B) extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classTag[B].runtimeClass)

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: java.util.LinkedHashSet[EClass]): EGraph = rootNode match {
    case rootNode: B =>
      val graphB = MutEGraphWrapper(eGraph)
      val revBinop = mkBinop(rootNode.rhs, rootNode.lhs)
      graphB.addNode(revBinop)
      newTargetNodesCollector.addLast(graphB.ownerClassOf(revBinop))
      graphB.assertEquality(rootNode, revBinop)
      graphB.getCurrentState
    case _ => eGraph
  }

}
