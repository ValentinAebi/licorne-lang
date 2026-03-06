package compiler.egraphs.rewrites

import compiler.egraphs.{EClass, EClassId, EGraph, ENode}

import scala.collection.mutable

abstract class EqualitySaturationRewriteRule {

  def nodeTargets: Iterable[Class[?]]

  def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: java.util.LinkedHashSet[EClass]): EGraph

}
