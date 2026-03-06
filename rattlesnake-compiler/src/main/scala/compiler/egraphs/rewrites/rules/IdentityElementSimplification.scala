package compiler.egraphs.rewrites.rules

import compiler.egraphs.rewrites.EqualitySaturationRewriteRule
import compiler.egraphs.{BinaryOperatorENode, EClass, EClassId, EGraph, ENode}

import scala.collection.mutable
import scala.reflect.{ClassTag, classTag}

/**
 * `id op x  ==>  x`
 *
 * `x op id  ==>  x`
 */
final class IdentityElementSimplification[I: ClassTag, B <: BinaryOperatorENode : ClassTag](identityElem: I, mkBinop: (EClassId, EClassId) => B, simplifyLeft: Boolean, simplifyRight: Boolean) extends EqualitySaturationRewriteRule {

  override def nodeTargets: Iterable[Class[?]] = List(classTag[B].runtimeClass)

  override def rewrite(eGraph: EGraph, rootNode: ENode, newTargetNodesCollector: java.util.LinkedHashSet[EClass]): EGraph = rootNode match {
    case rootNode: B =>

      def tryToSimplify(inputG: EGraph, simplificationTarget: EClassId, otherOperand: EClassId): EGraph = {
        inputG.classes(simplificationTarget).asConstOfType[I] match {
          case Some(cst) if cst == identityElem =>
            val rootNodeClass = inputG.ownerClassOf(rootNode)
            inputG.withEquality(rootNodeClass.canonicalId, otherOperand)
          case _ => inputG
        }
      }
      
      val ig = if simplifyLeft then tryToSimplify(eGraph, rootNode.lhs, rootNode.rhs) else eGraph
      if simplifyRight then tryToSimplify(ig, rootNode.rhs, rootNode.lhs) else ig

    case _ => eGraph
  }
}
