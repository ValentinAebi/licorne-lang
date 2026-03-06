package compiler.egraphs.rewrites

import compiler.egraphs.rewrites.rules.*
import compiler.egraphs.{EDivNode, EPlusNode, ETimesNode}

object EqualitySaturationRewriteRules {

  val allRules: List[EqualitySaturationRewriteRule] = List(
    AssociativityDirection1(EPlusNode(_, _)),
    AssociativityDirection1(ETimesNode(_, _)),
    AssociativityDirection2(EPlusNode(_, _)),
    AssociativityDirection2(ETimesNode(_, _)),
    Commutativity(EPlusNode(_, _)),
    Commutativity(ETimesNode(_, _)),
    ConstPropagation,
    IdentityElementSimplification(0, EPlusNode(_, _), simplifyLeft = true, simplifyRight = true),
    IdentityElementSimplification(1, ETimesNode(_, _), simplifyLeft = true, simplifyRight = true),
    IdentityElementSimplification(1, EDivNode(_, _), simplifyLeft = false, simplifyRight = true),
    InverseElemSimplification,
    SumSummarization,
    NegNegCancellation,
    NegationPush
  )

}
