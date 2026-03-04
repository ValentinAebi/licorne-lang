package compiler.egraphs.rewrites

import compiler.egraphs.{EGraph, ENode}
import compiler.util.SeqSet

trait EqualitySaturationRewriteRule {

  /**
   * @return the updated graph and a list containing the new nodes
   */
  def rewrite(eGraph: EGraph, rootNode: ENode): (EGraph, List[ENode])

}
