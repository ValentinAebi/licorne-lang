package compiler.parser

/**
 * Composite containing the results of individual parsers, while keeping info on their types
 * @tparam L left
 * @tparam R right
 */
type ParseTree[L, R] = ParseTree.^:[L, R]

object ParseTree {
  
  extension[L](left: L) {
    /**
     * Composite containing the results of individual parsers, while keeping info on their types
     * @tparam L left
     * @tparam R right
     */
    def ^:[R](right: R): L ^: R = new ^:(left, right)
  }

  /**
   * Composite containing the results of individual parsers, while keeping info on their types
   * @tparam L left
   * @tparam R right
   */
  final infix case class ^:[+L, +R](left: L, right: R){
    
    def toTuple: (L, R) = (left, right)
    
    override def toString: String = s"$left ^: $right"
  }
  
}
