package compiler.irs.ircorne

trait CallableTarget {
  
  def isResolved: Boolean
  
  def isResolvedAndPure: Boolean

  def isUnresolvable: Boolean

  def isNotResolvedYet: Boolean = !isResolved && !isUnresolvable

  def markUnresolvable(): Unit
}
