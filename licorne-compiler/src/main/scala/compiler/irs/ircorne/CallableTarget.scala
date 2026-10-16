package compiler.irs.ircorne

trait CallableTarget {
  
  def isResolved: Boolean
  
  def isProvablyPure: Boolean

  def isUnresolvable: Boolean

  def isNotResolvedYet: Boolean = !isResolved && !isUnresolvable

  def markUnresolvable(): Unit
}
