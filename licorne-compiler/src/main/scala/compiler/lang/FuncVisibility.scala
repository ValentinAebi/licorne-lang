package compiler.lang

enum FuncVisibility extends Enum[FuncVisibility] {
  case Private, Public
  
  def isPublic: Boolean = this == Public
  
  def isPrivate: Boolean = this == Private
  
  def atLeastAsPermissiveAs(that: FuncVisibility): Boolean = (this, that) match {
    case (Public, _) | (_, Private) => true
    case _ => this == that
  }

  override def toString: String = name().toLowerCase
  
}
