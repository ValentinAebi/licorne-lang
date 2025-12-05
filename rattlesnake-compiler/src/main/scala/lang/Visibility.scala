package lang

enum Visibility extends Enum[Visibility] {
  case Private, Public
  
  def isPublic: Boolean = this == Public
  
  def isPrivate: Boolean = this == Private
  
  def atLeastAsPermissiveAs(that: Visibility): Boolean = (this, that) match {
    case (Public, _) | (_, Private) => true
    case _ => this == that
  }

  override def toString: String = name().toLowerCase
  
}
