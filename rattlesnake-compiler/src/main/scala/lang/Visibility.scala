package lang

enum Visibility extends Enum[Visibility] {
  case Private, Public
  
  def isPublic: Boolean = this == Public
  
  def isPrivate: Boolean = this == Private

  override def toString: String = name().toLowerCase
  
}
