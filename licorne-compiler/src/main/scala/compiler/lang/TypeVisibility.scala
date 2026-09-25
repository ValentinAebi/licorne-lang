package compiler.lang

enum TypeVisibility {
  case Public extends TypeVisibility
  case Private(pkgPrefix: List[String]) extends TypeVisibility

  def canBeImportedFrom(importerPkg: List[String]): Boolean = this match {
    case TypeVisibility.Public => true
    case TypeVisibility.Private(pkgPrefix) => importerPkg.startsWith(pkgPrefix)
  }

  def isAtLeastAsPermissiveAs(that: TypeVisibility): Boolean = (this, that) match {
    case (Public, _) => true
    case (Private(thisPkg), Private(thatPkg)) => thatPkg.startsWith(thisPkg)
    case _ => false
  }

  override def toString: String = this match {
    case TypeVisibility.Public => "public"
    case TypeVisibility.Private(pkgPrefix) => s"private(${pkgPrefix.mkString(".")})"
  }

}
