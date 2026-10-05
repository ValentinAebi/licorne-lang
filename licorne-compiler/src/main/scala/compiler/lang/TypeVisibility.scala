package compiler.lang

enum TypeVisibility {
  case Public extends TypeVisibility
  case PkgPrivate(pkgPrefix: List[String]) extends TypeVisibility
  case FilePrivate extends TypeVisibility

  def isAtLeastAsPermissiveAs(that: TypeVisibility): Boolean = (this, that) match {
    case (Public, _) => true
    case (PkgPrivate(thisPkg), PkgPrivate(thatPkg)) => thatPkg.startsWith(thisPkg)
    case (_, FilePrivate) => true
    case _ => false
  }

  override def toString: String = this match {
    case Public => "public"
    case PkgPrivate(pkgPrefix) => s"private(${pkgPrefix.mkString(".")})"
    case FilePrivate => "private"
  }

}
