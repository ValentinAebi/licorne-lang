package lang

import identifiers.{FunOrVarId, TypeIdentifier}

object Capturables {

  sealed trait Capturable

  sealed trait ConcreteCapturable extends Capturable

  sealed trait Path extends ConcreteCapturable {
    def root: RootPath
    def dot(fld: FunOrVarId): Path = SelectPath(this, fld)
  }
  
  sealed trait RootPath extends Path {
    override def root: RootPath = this
  }

  final case class IdPath(id: FunOrVarId) extends RootPath {
    override def toString: String = id.stringId
  }

  case object ThisPath extends RootPath {
    override def toString: String = Keyword.This.str
  }

  final case class SelectPath(directRoot: Path, fld: FunOrVarId) extends Path {
    override def root: RootPath = directRoot.root
    override def toString: String = s"$directRoot.$fld"
  }
  
  sealed trait GlobalCapturable extends Capturable

  final case class CapPackage(pkgName: TypeIdentifier) extends ConcreteCapturable, GlobalCapturable {
    override def toString: String = pkgName.stringId
  }

  case object RootCapability extends GlobalCapturable {
    override def toString: String = Keyword.Cap.str
  }
  
}
