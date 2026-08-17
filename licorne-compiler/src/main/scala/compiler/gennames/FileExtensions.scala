package compiler.gennames

object FileExtensions {
  val licorne: String = "lic"
  val clazz: String = "class"
  
  def dot(mkExt: FileExtensions.type => String): String =
    s".${mkExt(this)}"
  
}
