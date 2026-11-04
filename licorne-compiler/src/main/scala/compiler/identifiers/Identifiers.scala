package compiler.identifiers

import compiler.lang.Keyword

sealed trait Identifier {

  def stringId: String

  override def toString: String = stringId
}

final case class TypeIdentifier(prefixes: List[String], nonPrefixedId: String, isCompanionObject: Boolean = false) extends Identifier {

  def asCompanionId: TypeIdentifier = copy(isCompanionObject = true)
  
  def asNonCompanionId: TypeIdentifier = copy(isCompanionObject = false)
  
  def stringIdWithPostfixSep(sep: String): String = (prefixes :+ nonPrefixedId).mkString(".") ++ maybeCompanionPostfix(sep)
  
  override def stringId: String = stringIdWithPostfixSep("::")

  def nonPrefixedIdWithPostfixSep(sep: String): String = nonPrefixedId ++ maybeCompanionPostfix(sep)

  private def maybeCompanionPostfix(sep: String): String = if isCompanionObject then sep + Keyword.Companion else ""
}

sealed trait FunOrVarId extends Identifier

final case class NormalFunOrVarId(stringId: String) extends FunOrVarId

case object ConstructorFunId extends FunOrVarId {
  override def stringId: String = Keyword.Constructor.str
}

case object ThisId extends FunOrVarId {
  override def stringId: String = Keyword.This.str
}

case object ItId extends FunOrVarId {
  override def stringId: String = Keyword.It.str
}
