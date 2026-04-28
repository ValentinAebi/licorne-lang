package compiler.identifiers

import compiler.lang.Keyword

sealed trait Identifier {

  def stringId: String

  override def toString: String = stringId
}

final case class TypeIdentifier(prefixes: List[String], nonPrefixedId: String) extends Identifier {
  override def stringId: String = (prefixes :+ nonPrefixedId).mkString(".")
}

sealed trait FunOrVarId extends Identifier

final case class NormalFunOrVarId(stringId: String) extends FunOrVarId

case object ConstructorFunId extends FunOrVarId {
  override def stringId: String = "<init>"
}

case object ThisId extends FunOrVarId {
  override def stringId: String = Keyword.This.str
}

case object ItId extends FunOrVarId {
  override def stringId: String = Keyword.It.str
}
