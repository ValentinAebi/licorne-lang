package identifiers

sealed trait Identifier {

  def stringId: String

  override def toString: String = stringId
}

sealed trait FunOrVarId extends Identifier

sealed trait TypeIdentifier extends Identifier

final case class NormalFunOrVarId(stringId: String) extends FunOrVarId
final case class NormalTypeId(stringId: String) extends TypeIdentifier

case object ConstructorFunId extends FunOrVarId {
  override def stringId: String = "<init>"
}

case object MeVarId extends FunOrVarId {
  override def stringId: String = "me"
}
