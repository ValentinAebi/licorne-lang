package identifiers

sealed trait Identifier {

  def stringId: String

  override def toString: String = stringId
}

sealed trait FunOrVarId extends Identifier

sealed trait TypeIdentifier extends Identifier

final case class NormalFunOrVarId(stringId: String) extends FunOrVarId
final case class NormalTypeId(stringId: String) extends TypeIdentifier

final case class LowererGeneratedVarId(private val rawName: String) extends FunOrVarId {
  override def stringId: String = "des$" ++ rawName
}

final case class BackendGeneratedVarId(private val rawName: String) extends FunOrVarId {
  override def stringId: String = "bck$" ++ rawName
}

case object ConstructorFunId extends FunOrVarId {
  override def stringId: String = "<init>"
}

object BackendGeneratedVarId {
  def apply(varIdx: Int): BackendGeneratedVarId = new BackendGeneratedVarId(varIdx.toString)
}

case object MeVarId extends FunOrVarId {
  override def stringId: String = "me"
}
