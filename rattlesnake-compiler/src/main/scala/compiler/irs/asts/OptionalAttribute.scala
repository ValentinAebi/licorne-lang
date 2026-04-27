package compiler.irs.asts

private[asts] class OptionalAttribute[A] {
  private var valueOpt: Option[A] = None

  def setOpt(valueOpt: Option[A]): Unit = {
    this.valueOpt = valueOpt
  }

  def set(value: A): Unit = {
    setOpt(Some(value))
  }

  def getOpt: Option[A] = valueOpt

  override def toString: String = valueOpt.getOrElse("<empty>").toString
}
