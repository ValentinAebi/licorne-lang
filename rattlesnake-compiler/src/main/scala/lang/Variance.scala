package lang

enum Variance(private val value: Int, val descr: String) {
  case Invariant extends Variance(0, "invariant")
  case Covariant extends Variance(1, "covariant")
  case Contravariant extends Variance(-1, "contravariant")

  def isAssignableTo(superV: Variance): Boolean = superV match {
    case Invariant => this == Invariant
    case Covariant => this != Contravariant
    case Contravariant => this != Covariant
  }

  def *(that: Variance): Variance = this.value * that.value match {
    case 0 => Invariant
    case 1 => Covariant
    case -1 => Contravariant
    case _ => assert(false)
  }

  override def toString: String = descr

}
