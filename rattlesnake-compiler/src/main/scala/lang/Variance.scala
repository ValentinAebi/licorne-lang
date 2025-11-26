package lang

enum Variance {
  case Invariant, Covariant, Contravariant

  def isAssignableTo(superV: Variance): Boolean = superV match {
    case Variance.Invariant => this == Invariant
    case Variance.Covariant => this != Contravariant
    case Variance.Contravariant => this != Covariant
  }

}
