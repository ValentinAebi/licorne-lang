package compiler.lang

enum Purity(override val toString: String) {
  case Pure extends Purity("pure")
  case PossiblyImpure extends Purity("possibly-impure")
  
  def conformsTo(that: Purity): Boolean = (this, that) match {
    case (Pure, _) => true
    case (_, PossiblyImpure) => true
    case _ => false
  }
}
