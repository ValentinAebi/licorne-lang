package compiler.lang

enum Overridability extends Enum[Overridability] {
  case Abstract, Final, Open

  override def toString: String = name().toLowerCase
}
