package compiler.typechecking

import lang.Types.Type
import lang.Values.IdValue

sealed trait Constraint

final case class ValValSubtype(subT: IdValue, superT: IdValue) extends Constraint
final case class ValTypeSubtype(subT: IdValue, superT: Type) extends Constraint
