package compiler.recurrences

import compiler.lang.Formulas.{Formula, IdValue}


final case class Recurrence(init: Formula, induct: Formula, inductVal: IdValue) {

  override def toString: String = s"[init = $init, induct($inductVal) = $induct]"

}
