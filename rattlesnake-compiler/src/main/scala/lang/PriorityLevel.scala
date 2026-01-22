package lang

import lang.Formulas.*
import lang.PriorityLevel.*

enum PriorityLevel {
  case Atomic, TypeTest, Mul, Linear, Comparison, Conj, Disj

  def bindsStrongerThan(that: PriorityLevel): Boolean =
    this.ordinal < that.ordinal

  def bindsWeakerThan(that: PriorityLevel): Boolean =
    that.bindsStrongerThan(this)

  def bindsAtLeastAsMuchAs(that: PriorityLevel): Boolean =
    this.ordinal <= that.ordinal

  def bindsNoMoreThan(that: PriorityLevel): Boolean =
    that.bindsAtLeastAsMuchAs(this)

}

extension (binOp: BinOp) def priorityLevel: PriorityLevel = binOp match {
  case _: (Plus | Minus) => Linear
  case _: (Times | Div | Rem) => Mul
  case _: And => Conj
  case _: Or => Disj
  case _: (LessThan | LessOrEq | Equal) => Comparison
}

extension (l: BinOp) {

  def bindsStrongerThan(r: BinOp): Boolean =
    l.priorityLevel.bindsStrongerThan(r.priorityLevel)

  def bindsWeakerThan(r: BinOp): Boolean =
    l.priorityLevel.bindsWeakerThan(r.priorityLevel)

  def bindsAtLeastAsMuchAs(r: BinOp): Boolean =
    l.priorityLevel.bindsAtLeastAsMuchAs(r.priorityLevel)

  def bindsNoMoreThan(r: BinOp): Boolean =
    l.priorityLevel.bindsNoMoreThan(r.priorityLevel)

}
