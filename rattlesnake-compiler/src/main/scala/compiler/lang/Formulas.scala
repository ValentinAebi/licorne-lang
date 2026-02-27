package compiler.lang

import compiler.identifiers.{FunOrVarId, Identifier}
import compiler.irs.SSA.Scope
import compiler.util.SeqSet

object Formulas {
  
  sealed trait Formula

  sealed trait IdValue extends Formula {
    def uid: Long

    def definingScope: Scope
  }

  sealed trait NamedIdValue extends IdValue {
    def name: String
  }

  final case class ParamIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue {
    override def name: String = id.stringId
  }

  final case class ValIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue {
    override def name: String = id.stringId
  }

  final case class VarIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue {
    override def name: String = id.stringId
  }

  final case class UninterpretedConstIdValue(name: String, definingScope: Scope, uid: Long) extends NamedIdValue

  final case class IntermediateIdValue(definingScope: Scope, uid: Long, nameHintOpt: Option[String]) extends IdValue
  
  
  final case class IntConst(value: Int) extends Formula
  
  final case class BoolConst(value: Boolean) extends Formula
  
  final case class StringConst(value: String) extends Formula
  
  final case class Select(owner: Formula, field: FunOrVarId) extends Formula
  
  final case class Sum(terms: SeqSet[Formula]) extends Formula
  
  object Sum {
    def apply(terms: Formula*): Sum = new Sum(SeqSet(terms))
  }
  
  final case class Neg(operand: Formula) extends Formula
  
  final case class Times(terms: SeqSet[Formula]) extends Formula
  
  object Times {
    def apply(terms: Formula*): Times = new Times(SeqSet(terms))
  }
  
  final case class DivBy(lhs: Formula, rhs: Formula) extends Formula
  
  final case class Modulo(lhs: Formula, rhs: Formula) extends Formula
  
  // TODO may be optimized: when operand(s) do not change, return input as is
  extension (formula: Formula) def substitute(subst: Map[IdValue, Formula]): Formula = formula match {
    case value: IdValue => subst.getOrElse(value, value)
    case c: IntConst => c
    case c: BoolConst => c
    case c: StringConst => c
    case Select(owner, field) => Select(owner.substitute(subst), field)
    case Sum(terms) => Sum(terms.map(_.substitute(subst)))
    case Neg(operand) => Neg(operand.substitute(subst))
    case Times(terms) => Times(terms.map(_.substitute(subst)))
    case DivBy(lhs, rhs) => DivBy(lhs.substitute(subst), rhs.substitute(subst))
    case Modulo(lhs, rhs) => Modulo(lhs.substitute(subst), rhs.substitute(subst))
  }

}
