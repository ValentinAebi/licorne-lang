package compiler.irs.ssa

import compiler.identifiers.FunOrVarId
import compiler.irs.ssa.SSA.Scope
import compiler.util.SeqSet

object Formulas {
  
  sealed trait Formula

  sealed trait IdValue extends Formula {
    def uid: Long

    def definingScope: Scope
  }

  sealed trait UserDefinedIdValue extends IdValue {
    def srcId: FunOrVarId
  }

  final case class ParamIdValue(srcId: FunOrVarId, definingScope: Scope, uid: Long) extends UserDefinedIdValue

  final case class ValIdValue(srcId: FunOrVarId, definingScope: Scope, uid: Long) extends UserDefinedIdValue

  final case class VarIdValue(srcId: FunOrVarId, definingScope: Scope, uid: Long) extends UserDefinedIdValue

  final case class IntermediateIdValue(definingScope: Scope, uid: Long, nameHintOpt: Option[String]) extends IdValue

  final case class UninterpretedConst(descr: String, definingScope: Scope, uid: Long) extends IdValue
  
  
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

}
