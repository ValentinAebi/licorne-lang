package compiler.lang

import compiler.identifiers.FunOrVarId
import compiler.irs.SSA.{FieldResolutionTarget, Scope}
import compiler.util.SeqSet

object Formulas {

  sealed trait Formula

  sealed trait IdValue extends Formula {
    def uid: Long

    def definingScope: Scope
  }

  sealed trait NamedIdValue(valKindDescr: String) extends IdValue {
    def name: String

    override def toString: String =
      s"$name#$uid@${definingScope.scopeUid}$valKindDescr"
  }

  final case class ParamIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue("p") {
    override def name: String = id.stringId
  }

  final case class ValIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue("s") {
    override def name: String = id.stringId
  }

  final case class VarIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue("r") {
    override def name: String = id.stringId
  }

  final case class UninterpretedConstIdValue(name: String, definingScope: Scope, uid: Long) extends NamedIdValue("c")

  final case class IntermediateIdValue(definingScope: Scope, uid: Long, nameHintOpt: Option[String]) extends IdValue {
    override def toString: String = s"${"$"}$uid@${definingScope.scopeUid}i"
  }

  sealed trait ConstFormula extends Formula {
    def value: Any

    override def toString: String = value.toString
  }

  final case class IntConst(value: Int) extends ConstFormula

  final case class BoolConst(value: Boolean) extends ConstFormula

  final case class StringConst(value: String) extends ConstFormula

  final case class Select(owner: Formula, field: FieldResolutionTarget) extends Formula {
    override def toString: String = s"$owner.$field"
  }
  
  final case class Call(receiver: Formula, funId: FunOrVarId, args: List[Formula]) extends Formula {
    override def toString: String =
      s"$receiver.$funId" ++ args.mkString("(", ",", ")")
  }

  final case class Sum(terms: SeqSet[Formula]) extends Formula {
    override def toString: String = {
      val sb = new StringBuilder
      var isFirst = true
      for (term <- terms) {
        term match {
          case neg: Neg if isFirst =>
            sb.append(neg)
          case Neg(operand) =>
            sb.append(" - ").append(operand)
          case term if isFirst =>
            sb.append(term)
          case term =>
            sb.append(" + ").append(term)
        }
        isFirst = false
      }
      sb.toString
    }
  }

  object Sum {
    def apply(terms: Formula*): Sum = new Sum(SeqSet(terms))
  }

  final case class Neg(operand: Formula) extends Formula {
    override def toString: String = "-" + parenthIfNot[IdValue | ConstFormula](operand)
  }

  final case class Times(terms: SeqSet[Formula]) extends Formula {
    override def toString: String = {
      val sb = new StringBuilder
      var isFirst = true
      for (term <- terms) {
        val termStr =
          if isFirst then parenthIfNot[Times | IdValue | ConstFormula](term)
          else parenthIf[Sum | Neg](term)
        if (!isFirst) {
          sb.append(" * ")
        }
        sb.append(termStr)
        isFirst = false
      }
      sb.toString()
    }
  }

  object Times {
    def apply(terms: Formula*): Times = new Times(SeqSet(terms))
  }

  final case class DivBy(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Sum | Neg](lhs)
      val rhsStr = parenthIfNot[IdValue | ConstFormula](rhs)
      s"$lhsStr / $rhsStr"
    }
  }

  final case class Modulo(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Sum | Neg](lhs)
      val rhsStr = parenthIfNot[IdValue | ConstFormula](rhs)
      s"$lhsStr % $rhsStr"
    }
  }

  private inline def parenthIf[F <: Formula](inline term: Formula): String = {
    val parenth = term.isInstanceOf[F]
    if parenth then s"($term)" else term.toString
  }

  private inline def parenthIfNot[F <: Formula](inline term: Formula): String = {
    val parenth = !term.isInstanceOf[F]
    if parenth then s"($term)" else term.toString
  }

  // TODO may be optimized: when operand(s) do not change, return input as is
  extension (formula: Formula) def substitute(subst: Map[IdValue, Formula]): Formula = formula match {
    case value: IdValue => subst.getOrElse(value, value)
    case c: IntConst => c
    case c: BoolConst => c
    case c: StringConst => c
    case Select(owner, field) => Select(owner.substitute(subst), field)
    case Call(receiver, funId, args) => Call(receiver.substitute(subst), funId, args.map(_.substitute(subst)))
    case Sum(terms) => Sum(terms.map(_.substitute(subst)))
    case Neg(operand) => Neg(operand.substitute(subst))
    case Times(terms) => Times(terms.map(_.substitute(subst)))
    case DivBy(lhs, rhs) => DivBy(lhs.substitute(subst), rhs.substitute(subst))
    case Modulo(lhs, rhs) => Modulo(lhs.substitute(subst), rhs.substitute(subst))
  }

}
