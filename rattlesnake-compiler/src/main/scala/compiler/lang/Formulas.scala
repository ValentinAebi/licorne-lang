package compiler.lang

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.SSA.{FieldResolutionTarget, InvocationTarget, Scope}
import compiler.lang.Types.Type
import compiler.util.SeqSet

// TODO cleaner pretty-printing system
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

  final case class Select(owner: Formula, var field: FieldResolutionTarget) extends Formula {
    override def toString: String = s"$owner.$field"
  }

  final case class Call(receiver: Formula, var func: InvocationTarget, typeArgs: List[Type], args: List[Formula]) extends Formula {
    override def toString: String = {
      val typeArgsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      s"$receiver.$func" ++ typeArgsDescr ++ args.mkString("(", ",", ")")
    }
  }

  final case class Plus(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = lhs.toString
      val opAndRhsStr = rhs match {
        case Neg(negated) => s" - $negated"
        case IntConst(cst) if cst < 0 => s" - ${-cst}"
        case rhs => s" + $rhs"
      }
      lhsStr ++ opAndRhsStr
    }
  }

  final case class Neg(operand: Formula) extends Formula {
    override def toString: String = operand match {
      case IntConst(cst) if cst < 0 => (-cst).toString
      case _ => "-" + parenthIfNot[IdValue | ConstFormula](operand)
    }
  }

  final case class Times(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIfNot[IdValue | ConstFormula](rhs)
      s"$lhsStr * $rhsStr"
    }
  }

  final case class DivBy(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIfNot[IdValue | ConstFormula](rhs)
      s"$lhsStr / $rhsStr"
    }
  }

  final case class Modulo(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIfNot[IdValue | ConstFormula](rhs)
      s"$lhsStr % $rhsStr"
    }
  }

  final case class LogicalAnd(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[LogicalOr](lhs)
      val rhsStr = parenthIf[LogicalOr](rhs)
      s"$lhs and $rhs"
    }
  }

  final case class LogicalNot(operand: Formula) extends Formula {
    override def toString: String = s"!$operand"
  }

  final case class LogicalOr(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = s"$lhs or $rhs"
  }

  final case class Equality(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = s"$lhs == $rhs"
  }

  final case class LessOrEq(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = s"$lhs <= $rhs"
  }

  final case class LessThan(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = s"$lhs < $rhs"
  }

  final case class TypePredicate(subject: Formula, tpe: TypeIdentifier) extends Formula {
    override def toString: String = s"$subject is $tpe"
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
    case Call(receiver, funId, typeArgs, args) => Call(receiver.substitute(subst), funId, typeArgs.map(_.substitute(Map.empty, subst)), args.map(_.substitute(subst)))
    case Plus(lhs, rhs) => Plus(lhs.substitute(subst), rhs.substitute(subst))
    case Neg(operand) => Neg(operand.substitute(subst))
    case Times(lhs, rhs) => Times(lhs.substitute(subst), rhs.substitute(subst))
    case DivBy(lhs, rhs) => DivBy(lhs.substitute(subst), rhs.substitute(subst))
    case Modulo(lhs, rhs) => Modulo(lhs.substitute(subst), rhs.substitute(subst))
    case LogicalNot(operand) => LogicalNot(operand.substitute(subst))
    case LogicalAnd(lhs, rhs) => LogicalAnd(lhs.substitute(subst), rhs.substitute(subst))
    case LogicalOr(lhs, rhs) => LogicalOr(lhs.substitute(subst), rhs.substitute(subst))
    case Equality(lhs, rhs) => Equality(lhs.substitute(subst), rhs.substitute(subst))
    case LessOrEq(lhs, rhs) => LessOrEq(lhs.substitute(subst), rhs.substitute(subst))
    case LessThan(lhs, rhs) => LessThan(lhs.substitute(subst), rhs.substitute(subst))
    case TypePredicate(subject, tpe) => TypePredicate(subject.substitute(subst), tpe)
  }

  extension (idValue: IdValue) def typeCanMention(formula: Formula): Boolean = formula match {
    case otherValue: IdValue =>
      (idValue.definingScope == otherValue.definingScope && idValue.uid > otherValue.uid) ||
        idValue.definingScope.isNestedIn(otherValue.definingScope)
    case formula: ConstFormula => true
    case Select(owner, FieldResolutionTarget.ResolvedField(receiverSig, fieldId, instantiatedFieldType)) =>
      receiverSig.fields(fieldId).isStable && typeCanMention(owner)
    case Select(owner, field) => false
    // TODO maybe check side-effects
    case Call(receiver, func, typeArgs, args) => false
    case Plus(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case Neg(operand) => typeCanMention(operand)
    case Times(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case DivBy(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case Modulo(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case LogicalAnd(lhs, rhs) => false
    case LogicalNot(operand) => false
    case LogicalOr(lhs, rhs) => false
    case Equality(lhs, rhs) => false
    case LessOrEq(lhs, rhs) => false
    case LessThan(lhs, rhs) => false
    case TypePredicate(subject, tpe) => false
  }

  extension (formula: Formula) def isStable: Boolean = formula match {
    case value: IdValue => true
    case Select(owner, FieldResolutionTarget.ResolvedField(receiverSig, fieldId, instantiatedFieldType)) =>
      receiverSig.fields(fieldId).isStable
    case _: Select => false
    case formula: ConstFormula => true
    // TODO maybe check side-effects
    case Call(receiver, func, typeArgs, args) => false
    case Plus(lhs, rhs) => lhs.isStable && rhs.isStable
    case Neg(operand) => operand.isStable
    case Times(lhs, rhs) => lhs.isStable && rhs.isStable
    case DivBy(lhs, rhs) => lhs.isStable && rhs.isStable
    case Modulo(lhs, rhs) => lhs.isStable && rhs.isStable
    case LogicalAnd(lhs, rhs) => lhs.isStable && rhs.isStable
    case LogicalNot(operand) => operand.isStable
    case LogicalOr(lhs, rhs) => lhs.isStable && rhs.isStable
    case Equality(lhs, rhs) => lhs.isStable && rhs.isStable
    case LessOrEq(lhs, rhs) => lhs.isStable && rhs.isStable
    case LessThan(lhs, rhs) => lhs.isStable && rhs.isStable
    case TypePredicate(subject, tpe) => subject.isStable
  }

}
