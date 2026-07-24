package compiler.irs.ssa

import compiler.identifiers.{FunOrVarId, ThisId, TypeIdentifier}
import compiler.irs.ssa.SSA.{LocalDecl, Scope}
import compiler.irs.ssa.{FieldResolutionTarget, InvocationTarget}
import compiler.lang.Types.Type
import compiler.lang.{Keyword, RuntimeTypeSignature}
import compiler.reporting.Position
import compiler.util.SeqSet

import java.util.Objects
import scala.collection


object Formulas {

  sealed trait Formula {
    def isAtomic = false
  }

  sealed trait IdValue extends Formula {
    def uid: Long

    def definingScope: Scope

    override def isAtomic: Boolean = true
  }

  sealed trait NamedIdValue(valKindDescr: String) extends IdValue {
    def name: String

    def posOpt: Option[Position]

    def irDescr: String =
      s"$name#$uid@${definingScope.scopeUid}$valKindDescr"

  }

  sealed trait LocalIdValue {
    this: NamedIdValue =>
    def id: FunOrVarId
  }

  final case class ParamIdValue(id: FunOrVarId, definingScope: Scope, uid: Long, posOpt: Option[Position]) extends NamedIdValue("p"), LocalIdValue {
    override def name: String = id.stringId

    override def toString: String = name
  }

  final case class ValIdValue(id: FunOrVarId, definingScope: Scope, uid: Long, posOpt: Option[Position]) extends NamedIdValue("s"), LocalIdValue {
    override def name: String = id.stringId

    override def toString: String = name
  }

  final case class VarIdValue(id: FunOrVarId, declOpt: Option[LocalDecl], definingScope: Scope, uid: Long, descrOpt: Option[String], posOpt: Option[Position]) extends NamedIdValue("r"), LocalIdValue {
    override def name: String = id.stringId

    override def toString: String = (descrOpt, posOpt) match {
      case (Some(descr), Some(position)) => s"$name<$descr@${position.lineColonColumn}>"
      case (Some(descr), None) => s"$name<$descr>"
      case (None, Some(position)) => s"$name<${position.lineColonColumn}>"
      case (None, None) => irDescr
    }
  }

  final case class HeapVarIdValue(id: FunOrVarId, definingScope: Scope, uid: Long, posOpt: Option[Position]) extends NamedIdValue("h") {
    override def name: String = id.stringId

    override def toString: String = s"$name<heap>"
  }

  final case class UninterpretedConstIdValue(name: String, definingScope: Scope, uid: Long) extends NamedIdValue("c") {
    override def posOpt: Option[Position] = None

    override def toString: String = name
  }

  final case class IntermediateIdValue(definingScope: Scope, uid: Long, var nameHint: String) extends IdValue {
    override def toString: String = s"$nameHint${"$"}snapshot${"$"}$uid@${definingScope.scopeUid}i"
  }

  sealed trait ConstFormula extends Formula {
    def value: Any

    override def isAtomic: Boolean = true

    override def toString: String = value.toString
  }

  final case class IntConst(value: Int) extends ConstFormula

  final case class BoolConst(value: Boolean) extends ConstFormula

  final case class StringConst(value: String) extends ConstFormula {
    override def toString: String = s"\"$value\""
  }

  final case class Select(owner: Formula, field: FieldResolutionTarget) extends Formula {

    override def equals(that: Any): Boolean = that match {
      case Select(thatOwner, thatField) =>
        this.owner == thatOwner && this.field.fieldId == thatField.fieldId
      case _ => false
    }

    override def hashCode(): Int = Objects.hash(owner, field.fieldId)

    override def toString: String = s"$owner.${field.fieldId}"
  }

  final case class FunCall(receiver: Formula, func: InvocationTarget, var typeArgs: List[Type], args: List[Formula]) extends Formula {

    override def equals(that: Any): Boolean = that match {
      case FunCall(thatReceiver, thatFunc, _, thatArgs) =>
        this.receiver == thatReceiver && this.func.funId == thatFunc.funId && this.args == thatArgs
      case _ => false
    }

    override def hashCode(): Int = Objects.hash(receiver, func.funId, args)

    override def toString: String = {
      val typeArgsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      s"$receiver.${func.funId}" ++ typeArgsDescr ++ args.mkString("(", ",", ")")
    }
  }

  final case class ClosureCall private(callee: Formula, closureTypingTarget: ClosureTypingTarget, args: List[Formula]) extends Formula {
    override def toString: String = s"$callee(" ++ args.mkString(",") ++ ")"
  }

  object ClosureCall {
    def apply(callee: Formula, target: ClosureTypingTarget, args: List[Formula]): Formula = callee match {
      case PureClosureValue(params, body, closureVal) =>
        val subst = params.zip(args).toMap
        body.substitute(subst)
      case callee => new ClosureCall(callee, target, args)
    }
  }

  final case class PureClosureValue(params: List[IdValue], body: Formula, closureVal: IdValue) extends Formula {
    override def toString: String = Keyword.Fn.str + " " + params.mkString("(", ", ", ")") + " -> " + body
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

    override def isAtomic: Boolean = operand.isAtomic

    override def toString: String = operand match {
      case IntConst(cst) if cst < 0 => (-cst).toString
      case _ => "-" + parenthIfNot[IdValue | ConstFormula](operand)
    }
  }

  final case class Times(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIf[Plus | Neg | DivBy](rhs)
      s"$lhsStr * $rhsStr"
    }
  }

  final case class DivBy(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIf[Plus | Neg | Times | DivBy](rhs)
      s"$lhsStr / $rhsStr"
    }
  }

  final case class Modulo(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIf[Plus | Neg | Times | DivBy](rhs)
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
    override def toString: String = operand match {
      case Equality(lhs, rhs) => s"$lhs != $rhs"
      case operand => s"!${parenthIfNot[IdValue | ConstFormula | FunCall | ClosureCall](operand)}"
    }
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

  final case class Phi(terms: SeqSet[Formula]) extends Formula {
    override def toString: String = terms.mkString("phi(", ",", ")")
  }

  object Phi {
    def apply(terms: Iterable[Formula]): Phi = new Phi(SeqSet(terms))

    def apply(terms: Formula*): Phi = new Phi(SeqSet(terms))
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
  extension (formula: Formula) def substitute(subst: collection.Map[IdValue, Formula]): Formula = formula match {
    case value: IdValue => subst.getOrElse(value, value)
    case c: IntConst => c
    case c: BoolConst => c
    case c: StringConst => c
    case Select(owner, field) => Select(owner.substitute(subst), field)
    case FunCall(receiver, funId, typeArgs, args) => FunCall(receiver.substitute(subst), funId, typeArgs.map(_.substitute(Map.empty, subst)), args.map(_.substitute(subst)))
    case ClosureCall(callee, target, args) => ClosureCall(callee.substitute(subst), target, args.map(_.substitute(subst)))
    case PureClosureValue(params, body, closureVal) => PureClosureValue(params, body.substitute(subst.filterNot(params.contains)), closureVal)
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
    case Phi(terms) => Phi(terms.map(_.substitute(subst)))
  }

  // TODO may be optimized: when operand(s) do not change, return input as is
  extension (formula: Formula) def substitute(target: Formula, repl: Formula): Formula = formula match {
    case formula if formula == target => repl
    case value: IdValue => value
    case formula: ConstFormula => formula
    case Select(owner, field) => Select(owner.substitute(target, repl), field)
    case FunCall(receiver, func, typeArgs, args) => FunCall(receiver.substitute(target, repl), func, typeArgs, args.map(_.substitute(target, repl)))
    case ClosureCall(callee, closureTypingTarget, args) => ClosureCall(callee.substitute(target, repl), closureTypingTarget, args.map(_.substitute(target, repl)))
    case formula@PureClosureValue(params, body, closureVal) if params.contains(target) => formula
    case PureClosureValue(params, body, closureVal) => PureClosureValue(params, body.substitute(target, repl), closureVal)
    case Plus(lhs, rhs) => Plus(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case Neg(operand) => Neg(operand.substitute(target, repl))
    case Times(lhs, rhs) => Times(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case DivBy(lhs, rhs) => DivBy(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case Modulo(lhs, rhs) => Modulo(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case LogicalAnd(lhs, rhs) => LogicalAnd(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case LogicalNot(operand) => LogicalNot(operand.substitute(target, repl))
    case LogicalOr(lhs, rhs) => LogicalOr(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case Equality(lhs, rhs) => Equality(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case LessOrEq(lhs, rhs) => LessOrEq(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case LessThan(lhs, rhs) => LessThan(lhs.substitute(target, repl), rhs.substitute(target, repl))
    case TypePredicate(subject, tpe) => TypePredicate(subject.substitute(target, repl), tpe)
    case Phi(terms) => Phi(terms.map(_.substitute(target, repl)))
  }

  extension (idValue: IdValue) def typeCanMention(formula: Formula): Boolean = formula match {
    case otherValue: IdValue =>
      (idValue.definingScope == otherValue.definingScope && idValue.uid > otherValue.uid) ||
        idValue.definingScope.isNestedIn(otherValue.definingScope)
    case formula: ConstFormula => true
    case Select(owner, field) if field.isResolved =>
      field.getReceiverSigUnsafe.fields(field.fieldId).isStable && typeCanMention(owner)
    case Select(owner, field) => false
    case FunCall(receiver, func, typeArgs, args) =>
      typeCanMention(receiver) && func.isResolved && func.getFunSigUnsafe.isPure && args.forall(typeCanMention)
    case ClosureCall(callee, target, args) =>
      typeCanMention(callee) && target.isResolvedAndPure && args.forall(typeCanMention)
    case PureClosureValue(params, body, closureVal) => typeCanMention(body)
    case Plus(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case Neg(operand) => typeCanMention(operand)
    case Times(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case DivBy(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case Modulo(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case LogicalAnd(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case LogicalNot(operand) => typeCanMention(operand)
    case LogicalOr(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case Equality(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case LessOrEq(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case LessThan(lhs, rhs) => typeCanMention(lhs) && typeCanMention(rhs)
    case TypePredicate(subject, tpe) => typeCanMention(subject)
    case Phi(terms) => terms.forall(typeCanMention)
  }

  extension (formula: Formula) def isPure: Boolean = formula match {
    case value: IdValue => true
    case Select(owner, field) if field.isResolved =>
      owner.isPure && field.getReceiverSigUnsafe.fields(field.fieldId).isStable
    case _: Select => false
    case formula: ConstFormula => true
    case FunCall(receiver, func, typeArgs, args) =>
      receiver.isPure && func.isResolvedAndPure && func.getFunSigUnsafe.isPure && args.forall(_.isPure)
    case ClosureCall(callee, target, args) =>
      callee.isPure && target.isResolvedAndPure && args.forall(_.isPure)
    case PureClosureValue(params, body, closureVal) => true
    case Plus(lhs, rhs) => lhs.isPure && rhs.isPure
    case Neg(operand) => operand.isPure
    case Times(lhs, rhs) => lhs.isPure && rhs.isPure
    case DivBy(lhs, rhs) => lhs.isPure && rhs.isPure
    case Modulo(lhs, rhs) => lhs.isPure && rhs.isPure
    case LogicalAnd(lhs, rhs) => lhs.isPure && rhs.isPure
    case LogicalNot(operand) => operand.isPure
    case LogicalOr(lhs, rhs) => lhs.isPure && rhs.isPure
    case Equality(lhs, rhs) => lhs.isPure && rhs.isPure
    case LessOrEq(lhs, rhs) => lhs.isPure && rhs.isPure
    case LessThan(lhs, rhs) => lhs.isPure && rhs.isPure
    case TypePredicate(subject, tpe) => subject.isPure
    case Phi(terms) => terms.forall(_.isPure)
  }

  extension (formula: Formula) def idValsDependencies: Set[IdValue] = formula match {
    case value: IdValue => Set(value)
    case formula: ConstFormula => Set.empty
    case Select(owner, field) => owner.idValsDependencies
    case FunCall(receiver, func, typeArgs, args) =>
      receiver.idValsDependencies ++ args.flatMap(_.idValsDependencies)
    case ClosureCall(callee, closureTypingTarget, args) =>
      callee.idValsDependencies ++ args.flatMap(_.idValsDependencies)
    case PureClosureValue(params, body, closureVal) =>
      body.idValsDependencies -- params
    case Plus(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case Neg(operand) => operand.idValsDependencies
    case Times(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case DivBy(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case Modulo(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case LogicalAnd(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case LogicalNot(operand) =>
      operand.idValsDependencies
    case LogicalOr(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case Equality(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case LessOrEq(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case LessThan(lhs, rhs) =>
      lhs.idValsDependencies ++ rhs.idValsDependencies
    case TypePredicate(subject, tpe) =>
      subject.idValsDependencies
    case Phi(terms) => terms.flatMap(_.idValsDependencies)
  }

  extension (formula: Formula) def transformParamValsIntoSelectOn(owner: Formula)(using ownerSig: RuntimeTypeSignature): Formula = formula match {
    case paramIdVal@ParamIdValue(id, definingScope, uid, defPosOpt) if id != ThisId =>
      val field = FieldResolutionTarget(id)
      ownerSig.stableFields.get(paramIdVal.id).foreach { fld =>
        field.resolve(ownerSig, fld.tpe)
      }
      Select(owner, field)
    case value: IdValue => value
    case cst: ConstFormula => cst
    case Select(owner, field) => Select(owner.transformParamValsIntoSelectOn(owner), field)
    case FunCall(receiver, func, typeArgs, args) => FunCall(
      receiver.transformParamValsIntoSelectOn(owner),
      func,
      typeArgs.map(_.withDependenciesTransformed(_.transformParamValsIntoSelectOn(owner))),
      args.map(_.transformParamValsIntoSelectOn(owner))
    )
    case ClosureCall(callee, closureTypingTarget, args) => ClosureCall(callee.transformParamValsIntoSelectOn(owner), closureTypingTarget, args.map(_.transformParamValsIntoSelectOn(owner)))
    case closure: PureClosureValue => closure
    case Plus(lhs, rhs) => Plus(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case Neg(operand) => Neg(operand.transformParamValsIntoSelectOn(owner))
    case Times(lhs, rhs) => Times(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case DivBy(lhs, rhs) => DivBy(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case Modulo(lhs, rhs) => Modulo(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case LogicalAnd(lhs, rhs) => LogicalAnd(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case LogicalNot(operand) => LogicalNot(operand.transformParamValsIntoSelectOn(owner))
    case LogicalOr(lhs, rhs) => LogicalOr(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case Equality(lhs, rhs) => Equality(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case LessOrEq(lhs, rhs) => LessOrEq(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case LessThan(lhs, rhs) => LessThan(lhs.transformParamValsIntoSelectOn(owner), rhs.transformParamValsIntoSelectOn(owner))
    case TypePredicate(subject, tpe) => TypePredicate(subject.transformParamValsIntoSelectOn(owner), tpe)
    case Phi(terms) => Phi(terms.map(_.transformParamValsIntoSelectOn(owner)))
  }

  extension (subject: Formula) def typeCanMention(dep: Formula): Boolean =
    !subject.isInstanceOf[ConstFormula] && subject.idValsDependencies.forall(_.typeCanMention(dep))

}
