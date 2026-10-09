package compiler.irs.ircorne

import compiler.identifiers.{FunOrVarId, ThisId, TypeIdentifier}
import compiler.irs.ircorne.IRcorne.{LocalDecl, Scope}
import compiler.irs.ircorne.{FieldResolutionTarget, InvocationTarget}
import compiler.lang.Types.Type
import compiler.lang.{Operator, RuntimeTypeSignature}
import compiler.reporting.Position
import compiler.util.SeqSet

import java.util.Objects
import scala.collection


object Formulas {

  sealed trait Formula {
    def isAtomic = false

    def children: List[Formula]

    final override def toString: String = SourceLevelFormulaPrinter.prettyprint(this)

    def traversePreOrder(action: Formula => Unit): Unit = {
      action(this)
      for (child <- children) {
        child.traversePreOrder(action)
      }
    }
  }

  sealed trait AtomicValue extends Formula

  sealed abstract class IdValue extends AtomicValue {
    def uid: Long

    def definingScope: Scope

    override def isAtomic: Boolean = true

    override def children: List[Formula] = List.empty
  }

  sealed trait NamedIdValue(val valKindDescr: String) extends IdValue {
    def name: String

    def posOpt: Option[Position]
  }

  sealed trait LocalIdValue {
    this: NamedIdValue =>
    def id: FunOrVarId
  }

  sealed trait Binop(val op: Operator) extends Formula {

    def lhs: Formula

    def rhs: Formula

    override def children: List[Formula] = List(lhs, rhs)
  }
  
  sealed trait NumericFormula extends Formula
  
  sealed trait LogicFormula extends Formula
  
  sealed trait ComparisonFormula extends LogicFormula

  final case class ParamIdValue(id: FunOrVarId, definingScope: Scope, uid: Long, posOpt: Option[Position]) extends NamedIdValue("p"), LocalIdValue {
    override def name: String = id.stringId

  }

  final case class ValIdValue(id: FunOrVarId, definingScope: Scope, uid: Long, posOpt: Option[Position]) extends NamedIdValue("s"), LocalIdValue {
    override def name: String = id.stringId
  }

  final case class VarIdValue(id: FunOrVarId, declOpt: Option[LocalDecl], definingScope: Scope, uid: Long, descrOpt: Option[String], posOpt: Option[Position]) extends NamedIdValue("r"), LocalIdValue {
    override def name: String = id.stringId
  }

  final case class HeapVarIdValue(id: FunOrVarId, definingScope: Scope, uid: Long, posOpt: Option[Position]) extends NamedIdValue("h") {
    private var annotTypeOpt: Option[Type] = None

    def offerAnnotType(annotOpt: Option[Type]): Unit = {
      if (annotTypeOpt.isEmpty && annotOpt.nonEmpty) {
        annotTypeOpt = annotOpt
      }
    }

    def getAnnotTypeOpt: Option[Type] = annotTypeOpt

    override def name: String = id.stringId
  }

  final case class UninterpretedConstIdValue(name: String, definingScope: Scope, uid: Long) extends NamedIdValue("c") {
    override def posOpt: Option[Position] = None
  }

  final case class IntermediateIdValue(definingScope: Scope, uid: Long, var nameHint: String) extends IdValue

  sealed trait ConstFormula extends AtomicValue {
    def value: Any

    override def isAtomic: Boolean = true

    override def children: List[Formula] = List.empty
  }

  final case class IntConst(value: Int) extends ConstFormula, NumericFormula

  final case class BoolConst(value: Boolean) extends ConstFormula, LogicFormula

  final case class StringConst(value: String) extends ConstFormula

  final case class Select(owner: Formula, field: FieldResolutionTarget) extends Formula {

    override def children: List[Formula] = List(owner)

    override def equals(that: Any): Boolean = that match {
      case Select(thatOwner, thatField) =>
        this.owner == thatOwner && this.field.fieldId == thatField.fieldId
      case _ => false
    }

    override def hashCode(): Int = Objects.hash(owner, field.fieldId)
  }

  final case class FunCall(receiver: Formula, func: InvocationTarget, var typeArgs: List[Type], args: List[Formula]) extends Formula {

    override def children: List[Formula] = receiver :: args

    override def equals(that: Any): Boolean = that match {
      case FunCall(thatReceiver, thatFunc, _, thatArgs) =>
        this.receiver == thatReceiver && this.func.funId == thatFunc.funId && this.args == thatArgs
      case _ => false
    }

    override def hashCode(): Int = Objects.hash(receiver, func.funId, args)
  }

  final case class ClosureCall private(callee: Formula, closureTypingTarget: ClosureTypingTarget, args: List[Formula]) extends Formula {
    override def children: List[Formula] = callee :: args
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
    override def children: List[Formula] = params :+ body :+ closureVal
  }

  final case class Plus(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.Plus), NumericFormula

  final case class Neg(operand: Formula) extends Formula {
    override def isAtomic: Boolean = operand.isAtomic

    override def children: List[Formula] = List(operand)
  }

  final case class Times(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.Times), NumericFormula

  final case class DivBy(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.Div), NumericFormula

  final case class Modulo(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.Modulo), NumericFormula

  final case class LogicalAnd(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.And), LogicFormula

  final case class LogicalNot(operand: Formula) extends Formula, LogicFormula {
    override def isAtomic: Boolean = operand.isAtomic

    override def children: List[Formula] = List(operand)
  }

  final case class LogicalOr(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.Or), LogicFormula

  final case class Equality(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.Equality), ComparisonFormula

  final case class LessOrEq(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.LessOrEq), ComparisonFormula

  final case class LessThan(lhs: Formula, rhs: Formula) extends Formula, Binop(Operator.LessThan), ComparisonFormula

  final case class TypePredicate(subject: Formula, tpe: TypeIdentifier) extends Formula, LogicFormula {
    override def children: List[Formula] = List(subject)
  }

  final case class Phi(terms: SeqSet[Formula]) extends Formula {
    override def children: List[Formula] = terms.toList
  }

  final case class WrappedScope(resVal: IdValue, scope: Scope) extends Formula {
    override def children: List[Formula] = List.empty
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

  extension (formula: Formula) def applyRecursively(pf: PartialFunction[Formula, Formula]): Formula =
    formula.applyRecursively(pf.applyOrElse(_, identity))

  extension (formula: Formula) def applyRecursively(f: Formula => Formula): Formula = f(formula match {
    case value: AtomicValue => value
    case Select(owner, field) => Select(owner.applyRecursively(f), field)
    case FunCall(receiver, func, typeArgs, args) =>
      FunCall(receiver.applyRecursively(f), func, typeArgs.map(_.withDependenciesTransformed(_.applyRecursively(f))), args.map(_.applyRecursively(f)))
    case ClosureCall(callee, closureTypingTarget, args) =>
      ClosureCall(callee.applyRecursively(f), closureTypingTarget, args.map(_.applyRecursively(f)))
    case PureClosureValue(params, body, closureVal) =>
      PureClosureValue(params, body.applyRecursively(f), closureVal)
    case Plus(lhs, rhs) => Plus(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case Neg(operand) => Neg(operand.applyRecursively(f))
    case Times(lhs, rhs) => Times(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case DivBy(lhs, rhs) => DivBy(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case Modulo(lhs, rhs) => Modulo(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case LogicalAnd(lhs, rhs) => LogicalAnd(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case LogicalNot(operand) => LogicalNot(operand.applyRecursively(f))
    case LogicalOr(lhs, rhs) => LogicalOr(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case Equality(lhs, rhs) => Equality(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case LessOrEq(lhs, rhs) => LessOrEq(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case LessThan(lhs, rhs) => LessThan(lhs.applyRecursively(f), rhs.applyRecursively(f))
    case TypePredicate(subject, tpe) => TypePredicate(subject.applyRecursively(f), tpe)
    case Phi(terms) => Phi(terms.map(_.applyRecursively(f)))
    case WrappedScope(resVal, scope) => WrappedScope(resVal, scope)
  })

  // TODO may be optimized: when operand(s) do not change, return input as is
  extension (formula: Formula) def substitute(subst: collection.Map[IdValue, Formula]): Formula =
    formula.applyRecursively {
      case value: IdValue => subst.getOrElse(value, value)
    }

  // TODO may be optimized: when operand(s) do not change, return input as is
  extension (formula: Formula) def substitute(target: Formula, repl: Formula): Formula =
    formula.applyRecursively {
      case formula if formula == target => repl
    }

  extension (idValue: IdValue) def typeCanMention(formula: Formula): Boolean = formula match {
    case otherValue: IdValue =>
      (idValue.definingScope == otherValue.definingScope && idValue.uid > otherValue.uid) ||
        idValue.definingScope.isNestedIn(otherValue.definingScope)
    case formula: ConstFormula => true
    case Select(owner, field) if field.isResolved =>
      field.getFieldUnsafe.isStable && typeCanMention(owner)
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
    case _: WrappedScope => throw UnsupportedOperationException(s"typeCanMention on a ${classOf[WrappedScope].getSimpleName}")
  }

  extension (formula: Formula) def isPure: Boolean = formula match {
    case value: IdValue => true
    case Select(owner, field) if field.isResolved =>
      owner.isPure && field.getFieldUnsafe.isStable
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
    case WrappedScope(resVal, scope) => scope.isObviouslyPure
  }

  extension (formula: Formula) def idValsDependencies: Set[IdValue] = {
    val deps = Set.newBuilder[IdValue]
    formula.traversePreOrder {
      case idValue: IdValue =>
        deps.addOne(idValue)
      case _ => ()
    }
    deps.result()
  }

  extension (formula: Formula) def transformParamValsIntoSelectOn(owner: Formula, ownerSig: RuntimeTypeSignature): Formula =
    formula.applyRecursively {
      case paramIdVal@ParamIdValue(id, definingScope, uid, defPosOpt) if id != ThisId =>
        val field = FieldResolutionTarget(id)
        ownerSig.stableExposedFields.get(paramIdVal.id).foreach { fld =>
          field.resolve(ownerSig, fld.tpe)
        }
        Select(owner, field)
    }

  extension (formula: Formula) def convertThisDotFieldToFieldVal(tSig: RuntimeTypeSignature): Formula =
    formula.applyRecursively {
      case Select(owner, field) if field.isResolved && owner == tSig.sigScope.getLocalValuesContextUnsafe.getThisValue.get =>
        field.getFieldUnsafe.value
      case funCall@FunCall(receiver, func, typeArgs, args) if func.isResolved && receiver == tSig.sigScope.getLocalValuesContextUnsafe.getThisValue.get =>
        tSig.fields.get(func.funId).map(_.value).getOrElse(funCall)
    }

  extension (subject: Formula) def typeCanMention(dep: Formula): Boolean =
    !subject.isInstanceOf[ConstFormula] && subject.idValsDependencies.forall(_.typeCanMention(dep))

}
