package lang

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Types.{BaseType, NominalType, RefinedType, Type, UnionType}

object Formulas {

  sealed trait Formula {
    final override def toString: String = formulaToString(this)(using _ => None)
    def typedStr(using typeFunc: IdValue => Option[Type]): String = formulaToString(this)
    def str: String = typedStr(using _ => None)
  }

  sealed trait Capturable

  sealed trait Value extends Formula

  trait IdValue extends Value, Capturable {
    def completeDescr: String
    def sourceLevelDescrOrDefault: String
  }

  final case class RegularIdValue(varId: String, idx: Long) extends IdValue {
    override def completeDescr: String = s"$varId$$$idx"
    override def sourceLevelDescrOrDefault: String = varId
  }

  sealed trait Constant extends Value {
    def valueDescr: String
  }

  case object True extends Constant {
    override def valueDescr: String = "true"
  }

  case object False extends Constant {
    override def valueDescr: String = "false"
  }

  case object NullPtr extends Constant {
    override def valueDescr: String = "null"
  }
  
  case object UnitVal extends Constant {
    override def valueDescr: String = "unit"
  }

  final case class IntConstant(value: Int) extends Constant {
    override def valueDescr: String = value.toString
  }

  final case class DoubleConstant(value: Double) extends Constant {
    override def valueDescr: String = value.toString
  }

  final case class StringConstant(value: String) extends Constant {
    override def valueDescr: String = s"\"$value\""
  }

  sealed trait BinOp(val operator: Operator) extends Formula {
    def lhs: Formula

    def rhs: Formula
  }

  sealed trait UnaryOp(val operator: Operator) extends Formula {
    def operand: Formula
  }

  final case class Plus(lhs: Formula, rhs: Formula) extends BinOp(Operator.Plus)

  final case class Minus(lhs: Formula, rhs: Formula) extends BinOp(Operator.Minus)

  final case class Times(lhs: Formula, rhs: Formula) extends BinOp(Operator.Times)

  final case class Div(lhs: Formula, rhs: Formula) extends BinOp(Operator.Div)

  final case class Rem(lhs: Formula, rhs: Formula) extends BinOp(Operator.Modulo)

  final case class Neg(operand: Formula) extends UnaryOp(Operator.Minus)

  final case class And(lhs: Formula, rhs: Formula) extends BinOp(Operator.And)

  final case class Or(lhs: Formula, rhs: Formula) extends BinOp(Operator.Or)

  final case class Not(operand: Formula) extends UnaryOp(Operator.ExclamationMark)

  final case class LessThan(lhs: Formula, rhs: Formula) extends BinOp(Operator.LessThan)

  final case class LessOrEq(lhs: Formula, rhs: Formula) extends BinOp(Operator.LessOrEq)

  final case class Equal(lhs: Formula, rhs: Formula) extends BinOp(Operator.Equality)

  final case class Call(receiver: Formula, funId: FunOrVarId, typeArgs: List[Type], args: List[Formula]) extends Formula, Capturable

  final case class ClosureInvocation(closure: Formula, args: List[Formula]) extends Formula, Capturable

  final case class Select(owner: Formula, fieldName: FunOrVarId) extends Formula, Capturable

  final case class HasType(formula: Formula, tpe: TypeIdentifier) extends Formula

  case object RootCapability extends Capturable {
    override def toString: String = "cap"
  }

  val zero: IntConstant = IntConstant(0)
  val one: IntConstant = IntConstant(1)

  extension (formula: Formula) def asCst: Option[Constant] = formula match {
    case cst: Constant => Some(cst)
    case _ => None
  }

  extension (formula: Formula) def simplified: Formula = formula match {
    case value: Value => value
    case Plus(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (l, r) if l == zero => r
        case (l, r) if r == zero => l
        case (IntConstant(lc), IntConstant(lr)) => IntConstant(lc + lr)
        case (l, r) => Plus(l, r)
      }
    case Minus(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (l, r) if l == zero => Neg(r)
        case (l, r) if r == zero => l
        case (l: Value, r: Value) if l == r => zero
        case (IntConstant(lc), IntConstant(lr)) => IntConstant(lc - lr)
        case (l, r) => Minus(l, r)
      }
    case Times(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (l, r) if l == zero => zero
        case (l, r) if r == zero => zero
        case (l, r) if l == one => r
        case (l, r) if r == one => l
        case (IntConstant(lc), IntConstant(lr)) => IntConstant(lc * lr)
        case (l, r) => Times(l, r)
      }
    case Div(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (l, r) if r == one => l
        case (l: Value, r: Value) if r != zero && l == r => one
        case (IntConstant(lc), IntConstant(lr)) if lr != 0 => IntConstant(lc / lr)
        case (l, r) => Div(l, r)
      }
    case Rem(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (IntConstant(lc), IntConstant(lr)) if lr != 0 => IntConstant(lc % lr)
        case (l, r) => Rem(l, r)
      }
    case And(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (True, r) => r
        case (False, r) if r.isPureByConstruction => False
        case (l, True) => l
        case (l, False) if l.isPureByConstruction => False
        case (l, r) => And(l, r)
      }
    case Or(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (True, r) if r.isPureByConstruction => True
        case (False, r) => r
        case (l, True) if l.isPureByConstruction => True
        case (l, False) => l
        case (l, r) => Or(l, r)
      }
    case LessThan(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (IntConstant(lc), IntConstant(lr)) =>
          if lc < lr then True else False
        case (l, r) => LessThan(l, r)
      }
    case LessOrEq(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (IntConstant(lc), IntConstant(lr)) =>
          if lc <= lr then True else False
        case (l, r) => LessOrEq(l, r)
      }
    case Equal(lhs, rhs) =>
      (lhs.simplified, rhs.simplified) match {
        case (l: Value, r: Value) =>
          if l == r then True else False
        case (l, r) => Equal(l, r)
      }
    case Neg(operand) =>
      operand.simplified match {
        case Neg(subOperand) => subOperand
        case IntConstant(cst) => IntConstant(-cst)
        case opSimplified => Neg(opSimplified)
      }
    case Not(operand) =>
      operand.simplified match {
        case Not(subOperand) => subOperand
        case True => False
        case False => True
        case opSimplified => Not(opSimplified)
      }
    case Call(receiver, funId, typeArgs, args) =>
      Call(receiver.simplified, funId, typeArgs.map(simplifyPredicates), args.map(_.simplified))
    case ClosureInvocation(closure, args) =>
      ClosureInvocation(closure.simplified, args.map(_.simplified))
    case Select(owner, fieldName) =>
      Select(owner.simplified, fieldName)
    case HasType(formula, tpe) =>
      HasType(formula.simplified, tpe)
  }

  extension (formula: Formula) def isPureByConstruction: Boolean = formula match {
    case value: Value => true
    case op: BinOp =>
      op.lhs.isPureByConstruction && op.rhs.isPureByConstruction
    case op: UnaryOp =>
      op.operand.isPureByConstruction
    case Call(receiver, funId, typeArgs, args) => false
    case ClosureInvocation(closure, args) => false
    case Select(owner, fieldName) => false
    case HasType(formula, tpe) => formula.isPureByConstruction
  }

  extension (formula: Formula) def substitute(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Formula = formula match {
    case value: IdValue => valsSubst.getOrElse(value, value)
    case constant: Constant => constant
    case Plus(lhs, rhs) => Plus(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Minus(lhs, rhs) => Minus(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Times(lhs, rhs) => Times(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Div(lhs, rhs) => Div(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Rem(lhs, rhs) => Rem(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case And(lhs, rhs) => And(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Or(lhs, rhs) => Or(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case LessThan(lhs, rhs) => LessThan(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case LessOrEq(lhs, rhs) => LessOrEq(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Equal(lhs, rhs) => Equal(lhs.substitute(typesSubst, valsSubst), rhs.substitute(typesSubst, valsSubst))
    case Neg(operand) => Neg(operand.substitute(typesSubst, valsSubst))
    case Not(operand) => Not(operand.substitute(typesSubst, valsSubst))
    case Call(receiver, funId, typeArgs, args) =>
      Call(receiver.substitute(typesSubst, valsSubst), funId,
        typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(typesSubst, valsSubst)))
    case ClosureInvocation(closure, args) =>
      ClosureInvocation(closure.substitute(typesSubst, valsSubst), args.map(_.substitute(typesSubst, valsSubst)))
    case Select(owner, fieldName) => Select(owner.substitute(typesSubst, valsSubst), fieldName)
    case HasType(formula, tpe) => HasType(formula.substitute(typesSubst, valsSubst), tpe)
  }

  def formulaToString(formula: Formula)(using typeFunc: (IdValue => Option[Type])): String = formula match {
    case idValue: IdValue =>
      val strWithoutType = idValue.completeDescr
      typeFunc(idValue) match {
        case Some(tpe) => s"($strWithoutType : $tpe)"
        case None => strWithoutType
      }
    case constant: Constant =>
      constant.valueDescr
    case op: BinOp =>
      s"${formulaToString(op.lhs)} ${op.operator} ${formulaToString(op.rhs)}"
    case op: UnaryOp =>
      s"${op.operator} ${formulaToString(op.operand)}"
    case Call(receiver, funId, typeArgs, args) =>
      val typeArgsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      s"${formulaToString(receiver)}.$funId(${args.map(formulaToString).mkString(", ")})"
    case ClosureInvocation(closure, args) =>
      s"$closure" + args.mkString("(", ", ", ")")
    case Select(owner, fieldName) =>
      s"${formulaToString(owner)}.$fieldName"
    case HasType(formula, tpe) =>
      s"${formulaToString(formula)} is $tpe"
  }

  private def simplifyPredicates(tpe: Type): Type = tpe match {
    case Types.RefinedType(baseType, itValue, predicate) =>
      RefinedType(baseType, itValue, predicate.simplified)
    case Types.UnionType(types) =>
      UnionType(types.map(simplifyPredicates))
    case baseType: Types.BaseType =>
      simplifyPredicates(baseType)
  }

}
