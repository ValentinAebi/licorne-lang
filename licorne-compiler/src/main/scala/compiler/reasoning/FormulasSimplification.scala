package compiler.reasoning

import compiler.irs.ircorne.Formulas.*
import compiler.stdlib.StdLib.{isFunc, sizeFunId, stringTypeId}

import scala.reflect.ClassTag

object FormulasSimplification {

  def simplifyFormula(formula: Formula): Formula = formula match {
    case formula: NumericFormula => simplifyNumeric(formula)
    case formula: LogicFormula => simplifyBool(formula)
    case _ => formula
  }

  def simplifyBool(formula: Formula): Formula = formula match {
    case LogicalAnd(lhs, rhs) =>
      (simplifyBool(lhs), simplifyBool(rhs)) match {
        case (lhs, BoolConst(true)) => lhs
        case (BoolConst(true), rhs) => rhs
        case (lhs, rhs) => LogicalAnd(lhs, rhs)
      }
    case LogicalNot(operand) =>
      simplifyBool(operand) match {
        case BoolConst(cst) => BoolConst(!cst)
        case LogicalNot(subOperand) => subOperand
        case operand => LogicalNot(operand)
      }
    case LogicalOr(lhs, rhs) =>
      (simplifyBool(lhs), simplifyBool(rhs)) match {
        case (lhs, BoolConst(false)) => lhs
        case (BoolConst(false), rhs) => rhs
        case (lhs, rhs) => LogicalOr(lhs, rhs)
      }
    case Equality(lhs, rhs) if lhs == rhs =>
      // TODO recurse?
      BoolConst(true)
    case LessOrEq(lhs, rhs) =>
      (simplifyNumeric(lhs), simplifyNumeric(rhs)) match {
        case (IntConst(l), IntConst(r)) => BoolConst(l <= r)
        case (lhs, Plus(pLhs, IntConst(-1))) => LessThan(lhs, pLhs)
        case (Plus(pLhs, IntConst(1)), rhs) => LessThan(pLhs, rhs)
        case (lhs, rhs) => LessOrEq(lhs, rhs)
      }
    case LessThan(lhs, rhs) =>
      (simplifyNumeric(lhs), simplifyNumeric(rhs)) match {
        case (IntConst(l), IntConst(r)) => BoolConst(l < r)
        case (Plus(pLhs, IntConst(-1)), rhs) => LessOrEq(pLhs, rhs)
        case (lhs, Plus(pLhs, IntConst(1))) => LessOrEq(lhs, pLhs)
        case (lhs, rhs) => LessThan(lhs, rhs)
      }
    case formula => formula
  }

  def simplifyNumeric(formula: Formula): Formula = eval(formula).getOrElse {
    var summaryOpt = Option.empty[Formula]

    def addToSummary(f: Formula): Unit = {
      summaryOpt = Some(summaryOpt match {
        case Some(summary) => Plus(summary, f)
        case None => f
      })
    }

    var cstOpt = Option.empty[Int]

    def simplifyAndAddToSummary(f: Formula, coef: Int): Unit = f match {
      case IntConst(0) => ()
      case IntConst(1) =>
        assert(cstOpt.isEmpty)
        cstOpt = Some(coef)
      case _ if coef == 0 => ()
      case _ if coef == 1 =>
        addToSummary(f)
      case _ if coef == -1 =>
        addToSummary(Neg(f))
      case DivBy(lhs, IntConst(rhsVal)) if coef % rhsVal == 0 =>
        simplifyAndAddToSummary(lhs, coef / rhsVal)
      case _ =>
        addToSummary(Times(IntConst(coef), f))
    }

    for ((f, coef) <- linearize(formula)) {
      simplifyAndAddToSummary(f, coef)
    }
    cstOpt.foreach { cst =>
      if (cst != 0 || summaryOpt.isEmpty) {
        addToSummary(IntConst(cst))
      }
    }
    summaryOpt.getOrElse(IntConst(0))
  }

  def mkSimplifiedConjunct(terms: List[Formula]): Formula =
    simplifyBool(terms.foldLeft[Formula](BoolConst(true))(LogicalAnd(_, _)))

  def eval(formula: Formula): Option[ConstFormula] = formula match {
    case value: IdValue => None
    case formula: ConstFormula => Some(formula)
    case Select(owner, field) => None
    case FunCall(receiver, func, typeArgs, args) if func.getFunSigOpt.exists(isFunc(stringTypeId, sizeFunId, 0)) =>
      eval(receiver) match {
        case Some(StringConst(stringLit)) => Some(IntConst(stringLit.length))
        case _ => None
      }
    case FunCall(receiver, func, typeArgs, args) => None
    case ClosureCall(callee, target, args) => None
    case PureClosureValue(params, body, closureVal) => None
    case Plus(lhs, rhs) => evalNumericBinop(lhs, rhs, _ + _, _ + _, rhsCanBeZero = true)
    case Neg(operand) =>
      eval(operand) match {
        case Some(IntConst(cst)) => Some(IntConst(-cst))
        // TODO Double
        case _ => None
      }
    case Times(lhs, rhs) => evalNumericBinop(lhs, rhs, _ * _, _ * _, rhsCanBeZero = true)
    case DivBy(lhs, rhs) => evalNumericBinop(lhs, rhs, _ / _, _ / _, rhsCanBeZero = false)
    case Modulo(lhs, rhs) => evalNumericBinop(lhs, rhs, _ % _, _ % _, rhsCanBeZero = false)
    case LogicalAnd(lhs, rhs) => evalLogicalBinop(lhs, rhs, _ && _)
    case LogicalNot(operand) =>
      eval(operand) match {
        case Some(BoolConst(cst)) => Some(BoolConst(!cst))
        case _ => None
      }
    case LogicalOr(lhs, rhs) => evalLogicalBinop(lhs, rhs, _ || _)
    case Equality(lhs, rhs) => evalComparisonBinop[ConstFormula](lhs, rhs, _.value == _.value)
    case LessOrEq(lhs, rhs) => evalComparisonBinop[IntConst](lhs, rhs, _.value <= _.value)
    case LessThan(lhs, rhs) => evalComparisonBinop[IntConst](lhs, rhs, _.value < _.value)
    case TypePredicate(subject, tpe) => None
    case Phi(terms) if terms.size == 1 => eval(terms.head)
    case Phi(terms) => None
    case WrappedScope(resVal, scope) => eval(resVal)
  }

  def linearize(formula: Formula): Map[Formula, Int] = formula match {
    case value: IdValue => Map(value -> 1)
    case IntConst(cst) => Map(IntConst(1) -> cst)
    case formula: ConstFormula => Map(formula -> 1)
    case Select(owner, field) => Map(formula -> 1)
    case FunCall(receiver, func, typeArgs, args) => Map(formula -> 1)
    case ClosureCall(callee, closureTypingTarget, args) => Map(formula -> 1)
    case PureClosureValue(params, body, closureVal) => Map(formula -> 1)
    case Plus(lhs, rhs) =>
      val lLin = linearize(lhs)
      val rLin = linearize(rhs)
      Map.from(for (f <- lLin.keys ++ rLin.keys) yield {
        val coef = lLin.getOrElse(f, 0) + rLin.getOrElse(f, 0)
        f -> coef
      })
    case Neg(operand) =>
      for ((f, coef) <- linearize(operand)) yield (f, -coef)
    case formula: Times => Map(linearizeTimes(formula))
    case DivBy(lhs, rhs) =>
      val sLhs = simplifyNumeric(lhs)
      val sRhs = simplifyNumeric(rhs)
      (sLhs, sRhs) match {
        case (sLhs: Times, IntConst(rc)) =>
          val (resF, resCoef) = linearizeTimes(sLhs)
          Map(resF -> resCoef / rc)
        case _ =>
          Map(formula -> 1)
      }
    case Modulo(lhs, rhs) => Map(formula -> 1)
    case Equality(lhs, rhs) => Map.empty
    case LessOrEq(lhs, rhs) => Map.empty
    case LessThan(lhs, rhs) => Map.empty
    case LogicalNot(operand) => Map.empty
    case LogicalAnd(lhs, rhs) => Map.empty
    case LogicalOr(lhs, rhs) => Map.empty
    case TypePredicate(subject, tpe) => Map.empty
    case Phi(terms) if terms.size == 1 => linearize(terms.head)
    case Phi(terms) => Map.empty
    case WrappedScope(resVal, scope) => linearize(resVal)
  }

  private def linearizeTimes(times: Times): (Formula, Int) = {
    val Times(lhs, rhs) = times

    val sLhs = simplifyNumeric(lhs)
    val sRhs = simplifyNumeric(rhs)

    def computeTerm(sLhs: Formula, sRhs: Formula): Option[(Formula, Int)] = (sLhs, sRhs) match {
      case (IntConst(lc), IntConst(rc)) =>
        Some(IntConst(lc * rc) -> 1)
      case (IntConst(lc), sRhs: Times) =>
        val (resF, resCoef) = linearizeTimes(sRhs)
        Some(resF, lc * resCoef)
      case (IntConst(lc), sRhs) =>
        Some(sRhs -> lc)
      case (sLhs, sRhs: IntConst) =>
        computeTerm(sRhs, sLhs)
      case _ =>
        None
    }

    computeTerm(sLhs, sRhs).getOrElse(Times(sLhs, sRhs) -> 1)
  }

  private def evalNumericBinop(lhs: Formula, rhs: Formula, intBinop: (Int, Int) => Int, doubleBinop: (Double, Double) => Double, rhsCanBeZero: Boolean): Option[IntConst] =
    (eval(lhs), eval(rhs)) match {
      case (_, Some(IntConst(0) /* TODO | DoubleConst(0) */)) if !rhsCanBeZero => None
      case (Some(IntConst(lc)), Some(IntConst(rc))) => Some(IntConst(intBinop(lc, rc)))
      // TODO Double
      case _ => None
    }

  private def evalLogicalBinop(lhs: Formula, rhs: Formula, logicalBinop: (Boolean, Boolean) => Boolean): Option[BoolConst] =
    (eval(lhs), eval(rhs)) match {
      case (Some(BoolConst(lc)), Some(BoolConst(rc))) => Some(BoolConst(logicalBinop(lc, rc)))
      case _ => None
    }

  private def evalComparisonBinop[C <: ConstFormula : ClassTag](lhs: Formula, rhs: Formula, comparisonBinop: (C, C) => Boolean): Option[BoolConst] =
    (eval(lhs), eval(rhs)) match {
      case (Some(l: C), Some(r: C)) => Some(BoolConst(comparisonBinop(l, r)))
      case _ => None
    }

}
