package compiler.smt

import compiler.lang.Formulas.*
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{AnyType, IntType, NothingType}
import compiler.smt.Solver
import compiler.typing.contexts.SubtypingContext

import scala.reflect.ClassTag

// TODO caching?
final class Simplifier(subtypingCtx: SubtypingContext, solver: Solver) {

  def simplify(tpe: Type): Type = tpe match {
    case nominalType: NominalType => nominalType
    case ClosureType(params, result) => ClosureType(params.map(simplify), simplify(result))
    case variable: TypeVariable => variable
    case UnionType(types) =>
      val simplifiedTypes = types.map(simplify)
      val filteredTypes = simplifiedTypes.filter(tpe => !simplifiedTypes.exists(otherType => subtypingCtx.isSubtype(tpe, otherType)))
      filteredTypes.size match {
        case 0 => NothingType
        case 1 => simplifiedTypes.head
        case _ => UnionType(simplifiedTypes)
      }
    case IntersectionType(originalTypes) =>
      val simplifiedTypes = originalTypes.map(simplify).filter(_ != AnyType)
      val filteredTypes = simplifiedTypes.filter(tpe => !simplifiedTypes.exists(otherType => otherType != tpe && subtypingCtx.isSubtype(otherType, tpe)))
      filteredTypes.size match {
        case 0 => AnyType
        case 1 => filteredTypes.head
        case _ => IntersectionType(filteredTypes)
      }
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      (lowerBoundOpt.map(simplify), upperBoundOpt.map(simplify)) match {
        case (None, None) => IntType
        case (Some(lb), Some(ub)) if solver.canProveLt(ub, lb) => NothingType
        case (lb, ub) => IntRangeType(lb, ub)
      }
  }

  def simplify(formula: Formula): Formula = eval(formula).getOrElse {
    var summaryOpt = Option.empty[Formula]

    def addToSummary(f: Formula): Unit = {
      summaryOpt = Some(summaryOpt match {
        case Some(summary) => Plus(summary, f)
        case None => f
      })
    }

    var cstOpt = Option.empty[Int]
    for ((f, coef) <- linearize(formula)) {
      f match {
        case IntConst(0) => ()
        case IntConst(1) =>
          assert(cstOpt.isEmpty)
          cstOpt = Some(coef)
        case _ if coef == 0 => ()
        case _ if coef == 1 =>
          addToSummary(f)
        case _ if coef == -1 =>
          addToSummary(Neg(f))
        case _ =>
          addToSummary(Times(IntConst(coef), f))
      }
    }
    cstOpt.foreach { cst =>
      if (cst != 0 || summaryOpt.isEmpty) {
        addToSummary(IntConst(cst))
      }
    }
    summaryOpt.getOrElse(IntConst(0))
  }

  def eval(formula: Formula): Option[ConstFormula] = formula match {
    case value: IdValue => None
    case formula: ConstFormula => Some(formula)
    case Select(owner, field) => None
    case Call(receiver, func, typeArgs, args) => None
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

  private def linearize(formula: Formula): Map[Formula, Int] = formula match {
    case value: IdValue => Map(value -> 1)
    case IntConst(cst) => Map(IntConst(1) -> cst)
    case formula: ConstFormula => Map(formula -> 1)
    case Select(owner, field) => Map(formula -> 1)
    case Call(receiver, func, typeArgs, args) => Map(formula -> 1)
    case Plus(lhs, rhs) =>
      val lLin = linearize(lhs)
      val rLin = linearize(rhs)
      Map.from(for (f <- lLin.keys ++ rLin.keys) yield {
        val coef = lLin.getOrElse(f, 0) + rLin.getOrElse(f, 0)
        f -> coef
      })
    case Neg(operand) =>
      for ((f, coef) <- linearize(operand)) yield (f, -coef)
    case Times(lhs, rhs) =>
      val sLhs = simplify(lhs)
      val sRhs = simplify(rhs)
      (sLhs, sRhs) match {
        case (IntConst(lc), IntConst(rc)) =>
          Map(IntConst(lc * rc) -> 1)
        case (IntConst(lc), sRhs) =>
          Map(sRhs -> lc)
        case (sLhs, IntConst(rc)) =>
          Map(sLhs -> rc)
        case _ =>
          Map(formula -> 1)
      }
    case DivBy(lhs, rhs) => Map(formula -> 1)
    case Modulo(lhs, rhs) => Map(formula -> 1)
    case Equality(lhs, rhs) => Map.empty
    case LessOrEq(lhs, rhs) => Map.empty
    case LessThan(lhs, rhs) => Map.empty
    case LogicalNot(operand) => Map.empty
    case LogicalAnd(lhs, rhs) => Map.empty
    case LogicalOr(lhs, rhs) => Map.empty
    case TypePredicate(subject, tpe) => Map.empty
  }

}
