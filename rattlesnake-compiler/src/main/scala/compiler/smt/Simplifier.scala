package compiler.smt

import compiler.lang.Formulas.*
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{AnyType, IntType, NothingType, NullType}
import compiler.smt.Solver
import compiler.typing.contexts.{DealiasingContext, SubtypingContext}
import compiler.util.asIterableOfType

import scala.reflect.ClassTag

// TODO caching?
// TODO check edge cases in simplification of unions and intersections (e.g. all types are Null/Nothing/Any)
// TODO some code in simplification of unions and intersections seems very similar to the code of the join and meet computations, maybe this can be improved
final class Simplifier(subtypingCtx: SubtypingContext, solver: Solver, dealiasingCtx: DealiasingContext, meetJoinComputer: MeetJoinComputer) {

  def simplify(tpe: Type): Type = tpe match {
    case nominalType: NominalType => nominalType
    case ClosureType(params, result) => ClosureType(params.map(simplify), simplify(result))
    case variable: TypeVariable => variable
    case UnionType(types) =>
      val simplifiedTypes = types.map(simplify).filter(_ != NothingType)
      if simplifiedTypes.size == 1 then simplifiedTypes.head
      else {

        var nullableFlag = false

        val dealiasedNonNullTypes = simplifiedTypes.flatMap { rawType =>
          dealiasingCtx.dealiasType(rawType) match {
            case NullableType(nullatedType) =>
              nullableFlag = true
              Some(nullatedType)
            case NullType =>
              nullableFlag = true
              None
            case tpe => Some(tpe)
          }
        }
        val filteredTypes = dealiasedNonNullTypes.filter { tpe =>
          !dealiasedNonNullTypes.exists { otherType =>
            subtypingCtx.isSubtype(tpe, otherType) && !subtypingCtx.isSubtype(otherType, tpe)
          }
        }
        // TODO if datatypes/structs and union covers all cases of a supertype, return this supertype (?)
        val nonNullType = filteredTypes.size match {
          case 0 => NullType
          case 1 => simplifiedTypes.head
          case _ => filteredTypes.asIterableOfType[IntRangeType] match {
            case Some(filteredTypes) =>
              meetJoinComputer.computeJoinOfRanges(filteredTypes)
            case None => UnionType(simplifiedTypes)
          }
        }
        if nullableFlag
        then NullableType(nonNullType)
        else nonNullType
      }
    case IntersectionType(originalTypes) =>
      val simplifiedTypes = originalTypes.map(simplify).filter(_ != AnyType)

      var nullableFlag = true

      val nonNullableDealiasedTypes = simplifiedTypes.flatMap { rawType =>
        dealiasingCtx.dealiasType(rawType) match {
          case NullableType(nullatedType) => Some(nullatedType)
          case NullType => None
          case tpe =>
            nullableFlag = false
            Some(tpe)
        }
      }
      
      val filteredTypes =
        nonNullableDealiasedTypes.filter { tpe =>
          !nonNullableDealiasedTypes.exists { otherType =>
            subtypingCtx.isSubtype(otherType, tpe) && !subtypingCtx.isSubtype(tpe, otherType)
          }
        }
      // TODO if datatypes/structs, maybe compute intersection (?)
      // TODO might fallback to AnyType in cases where Null could be better, maybe look into a fix for this
      val nonNullType = filteredTypes.size match {
        case 0 => AnyType
        case 1 => filteredTypes.head
        case _ => filteredTypes.asIterableOfType[IntRangeType] match {
          case Some(filteredTypes) =>
            meetJoinComputer.computeMeetOfRanges(filteredTypes)
          case None => IntersectionType(filteredTypes)
        }
      }
      if nullableFlag
      then NullableType(nonNullType)
      else nonNullType
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      (lowerBoundOpt.map(simplify), upperBoundOpt.map(simplify)) match {
        case (None, None) => IntType
        case (Some(lb), Some(ub)) if solver.canProveLt(ub, lb) => NothingType
        case (lb, ub) => IntRangeType(lb, ub)
      }
    case NullableType(nullatedType@(AnyType | NothingType | NullType)) =>
      simplify(nullatedType)
    case NullableType(nullatedType) =>
      NullableType(simplify(nullatedType))
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

  def linearize(formula: Formula): Map[Formula, Int] = formula match {
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
