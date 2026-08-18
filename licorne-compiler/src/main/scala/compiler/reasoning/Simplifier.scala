package compiler.reasoning

import compiler.irs.ssa.Formulas.*
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{AnyType, IntType, NothingType, NullType}
import compiler.reasoning.Solver
import compiler.typing.contexts.{DealiasingContext, SubtypingContext, TypeParamsContext}
import compiler.util.{SeqSet, asIterableOfType}
import compiler.valuesconversion.GlobalValuesContext

import scala.reflect.ClassTag

// TODO caching?
// TODO check edge cases in simplification of unions and intersections (e.g. all types are Null/Nothing/Any)
// TODO some code in simplification of unions and intersections seems very similar to the code of the join and meet computations, maybe this can be improved
final class Simplifier(subtypingCtx: SubtypingContext, solver: Solver, dealiasingCtx: DealiasingContext, meetJoinComputer: MeetJoinComputer, globalValuesContext: GlobalValuesContext) {

  private given GlobalValuesContext = globalValuesContext

  import globalValuesContext.nullVal
  import globalValuesContext.itValue

  def simplify(tpe: Type)(using TypeParamsContext): Type = tpe.withTypeVarsExpanded match {
    case primitiveType: PrimitiveType => primitiveType
    case NamedType(typeName, typeArgs, args) =>
      NamedType(typeName, typeArgs.map(simplify), args)
    case ClosureType(params, result, enforcedPure) => ClosureType(params.map(simplify), simplify(result), enforcedPure)
    case variable: TypeVariable => variable

    case UnionType(originalTypes) =>
      val simplifiedTypes = SeqSet(originalTypes).map(simplify(_).flattenedPredIfGenRefined).filter(_ != NothingType)
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
          case 1 => filteredTypes.head
          case _ => filteredTypes.asIterableOfType[IntRangeType] match {
            case Some(filteredTypes) =>
              meetJoinComputer.computeJoinOfRanges(filteredTypes)
            case None => UnionType(filteredTypes)
          }
        }
        if nullableFlag
        then NullableType(nonNullType)
        else nonNullType
      }

    case IntersectionType(originalTypes) =>
      val simplifiedTypes = SeqSet(originalTypes).map(simplify(_).flattenedPredIfGenRefined).filter(_ != AnyType)

      var nullableFlag = true
      var knownNullFlag = false

      val nonNullableDealiasedTypes = simplifiedTypes.flatMap { rawType =>
        dealiasingCtx.dealiasType(rawType) match {
          case NullableType(nullatedType) => Some(nullatedType)
          case NullType =>
            knownNullFlag = true
            None
          case tpe =>
            nullableFlag = false
            Some(tpe)
        }
      }

      if (nonNullableDealiasedTypes.contains(NothingType) || knownNullFlag && !nullableFlag) {
        return NothingType
      } else if (knownNullFlag) {
        return NullType
      }

      val filteredTypes =
        nonNullableDealiasedTypes.filter { tpe =>
          !nonNullableDealiasedTypes.exists { otherType =>
            subtypingCtx.isSubtype(otherType, tpe) && !subtypingCtx.isSubtype(tpe, otherType)
          }
        }
      // TODO if datatypes/structs, maybe compute intersection (?)
      val nonNullType = filteredTypes.size match {
        case 0 => AnyType
        case 1 => filteredTypes.head
        case _ => filteredTypes.asIterableOfType[IntRangeType] match {
          case Some(filteredTypes) =>
            meetJoinComputer.computeMeetOfRanges(filteredTypes)
          case None => filteredTypes.asIterableOfType[RefinedType] match {
            case Some(filteredTypes) =>
              val baseType = meetJoinComputer.computeMeet(filteredTypes.map(_.baseType))
              val pred = filteredTypes.map(_.predicate).reduce(LogicalAnd(_, _))
              RefinedType(baseType, pred)
            case None => IntersectionType(filteredTypes)
          }
        }
      }
      if nullableFlag
      then NullableType(nonNullType)
      else nonNullType

    case refinedType: RefinedType =>
      val RefinedType(base1, pred1) = refinedType.flattenedRefinement

      // Step 1: T with it is S  --->  S  (if S <: T)
      val (targetTypes, pred2Parts) = searchTypeTests(pred1, base1)
      val base2 = if targetTypes.isEmpty then base1 else meetJoinComputer.computeMeet(targetTypes)
      val pred2 = mkSimplifiedConjunct(pred2Parts)

      // Step 2: T? with it != null  --->  T
      val (containsNonNullCheck, pred3Parts) = searchNonNullCheck(pred2)
      val base3 = if containsNonNullCheck then base2.ignoreNullabilityShallow else base2
      val pred3 = mkSimplifiedConjunct(pred3Parts)

      // Step 3: Int with it >= 0  --->  [0,]
      val RefinedType(b, p) = base3.asRefinedType
      val (base4, pred4) = b.withTypeVarsExpanded match {
        case IntType =>
          val (lowerBounds, upperBounds, pred4PartsBeforeReadd) = searchBounds(pred3)
          val lbOpt = solver.intMax(lowerBounds)
          val ubOpt = solver.intMin(upperBounds)
          val pred4PartsAfterReadd =
            (if lbOpt.isEmpty then lowerBounds.map(LessOrEq(_, itValue)) else List.empty) ++
              (if ubOpt.isEmpty then upperBounds.map(LessOrEq(itValue, _)) else List.empty) ++
              pred4PartsBeforeReadd
          (if lbOpt.isEmpty && ubOpt.isEmpty then IntType else IntRangeType(lbOpt, ubOpt),
            mkSimplifiedConjunct(pred4PartsAfterReadd))
        case _ => (base3, pred3)
      }

      // remove useless predicate
      val rawRefRes = if pred4 == BoolConst(true) then base4 else RefinedType(base4, pred4)

      // remove duplicate predicates
      rawRefRes match {
        case rawRefRes: RefinedType =>
          RefinedType(rawRefRes.baseType, rawRefRes.predicateAsSetOfConjuncts.reduceLeft(LogicalAnd(_, _)))
        case rawRefRes => rawRefRes
      }

    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      (lowerBoundOpt.map(simplifyInt), upperBoundOpt.map(simplifyInt)) match {
        case (None, None) => IntType
        case (Some(lb), Some(ub)) if solver.canProveLt(ub, lb) => NothingType
        case (lb, ub) => IntRangeType(lb, ub)
      }
    // FIXME improve simplification of nullable types
    case NullableType(nullatedType) if subtypingCtx.isSubtype(NullType, nullatedType) =>
      simplify(nullatedType)
    case NullableType(nullatedType) =>
      NullableType(simplify(nullatedType))
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
      (simplifyInt(lhs), simplifyInt(rhs)) match {
        case (IntConst(l), IntConst(r)) => BoolConst(l <= r)
        case (lhs, rhs) => LessOrEq(lhs, rhs)
      }
    case LessThan(lhs, rhs) =>
      (simplifyInt(lhs), simplifyInt(rhs)) match {
        case (IntConst(l), IntConst(r)) => BoolConst(l < r)
        case (lhs, rhs) => LessThan(lhs, rhs)
      }
    case formula => formula
  }

  def simplifyInt(formula: Formula): Formula = eval(formula).getOrElse {
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

  /**
   * @return (lowerBounds, upperBounds, otherConditions)
   */
  private def searchBounds(formula: Formula): (List[Formula], List[Formula], List[Formula]) = {
    import compiler.irs.ssa.FormulasDsl.*
    formula match {
      case LogicalAnd(lhs, rhs) =>
        val (llb, lrb, lo) = searchBounds(lhs)
        val (rlb, rrb, ro) = searchBounds(rhs)
        (llb ++ rlb, lrb ++ rrb, lo ++ ro)
      case LessOrEq(lb, `itValue`) => (List(lb), List.empty, List.empty)
      case LessThan(lb, `itValue`) => (List(lb + 1), List.empty, List.empty)
      case LessOrEq(`itValue`, ub) => (List.empty, List(ub), List.empty)
      case LessThan(`itValue`, ub) => (List.empty, List(ub - 1), List.empty)
      case formula => (List.empty, List.empty, List(formula))
    }
  }

  /**
   * @return (containsNonNullCheck, formulaWithoutNonNullCheck)
   */
  private def searchNonNullCheck(formula: Formula): (Boolean, List[Formula]) = formula match {
    case LogicalAnd(lhs, rhs) =>
      val (leftContainsNonNullCheck, leftWithoutNonNullCheck) = searchNonNullCheck(lhs)
      val (rightContainsNonNullCheck, rightWithoutNonNullCheck) = searchNonNullCheck(rhs)
      (leftContainsNonNullCheck || rightContainsNonNullCheck, leftWithoutNonNullCheck ++ rightWithoutNonNullCheck)
    case LogicalNot(Equality(`itValue`, `nullVal`) | Equality(`nullVal`, `itValue`)) =>
      (true, List.empty)
    case formula => (false, List(formula))
  }

  private def searchTypeTests(formula: Formula, baseType: Type): (List[Type], List[Formula]) = formula match {
    case LogicalAnd(lhs, rhs) =>
      val (lTids, lRem) = searchTypeTests(lhs, baseType)
      val (rTids, rRem) = searchTypeTests(rhs, baseType)
      (lTids ++ rTids, lRem ++ rRem)
    case TypePredicate(`itValue`, tpe) =>
      subtypingCtx.checkDowncastTarget(baseType, tpe).asOption match {
        case Some(targetType) => (List(targetType), List.empty)
        case None => (List.empty, List(formula))
      }
    case formula => (List.empty, List(formula))
  }

  private def mkSimplifiedConjunct(terms: List[Formula]): Formula =
    simplifyBool(terms.foldLeft[Formula](BoolConst(true))(LogicalAnd(_, _)))

  def eval(formula: Formula): Option[ConstFormula] = formula match {
    case value: IdValue => None
    case formula: ConstFormula => Some(formula)
    case Select(owner, field) => None
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
      val sLhs = simplifyInt(lhs)
      val sRhs = simplifyInt(rhs)
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
  }

  private def linearizeTimes(times: Times): (Formula, Int) = {
    val Times(lhs, rhs) = times

    val sLhs = simplifyInt(lhs)
    val sRhs = simplifyInt(rhs)

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

    computeTerm(sLhs, sRhs).getOrElse(times -> 1)
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
