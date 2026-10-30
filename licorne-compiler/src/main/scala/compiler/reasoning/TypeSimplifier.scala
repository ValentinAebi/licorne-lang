package compiler.reasoning

import compiler.irs.ircorne.Formulas.*
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{AnyType, IntType, NothingType, NullType}
import compiler.reasoning.FormulasSimplification.*
import compiler.reasoning.Solver
import compiler.stdlib.StdLib
import compiler.stdlib.StdLib.*
import compiler.typing.contexts.{DealiasingContext, SubtypingContext, TypeParamsContext}
import compiler.util.{SeqSet, asIterableOfType, findUnique}
import compiler.valuesconversion.GlobalValuesContext

import scala.reflect.ClassTag

// TODO caching?
// TODO check edge cases in simplification of unions and intersections (e.g. all types are Null/Nothing/Any)
// TODO some code in simplification of unions and intersections seems very similar to the code of the join and meet computations, maybe this can be improved
final class TypeSimplifier(subtypingCtx: SubtypingContext, solver: Solver, dealiasingCtx: DealiasingContext, meetJoinComputer: MeetJoinComputer, globalValuesContext: GlobalValuesContext) {

  private given GlobalValuesContext = globalValuesContext
  
  private given MeetJoinComputer = meetJoinComputer

  import globalValuesContext.{itValue, nullVal}

  def simplifyType(tpe: Type)(using TypeParamsContext): Type = tpe.withTypeVarsExpanded match {
    case primitiveType: PrimitiveType => primitiveType
    case NamedType(typeName, typeArgs, args) =>
      NamedType(typeName, typeArgs.map(simplifyType), args.map(simplifyFormula))
    case ClosureType(params, result, enforcedPure) => ClosureType(params.map(simplifyType), simplifyType(result), enforcedPure)
    case variable: TypeVariable => variable

    case UnionType(originalTypes) =>
      val simplifiedTypes = SeqSet(originalTypes).map(simplifyType(_).flattenedPredIfGenRefined).filter(_ != NothingType)
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
      val simplifiedTypes = SeqSet(originalTypes).map(simplifyType(_).flattenedPredIfGenRefined).filter(_ != AnyType)

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

    case TernaryType(cond, left, right) if subtypingCtx.canProveEquivalence(left, right) =>
      simplifyType(left)

    case TernaryType(cond, left, right) =>
      val simplifiedLeft = simplifyType(left)
      val simplifiedRight = simplifyType(right)
      val nonDegenerate = solver.checkSat()
      if nonDegenerate && solver.canProve(cond) then simplifiedLeft
      else if nonDegenerate && solver.canDisprove(cond) then simplifiedRight
      else TernaryType(cond, simplifiedLeft, simplifiedRight)

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
      val RefinedType(b, _) = base3.asRefinedType
      val (base4, pred4) = b.withTypeVarsExpanded match {
        case IntType =>
          val (lowerBounds, upperBounds, pred4PartsBeforeReadd) = searchBounds(pred3)
          val lbOpt = if solver.checkSat() then solver.intMax(lowerBounds) else lowerBounds.findUnique(_ => true)
          val ubOpt = if solver.checkSat() then solver.intMin(upperBounds) else upperBounds.findUnique(_ => true)
          val pred4PartsAfterReadd =
            (if lbOpt.isEmpty then lowerBounds.map(LessOrEq(_, itValue)) else List.empty) ++
              (if ubOpt.isEmpty then upperBounds.map(LessOrEq(itValue, _)) else List.empty) ++
              pred4PartsBeforeReadd
          (if lbOpt.isEmpty && ubOpt.isEmpty then IntType else IntRangeType(lbOpt, ubOpt),
            mkSimplifiedConjunct(pred4PartsAfterReadd))
        case StdLib.stringType => pred3 match {
          // String with it.size() == sz  ---> StringL(sz)
          case Equality(FunCall(globalValuesContext.itValue, invkTarget, Nil, Nil), sizeFormula) if invkTarget.getFunSigOpt.exists(isFunc(stringTypeId, sizeFunId, 0)) =>
            (NamedType(stringLTypeId, List.empty, List(sizeFormula)), BoolConst(true))
          case _ => (base3, pred3)
        }
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
      (lowerBoundOpt.map(simplifyNumeric), upperBoundOpt.map(simplifyNumeric)) match {
        case (None, None) => IntType
        case (Some(lb), Some(ub)) if solver.checkSat() && solver.canProveLt(ub, lb) => NothingType
        case (lb, ub) => IntRangeType(lb, ub)
      }
    // FIXME improve simplification of nullable types
    case NullableType(nullatedType) if subtypingCtx.isSubtype(NullType, nullatedType) =>
      simplifyType(nullatedType)
    case NullableType(nullatedType) =>
      NullableType(simplifyType(nullatedType))
  }

  /**
   * @return (lowerBounds, upperBounds, otherConditions)
   */
  private def searchBounds(formula: Formula): (List[Formula], List[Formula], List[Formula]) = {
    import compiler.irs.ircorne.FormulasDsl.*
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

  private def searchTypeTests(formula: Formula, baseType: Type)(using TypeParamsContext): (List[Type], List[Formula]) = formula match {
    case LogicalAnd(lhs, rhs) =>
      val (lTids, lRem) = searchTypeTests(lhs, baseType)
      val (rTids, rRem) = searchTypeTests(rhs, baseType)
      (lTids ++ rTids, lRem ++ rRem)
    case TypePredicate(`itValue`, tpe) =>
      subtypingCtx.checkDowncastTarget(baseType, tpe, acceptTypeParamTarget = false).asOption match {
        case Some(targetType) => (List(targetType), List.empty)
        case None => (List.empty, List(formula))
      }
    case formula => (List.empty, List(formula))
  }

}
