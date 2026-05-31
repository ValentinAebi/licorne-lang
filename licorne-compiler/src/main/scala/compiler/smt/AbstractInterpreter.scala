package compiler.smt

import compiler.irs.ssa.Formulas
import compiler.irs.ssa.Formulas.*
import compiler.lang.Types
import compiler.lang.Types.PrimitiveType.{DoubleType, IntType}
import compiler.lang.Types.{IntRangeType, Type, asRefinedType}
import compiler.smt.AbstractInterpreter.someZero
import compiler.smt.{Simplifier, Solver}
import compiler.typing.contexts.{ResolutionContext, TypeParamsContext}
import compiler.valuesconversion.GlobalValuesContext

final class AbstractInterpreter(solver: Solver, simplifier: Simplifier, globalValsCtx: GlobalValuesContext) {

  //> @formatter:off
  private given Simplifier = simplifier
  private given GlobalValuesContext = globalValsCtx
  //> @formatter:on

  /**
   * {{{
   *   [a,b] + [c,d]  ==  [a+b,c+d]
   * }}}
   */
  def typePlusType(l: Type, r: Type): Option[Type] = typeArithBinopType(l, r) {
    case ((a, b), (c, d)) => (boundPlusBound(a, c), boundPlusBound(b, d))
  }

  /**
   * {{{
   *   [a,b] - [c,d]  ==  [a-d,b-c]
   * }}}
   */
  def typeMinusType(l: Type, r: Type): Option[Type] = typeArithBinopType(l, r) {
    case ((a, b), (c, d)) => (boundMinusBound(a, d), boundMinusBound(b, c))
  }

  /**
   * {{{
   * [a,b] * [c,d] defined by:
   *
   *  [a,b] → |   >= 0    ¦    ∋ 0    ¦    <= 0
   *  [c,d] ↓ |           ¦           ¦
   *  --------------------------------------------
   *   >= 0   | [a*c,b*d] ¦ [a*d,b*d] ¦ [a*d,b*c]
   *   ∋ 0    | [b*c,b*d] ¦    ***    ¦ [a*d,a*c]
   *   <= 0   | [b*c,a*d] ¦ [b*c,a*c] ¦ [b*d,a*c]
   *
   * where *** stands for [min{a*d,b*c},max{a*c,b*d}]
   * }}}
   */
  def typeTimesType(l: Type, r: Type): Option[Type] = typeArithBinopType(l, r) {
    case ((a, b), (c, d)) =>
      lazy val `[a,b] >= 0` = solver.canProveGeZero(a)
      lazy val `[a,b] <= 0` = solver.canProveLeZero(b)
      lazy val `[a,b] contains 0` = solver.canProveLeZero(a) && solver.canProveGeZero(b)
      lazy val `[c,d] >= 0` = solver.canProveGeZero(c)
      lazy val `[c,d] <= 0` = solver.canProveLeZero(d)
      lazy val `[c,d] contains 0` = solver.canProveLeZero(c) && solver.canProveGeZero(d)

      // @formatter:off
      def ac = boundTimesBound(a, c)
      def ad = boundTimesBound(a, d)
      def bc = boundTimesBound(b, c)
      def bd = boundTimesBound(b, d)
      // @formatter:on

      if `[a,b] >= 0` && `[c,d] >= 0` then (ac, bd)
      else if `[a,b] >= 0` && `[c,d] contains 0` then (bc, bd)
      else if `[a,b] >= 0` && `[c,d] <= 0` then (bc, ad)
      else if `[a,b] contains 0` && `[c,d] >= 0` then (ad, bd)
      else if `[a,b] contains 0` && `[c,d] contains 0` then {
        val lb = for {
          aTimesD <- ad
          bTimesC <- bc
        } yield solver.intMin(aTimesD, bTimesC)
        val ub = for {
          aTimesC <- ac
          bTimesD <- bd
        } yield solver.intMax(aTimesC, bTimesD)
        (lb.flatten, ub.flatten)
      } else if `[a,b] contains 0` && `[c,d] <= 0` then (bc, ac)
      else if `[a,b] <= 0` && `[c,d] >= 0` then (ad, bc)
      else if `[a,b] <= 0` && `[c,d] contains 0` then (ad, ac)
      else if `[a,b] <= 0` && `[c,d] <= 0` then (bd, ac)
      else (None, None)
  }

  /**
   * {{{
   *   [a,b] / [c,d] defined by:
   *    -  [a,b] >= 0, [c,d] > 0  -->  [a/d,b/c]
   *    -  [a,b] <= 0, [c,d] < 0  -->  [b/c,a/d]
   *    -  [a,b] >= 0, [c,d] < 0  -->  [b/d,a/c]
   *    -  [a,b] <= 0, [c,d] > 0  -->  [a/c,b/d]
   * }}}
   */
  def typeDivType(l: Type, r: Type): Option[Type] = typeArithBinopType(l, r) {
    case ((a, b), (c, d)) =>

      extension (f: Option[Formula]) def orZero: Option[Formula] = f.orElse(Some(IntConst(0)))

      lazy val `[a,b] >= 0` = solver.canProveGeZero(a)
      lazy val `[c,d] > 0` = solver.canProveGtZero(c)
      lazy val `[a,b] <= 0` = solver.canProveLeZero(b)
      lazy val `[c,d] < 0` = solver.canProveLtZero(d)

      def aDivC = boundDivBound(a, c)
      def aDivD = boundDivBound(a, d)
      def bDivC = boundDivBound(b, c)
      def bDivD = boundDivBound(b, d)

      if `[a,b] >= 0` && `[c,d] > 0` then (aDivD.orZero, bDivC)
      else if `[a,b] <= 0` && `[c,d] < 0` then (bDivC.orZero, aDivD)
      else if `[a,b] >= 0` && `[c,d] < 0` then (bDivD, aDivC.orZero)
      else if `[a,b] <= 0` && `[c,d] > 0` then (aDivC, bDivD.orZero)
      else (None, None)
  }

  /**
   * {{{
   *   [a,b] % r:[c,d] defined by:
   *    -  [a,b] >= 0, [c,d] > 0  -->  [0,d-1]
   *    -  [a,b] >= 0, [c,d] < 0  -->  [0,-c-1]
   *    -  [a,b] <= 0, [c,d] > 0  -->  [-d+1,0]
   *    -  [a,b] <= 0, [c,d] < 0  -->  [c+1,0]
   * }}}
   */
  def typeModuloType(rhsOpt: Option[Formula])(l: Type, r: Type): Option[Type] = typeArithBinopType(l, r) {
    case ((a, b), (c, d)) =>
      import compiler.irs.ssa.FormulasDsl.*

      lazy val `[a,b] >= 0` = solver.canProveGeZero(a)
      lazy val `[c,d] > 0` = solver.canProveGtZero(c)
      lazy val `[a,b] <= 0` = solver.canProveLeZero(b)
      lazy val `[c,d] < 0` = solver.canProveLtZero(d)

      if `[a,b] >= 0` && `[c,d] > 0` then (someZero, for r <- rhsOpt.orElse(d) yield r - 1)
      else if `[a,b] >= 0` && `[c,d] < 0` then (someZero, for r <- rhsOpt.orElse(c) yield -r - 1)
      else if `[a,b] <= 0` && `[c,d] > 0` then (for r <- rhsOpt.orElse(d) yield -r + 1, someZero)
      else if `[a,b] <= 0` && `[c,d] < 0` then (for r <- rhsOpt.orElse(c) yield r + 1, someZero)
      else (None, None)
  }

  def unaryNegType(operand: Type): Option[Type] = simplifier.simplify(operand) match {
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      val rawRange = IntRangeType(upperBoundOpt.map(Neg(_)), lowerBoundOpt.map(Neg(_)))
      Some(simplifier.simplify(rawRange))
    case operand =>
      operand.asRefinedType.baseType match {
        case IntType => Some(IntType)
        case DoubleType => Some(DoubleType)
        case _ => None
      }
  }

  def interpretUnderAssumptions(formula: Formula, typeAssumptions: Map[IdValue, Type], assignmentTargetOpt: Option[IdValue])
                               (using GlobalValuesContext, ResolutionContext, TypeParamsContext): Option[Type] = {

    def interpretBinop(lhs: Formula, rhs: Formula, interpretationFunc: (Type, Type) => Option[Type]) = for {
      l <- interpretUnderAssumptions(lhs)
      r <- interpretUnderAssumptions(rhs)
      tpe <- interpretationFunc(l, r)
    } yield tpe

    def interpretUnderAssumptions(formula: Formula): Option[Type] = formula match {
      case formula: Formula if assignmentTargetOpt.exists(_.typeCanMention(formula)) => Some(IntRangeType.singleton(formula))
      case constFormula: ConstFormula => Some(IntRangeType.singleton(constFormula))
      case idValue: IdValue => typeAssumptions.get(idValue).map { tpe =>
        tpe.filtered(assignmentTargetOpt, currScopeAndProxyStoreOpt = None)
      }
      case Plus(lhs, rhs) => interpretBinop(lhs, rhs, typePlusType)
      case Neg(operand) => interpretUnderAssumptions(operand).flatMap(unaryNegType)
      case Times(lhs, rhs) => interpretBinop(lhs, rhs, typeTimesType)
      case DivBy(lhs, rhs) => interpretBinop(lhs, rhs, typeDivType)
      case Modulo(lhs, rhs) => interpretBinop(lhs, rhs, typeModuloType(Some(rhs)))
      case _ => None
    }

    interpretUnderAssumptions(formula)
  }

  private def typeArithBinopType(l: Type, r: Type)
                                (mergeRanges: ((Option[Formula], Option[Formula]), (Option[Formula], Option[Formula])) => (Option[Formula], Option[Formula])): Option[Type] = (simplifier.simplify(l), simplifier.simplify(r)) match {
    case (IntRangeType(llb, lub), IntRangeType(rlb, rub)) =>
      val (lb, ub) = mergeRanges((llb, lub), (rlb, rub))
      Some(simplifier.simplify(IntRangeType(lb, ub)))
    case (l, r) =>
      (l.asRefinedType.baseType, r.asRefinedType.baseType) match {
        case (IntType | IntRangeType(_, _), IntType | IntRangeType(_, _)) => Some(IntType)
        case (DoubleType, DoubleType) => Some(DoubleType)
        case _ => None
      }
  }

  private def boundPlusBound(l: Option[Formula], r: Option[Formula]): Option[Formula] =
    for {
      lf <- l
      rf <- r
    } yield Plus(lf, rf)

  private def boundMinusBound(l: Option[Formula], r: Option[Formula]): Option[Formula] =
    for {
      lf <- l
      rf <- r
    } yield Plus(lf, Neg(rf))

  private def boundTimesBound(l: Option[Formula], r: Option[Formula]): Option[Formula] =
    for {
      lf <- l
      rf <- r
    } yield Times(lf, rf)

  private def boundDivBound(l: Option[Formula], r: Option[Formula]): Option[Formula] =
    for {
      lf <- l
      rf <- r
    } yield DivBy(lf, rf)

}

object AbstractInterpreter {

  private val someZero = Some(IntConst(0))

}
