package compiler.smt

import compiler.irs.ssa.Formulas.{BoolConst, ClosureCall, DivBy, Equality, Formula, FunCall, IdValue, IntConst, LessOrEq, LessThan, LogicalAnd, LogicalNot, LogicalOr, Modulo, Neg, Plus, PureClosureValue, Select, StringConst, Times, TypePredicate}
import compiler.valproxies.ProxyStore
import io.ksmt.KContext
import io.ksmt.expr.KExpr
import io.ksmt.sort.{KBoolSort, KBv32Sort, KIntSort, KSort}

trait IntHandlingMode[IntSort <: KSort] {
  
  def iSort(using KContext): IntSort
  
  def const(i: Int)(using KContext): KExpr[IntSort]
  
  def plus(l: KExpr[IntSort], r: KExpr[IntSort])(using KContext): KExpr[IntSort]
  def neg(operand: KExpr[IntSort])(using KContext): KExpr[IntSort]
  def times(l: KExpr[IntSort], r: KExpr[IntSort])(using KContext): KExpr[IntSort]
  def div(l: KExpr[IntSort], r: KExpr[IntSort])(using KContext): KExpr[IntSort]
  def modulo(l: KExpr[IntSort], r: KExpr[IntSort])(using KContext): KExpr[IntSort]
  
  def leq(l: KExpr[IntSort], r: KExpr[IntSort])(using KContext): KExpr[KBoolSort]
  def lt(l: KExpr[IntSort], r: KExpr[IntSort])(using KContext): KExpr[KBoolSort]
  
}

object ArithIntMode extends IntHandlingMode[KIntSort] {

  override def iSort(using kCtx: KContext): KIntSort = kCtx.mkIntSort()

  override def const(i: Int)(using kCtx: KContext): KExpr[KIntSort] = kCtx.mkIntNum(i)

  override def plus(l: KExpr[KIntSort], r: KExpr[KIntSort])(using kCtx: KContext): KExpr[KIntSort] = kCtx.mkArithAdd(l, r)

  override def neg(operand: KExpr[KIntSort])(using kCtx: KContext): KExpr[KIntSort] = kCtx.mkArithUnaryMinus(operand)

  override def times(l: KExpr[KIntSort], r: KExpr[KIntSort])(using kCtx: KContext): KExpr[KIntSort] = kCtx.mkArithMul(l, r)

  override def div(l: KExpr[KIntSort], r: KExpr[KIntSort])(using kCtx: KContext): KExpr[KIntSort] = kCtx.mkArithDiv(l, r)

  override def modulo(l: KExpr[KIntSort], r: KExpr[KIntSort])(using kCtx: KContext): KExpr[KIntSort] =
    kCtx.mkIte(kCtx.le(kCtx.mkIntNum(0), l), kCtx.mkIntMod(l, r), kCtx.unaryMinus(kCtx.mkIntMod(kCtx.unaryMinus(l), r)))

  override def leq(l: KExpr[KIntSort], r: KExpr[KIntSort])(using kCtx: KContext): KExpr[KBoolSort] = kCtx.mkArithLe(l, r)

  override def lt(l: KExpr[KIntSort], r: KExpr[KIntSort])(using kCtx: KContext): KExpr[KBoolSort] = kCtx.mkArithLt(l, r)
  
}

object BvInt32Mode extends IntHandlingMode[KBv32Sort] {

  override def iSort(using kCtx: KContext): KBv32Sort = kCtx.mkBv32Sort()

  override def const(i: Int)(using kCtx: KContext): KExpr[KBv32Sort] = kCtx.mkBv(i)

  override def plus(l: KExpr[KBv32Sort], r: KExpr[KBv32Sort])(using kCtx: KContext): KExpr[KBv32Sort] = kCtx.mkBvAddExpr(l, r)

  override def neg(operand: KExpr[KBv32Sort])(using kCtx: KContext): KExpr[KBv32Sort] = kCtx.mkBvNegationExpr(operand)

  override def times(l: KExpr[KBv32Sort], r: KExpr[KBv32Sort])(using kCtx: KContext): KExpr[KBv32Sort] = kCtx.mkBvMulExpr(l, r)

  override def div(l: KExpr[KBv32Sort], r: KExpr[KBv32Sort])(using kCtx: KContext): KExpr[KBv32Sort] = kCtx.mkBvSignedDivExpr(l, r)

  override def modulo(l: KExpr[KBv32Sort], r: KExpr[KBv32Sort])(using kCtx: KContext): KExpr[KBv32Sort] = kCtx.mkBvSignedRemExpr(l, r)

  override def leq(l: KExpr[KBv32Sort], r: KExpr[KBv32Sort])(using kCtx: KContext): KExpr[KBoolSort] = kCtx.mkBvSignedLessOrEqualExpr(l, r)

  override def lt(l: KExpr[KBv32Sort], r: KExpr[KBv32Sort])(using kCtx: KContext): KExpr[KBoolSort] = kCtx.mkBvSignedLessExpr(l, r)
  
}
