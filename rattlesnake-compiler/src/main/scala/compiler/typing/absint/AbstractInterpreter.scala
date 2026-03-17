package compiler.typing.absint

import compiler.irs.SSA.Scope
import compiler.lang.Formulas.{Formula, Plus}
import compiler.lang.Types.{IntRangeType, Type}
import compiler.typing.UnionFind

final class AbstractInterpreter {
  
  def plus(l: Type, r: Type): Type = {
    ???
  }
  
  def plus(l: IntRangeType, r: IntRangeType, uf: UnionFind): IntRangeType = IntRangeType(
    operandOfBinop(l.lowerBoundOpt, r.lowerBoundOpt, Plus(_, _), uf),
    operandOfBinop(l.upperBoundOpt, r.upperBoundOpt, Plus(_, _), uf)
  )
  
  private def operandOfBinop(lhs: Option[Formula], rhs: Option[Formula], mkBinop: (Formula, Formula) => Formula, uf: UnionFind): Option[Formula] = {
    for {
      l <- lhs.flatMap(uf.filterFormula)
      r <- rhs.flatMap(uf.filterFormula)
    } yield mkBinop(l, r)
  }

}
