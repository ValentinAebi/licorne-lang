package compiler.solver

import compiler.datastructures.Graph
import lang.Formulas.{Formula, LessOrEq}
import lang.Types.IntRangeType
import lang.Types.IntRangeType.Bound

final class SMTBasedSolver extends Solver {

  def assert(formula: Formula): Unit = ???

  def canProve(formula: Formula): Boolean = ???

  def isSatisfiable(formula: Formula): Boolean = ???
  
}
