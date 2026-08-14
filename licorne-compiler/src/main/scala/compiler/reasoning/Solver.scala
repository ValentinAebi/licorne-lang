package compiler.reasoning

import compiler.irs.ssa.Formulas.Formula
import compiler.lang.Types.{IntRangeType, Type}
import compiler.typing.contexts.DealiasingContext
import compiler.valuesconversion.GlobalValuesContext
import io.ksmt.solver.KSolverStatus
import io.ksmt.sort.KSort

trait Solver {

  def acceptingPhisForInts[T](action: => T): T

  def check(): KSolverStatus
  
  def checkSat(): Boolean
  
  def checkUnsat(): Boolean
  
  def canProve(formula: Formula): Boolean
  
  def canProveImplication(premise: Formula, conseq: Formula): Boolean
  
  def canProveLeq(lhs: Formula, rhs: Formula): Boolean
  
  def canProveLt(lhs: Formula, rhs: Formula): Boolean
  
  def canProveGeZero(f: Option[Formula]): Boolean
  
  def canProveGtZero(f: Option[Formula]): Boolean
  
  def canProveLeZero(f: Option[Formula]): Boolean
  
  def canProveLtZero(f: Option[Formula]): Boolean
  
  def canProveNotZero(f: Formula): Boolean
  
  def onNewFrame[T](action: => T): T
  
  def intMin(l: Formula, r: Formula): Option[Formula]
  
  def intMin(formulas: Iterable[Formula]): Option[Formula]

  def discardNonMins(formulas: Iterable[Formula]): Iterable[Formula]
  
  def intMax(l: Formula, r: Formula): Option[Formula]
  
  def intMax(formulas: Iterable[Formula]): Option[Formula]

  def discardNonMax(formulas: Iterable[Formula]): Iterable[Formula]

  def assert(formula: Formula): Unit

  def assert(formulas: Iterable[Formula]): Unit

  def assertEq[S <: KSort](lhs: Formula, rhs: Formula, simplifiedType: SimplifiedType[S]): Unit

  def assertLeq(lhs: Formula, rhs: Formula): Unit

  def assertLt(lhs: Formula, rhs: Formula): Unit

  def assertInRange(formula: Formula, range: IntRangeType): Unit
  
  def takeType(subject: Formula, tpe: Type)(using DealiasingContext, GlobalValuesContext): Unit

  def canProveIsOutsideRange(formula: Formula, range: IntRangeType): Boolean

}
