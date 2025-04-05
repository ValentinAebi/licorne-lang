package compiler.lowerer

import compiler.irs.Asts.Literal
import identifiers.FunOrVarId

final case class LoweringContext(constants: Map[FunOrVarId, Literal]) extends AnyVal {
  
  def literalFor(constId: FunOrVarId): Literal = constants.apply(constId).freshCopyWithoutPos
  
}
