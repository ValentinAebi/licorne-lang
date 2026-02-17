package compiler.typing

import compiler.lang.Formulas.SelectedField.{ResolvedField, UnresolvedField}
import compiler.lang.Formulas.*

object PurityChecking {

  def isPure(typedFormula: Formula): Boolean = typedFormula match {
    case value: Value => true
    case binOp: BinOp => isPure(binOp.lhs) && isPure(binOp.rhs)
    case unaryOp: UnaryOp => isPure(unaryOp.operand)
    // TODO see if we can do something if the call target is resolved
    case Call(receiver, callTarget, typeArgs, args) => false
    case ClosureInvocation(closure, args) => false
    case Select(owner, ResolvedField(ownerSig, field)) =>
      isPure(owner) && field.isStable
    case Select(owner, UnresolvedField(fieldId)) => false
    case HasType(formula, tpe) => isPure(formula)
    case typed: TypedFormula => isPure(typed.formula)
  }
  
}
