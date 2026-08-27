package compiler.irs.ssa

import compiler.irs.ssa.Formulas.{Formula, IdValue, IntermediateIdValue, NamedIdValue}
import compiler.lang.Operator.Precedence
import compiler.lang.{Keyword, Operator}

trait FormulaPrinter {

  protected def printIdVal(value: NamedIdValue): String
  
  protected def inclAllocMode: Boolean

  def prettyprint(formula: Formula): String = formula match {
    case IntermediateIdValue(definingScope, uid, nameHint, allocMode) =>
      val allocModeDescr = if inclAllocMode then s"#$allocMode" else ""
      s"$nameHint${"$"}snap${"$"}$uid@${definingScope.scopeUid}i" ++ allocModeDescr
    case value: NamedIdValue => printIdVal(value)
    case Formulas.IntConst(value) => value.toString
    case Formulas.BoolConst(value) => value.toString
    case Formulas.StringConst(value) => s"\"$value\""
    case Formulas.Select(owner, field) =>
      s"${prettyprint(owner)}.${field.fieldId}"
    case Formulas.FunCall(receiver, func, typeArgs, args) =>
      val typeArgsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      s"$receiver.${func.funId}" ++ typeArgsDescr ++ args.map(prettyprint).mkString("(", ",", ")")
    case Formulas.ClosureCall(callee, closureTypingTarget, args) =>
      s"${prettyprint(callee)}(" ++ args.map(prettyprint).mkString(",") ++ ")"
    case Formulas.PureClosureValue(params, body, closureVal) =>
      Keyword.Fn.str + " " + params.map(prettyprint).mkString("(", ", ", ")") + " -> " + prettyprint(body)
    case Formulas.Plus(lhs, Formulas.IntConst(rhsVal)) if rhsVal < 0 =>
      prettyprint(Formulas.Plus(lhs, Formulas.Neg(Formulas.IntConst(-rhsVal))))
    case Formulas.Plus(lhs, Formulas.Neg(rhs)) => printBinop(lhs, Operator.Minus, rhs)
    case Formulas.Plus(lhs, rhs) => printBinop(lhs, Operator.Plus, rhs)
    case Formulas.Neg(operand) => printUnop(Operator.Minus, operand)
    case Formulas.Times(lhs, rhs) => printBinop(lhs, Operator.Times, rhs)
    case Formulas.DivBy(lhs, rhs) => printBinop(lhs, Operator.Div, rhs)
    case Formulas.Modulo(lhs, rhs) => printBinop(lhs, Operator.Modulo, rhs)
    case Formulas.LogicalAnd(lhs, rhs) => printBinop(lhs, Operator.And, rhs)
    case Formulas.LogicalOr(lhs, rhs) => printBinop(lhs, Operator.Or, rhs)
    case Formulas.LogicalNot(Formulas.Equality(lhs, rhs)) => printBinop(lhs, Operator.Inequality, rhs)
    case Formulas.LogicalNot(operand) => printUnop(Operator.ExclamationMark, operand)
    case Formulas.Equality(lhs, rhs) => printBinop(lhs, Operator.Equality, rhs)
    case Formulas.LessOrEq(lhs, rhs) => printBinop(lhs, Operator.LessOrEq, rhs)
    case Formulas.LessThan(lhs, rhs) => printBinop(lhs, Operator.LessThan, rhs)
    case Formulas.TypePredicate(subject, tpe) => s"${ppMaybeParenth(subject, Precedence.TypeTest.bindsMoreThan(precedenceOf(subject)))}"
    case Formulas.Phi(terms) => "phi(" ++ terms.map(prettyprint).mkString(",") ++ ")"
  }

  // TODO may be extended to types

  private def printBinop(lhs: Formula, op: Operator, rhs: Formula): String = {
    val precedence = op.precedenceLevelOpt.get
    val lhsp = ppMaybeParenth(lhs, precedence.bindsMoreThan(precedenceOf(lhs)))
    val rhsp = ppMaybeParenth(rhs, precedence.bindsAtLeastAsMuchAs(precedenceOf(rhs)))
    s"$lhsp $op $rhsp"
  }

  private def printUnop(operator: Operator, operand: Formula): String =
    s"$operator${ppMaybeParenth(operand, operator.precedenceLevelOpt.get.bindsAtLeastAsMuchAs(precedenceOf(operand)))}"

  private def ppMaybeParenth(f: Formula, parenthesize: Boolean): String = {
    val sf = prettyprint(f)
    if parenthesize then s"($sf)" else sf
  }

  private def precedenceOf(f: Formula): Precedence = f match {
    case value: IdValue => Precedence.Atom
    case formula: Formulas.ConstFormula => Precedence.Atom
    case Formulas.Select(owner, field) => Precedence.Atom
    case Formulas.FunCall(receiver, func, typeArgs, args) => Precedence.Atom
    case Formulas.ClosureCall(callee, closureTypingTarget, args) => Precedence.Atom
    case Formulas.PureClosureValue(params, body, closureVal) => Precedence.Atom
    case Formulas.Plus(lhs, rhs) => Precedence.Add
    case Formulas.Neg(operand) => Precedence.Unary
    case Formulas.Times(lhs, rhs) => Precedence.Mul
    case Formulas.DivBy(lhs, rhs) => Precedence.Mul
    case Formulas.Modulo(lhs, rhs) => Precedence.Mul
    case Formulas.LogicalAnd(lhs, rhs) => Precedence.And
    case Formulas.LogicalNot(operand) => Precedence.Unary
    case Formulas.LogicalOr(lhs, rhs) => Precedence.Or
    case Formulas.Equality(lhs, rhs) => Precedence.Comparison
    case Formulas.LessOrEq(lhs, rhs) => Precedence.Comparison
    case Formulas.LessThan(lhs, rhs) => Precedence.Comparison
    case Formulas.TypePredicate(subject, tpe) => Precedence.TypeTest
    case Formulas.Phi(terms) => Precedence.Atom
  }

}

object SourceLevelFormulaPrinter extends FormulaPrinter {
  override protected def printIdVal(value: NamedIdValue): String = value.name
  override protected def inclAllocMode: Boolean = false
}

object IRLevelFormulaPrinter extends FormulaPrinter {

  override protected def printIdVal(value: NamedIdValue): String = value match {
    case Formulas.ParamIdValue(id, definingScope, uid, posOpt) => id.stringId
    case Formulas.ValIdValue(id, definingScope, uid, posOpt) => id.stringId
    case Formulas.VarIdValue(id, declOpt, definingScope, uid, descrOpt, posOpt) =>
      (descrOpt, posOpt) match {
        case (Some(descr), Some(position)) => s"$id<$descr@${position.lineColonColumn}>"
        case (Some(descr), None) => s"$id<$descr>"
        case (None, Some(position)) => s"$id<${position.lineColonColumn}>"
        case (None, None) =>
          s"${value.name}#$uid@${definingScope.scopeUid}${value.valKindDescr}"
      }
    case Formulas.HeapVarIdValue(id, definingScope, uid, posOpt) => s"*name"
    case Formulas.UninterpretedConstIdValue(name, definingScope, uid) => name
  }

  override protected def inclAllocMode: Boolean = true
}
