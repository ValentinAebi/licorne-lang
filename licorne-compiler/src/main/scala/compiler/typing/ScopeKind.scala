package compiler.typing

import compiler.identifiers.FunOrVarId
import compiler.lang.Types.{Type, TypeVariable}

enum ScopeKind {
  case FuncBody(funId: FunOrVarId, retType: Type)
  case ClosureBody(retType: TypeVariable)
  case NotAFunc

  def retTypeOpt: Option[Type] = this match {
    case ScopeKind.FuncBody(_, retType) => Some(retType)
    case ScopeKind.ClosureBody(retType) => Some(retType)
    case ScopeKind.NotAFunc => None
  }
}
