package compiler.valuesconversion

import compiler.irs.Asts.Ast
import compiler.valuesconversion.ValueKind.{FunParamKind, LocalKind, PackageKind, UndefinedKind}
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.Value

import java.util.concurrent.atomic.AtomicLong

final class ValuesGenerator(globalValuesContext: GlobalValuesContext) {
  private val uidGen = AtomicLong(0)

  def newParam(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId): Value = newValue { value =>
    globalValuesContext.saveDebugInfo(value, FunParamKind(funOwnerId, funId, paramId))
  }

  def newPackage(packageId: TypeIdentifier): Value = newValue { value =>
    globalValuesContext.saveDebugInfo(value, PackageKind(packageId))
  }

  def newLocal(localId: FunOrVarId, astNode: Ast): Value = newValue { value =>
    globalValuesContext.saveDebugInfo(value, LocalKind(localId, astNode))
  }

  def newUndefined(astNode: Ast): Value = newValue { value =>
    globalValuesContext.saveDebugInfo(value, UndefinedKind(astNode))
  }

  private def newValue(callback: Value => Unit) = Value(uidGen.incrementAndGet())
}

enum ValueKind {
  case FunParamKind(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId)
  case PackageKind(pkgName: TypeIdentifier)
  case LocalKind(localId: FunOrVarId, introducingAstNode: Ast)
  case UndefinedKind(astNode: Ast)
}
