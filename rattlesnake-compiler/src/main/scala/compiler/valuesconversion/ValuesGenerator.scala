package compiler.valuesconversion

import compiler.irs.Asts.Ast
import compiler.valuesconversion.ValueKind.{FunParamKind, LocalKind, ObjectKind, TypeAliasParamKind, UndefinedKind}
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.Value

import java.util.concurrent.atomic.AtomicLong

final class ValuesGenerator(globalValuesContext: GlobalValuesContext) {
  private val uidGen = AtomicLong(0)

  def newParam(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId): Value =
    newValue(FunParamKind(funOwnerId, funId, paramId))
    
  def newTypeAliasParam(typeAliasId: TypeIdentifier, paramId: FunOrVarId): Value =
    newValue(TypeAliasParamKind(typeAliasId, paramId))

  def newObject(objectId: TypeIdentifier): Value =
    newValue(ObjectKind(objectId))

  def newLocal(localId: FunOrVarId, astNode: Ast): Value =
    newValue(LocalKind(localId, astNode))

  def newUndefined(astNode: Ast): Value =
    newValue(UndefinedKind(astNode))

  private def newValue(kind: ValueKind): Value = {
    val value = Value(uidGen.incrementAndGet())
    globalValuesContext.saveDebugInfo(value, kind)
    value
  }
}

enum ValueKind {
  case FunParamKind(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId)
  case TypeAliasParamKind(aliasId: TypeIdentifier, paramId: FunOrVarId)
  case ObjectKind(objectName: TypeIdentifier)
  case LocalKind(localId: FunOrVarId, introducingAstNode: Ast)
  case UndefinedKind(astNode: Ast)
}
