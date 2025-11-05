package compiler.valuesconversion

import compiler.irs.Asts.{Ast, TypeTree}
import compiler.valuesconversion.ValueKind.*
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.{IdValue, Value}

import java.util.concurrent.atomic.AtomicLong

final class ValuesGenerator(globalValuesContext: GlobalValuesContext) {
  private val uidGen = AtomicLong(0)

  def newParam(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId): Value =
    newValue(FunParamKind(funOwnerId, funId, paramId))

  def newObject(objectId: TypeIdentifier): Value =
    newValue(ObjectKind(objectId))

  def newLocal(localId: FunOrVarId, astNode: Ast, typeAnnot: Option[TypeTree]): Value =
    newValue(LocalKind(localId, astNode, typeAnnot))
    
  def newIntermediate(astNode: Ast): Value =
    newValue(IntermediateKind(astNode))
    
  def newPhi(inputValues: Set[Value]): Value =
    newValue(PhiKind(inputValues))

  def newUndefined(astNode: Ast): Value =
    newValue(UndefinedKind(astNode))

  private def newValue(kind: ValueKind): Value = {
    val value = IdValue(uidGen.incrementAndGet())
    globalValuesContext.saveDebugInfo(value, kind)
    value
  }
}

enum ValueKind {
  case FunParamKind(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId)
  case ObjectKind(objectName: TypeIdentifier)
  case LocalKind(localId: FunOrVarId, introducingAstNode: Ast, typeAnnot: Option[TypeTree])
  case IntermediateKind(introducingAstNode: Ast)
  case PhiKind(inputValues: Set[Value])
  case UndefinedKind(astNode: Ast)
}
