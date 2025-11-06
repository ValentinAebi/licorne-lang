package compiler.valuesconversion

import compiler.irs.Asts
import compiler.irs.Asts.{Ast, TypeTree}
import compiler.valuesconversion.ValueKind.*
import identifiers.{FunOrVarId, Identifier, TypeIdentifier}
import lang.Types.Type
import lang.Values.{IdValue, Value}

import java.util.concurrent.atomic.AtomicLong

final class ValuesGenerator(globalValuesContext: GlobalValuesContext) {
  private val uidGen = AtomicLong(0)

  def newParam(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId): Value =
    newValue(FunParamKind(funOwnerId, funId, paramId))

  def newObject(objectId: TypeIdentifier): Value =
    newValue(ObjectKind(objectId))

  def newLocal(localId: FunOrVarId, astNode: Ast, typeAnnot: Option[Type]): Value =
    newValue(LocalKind(localId, astNode, typeAnnot))

  def newIntermediate(astNode: Ast): Value =
    newValue(IntermediateKind(astNode))

  def newPhi(localId: FunOrVarId, inputValues: Set[Value], controlFlowNode: Asts.Ast): Value =
    newValue(PhiKind(localId, inputValues, controlFlowNode))

  def newUndefined(astNode: Ast): Value =
    newValue(UndefinedKind(astNode))

  private def newValue(kind: ValueKind): Value = {
    val value = IdValue(uidGen.incrementAndGet())
    globalValuesContext.offerDebugInfo(value, kind)
    value
  }
}

enum ValueKind {
  // Ordered by priority level
  case FunParamKind(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId)
  case ObjectKind(objectName: TypeIdentifier)
  case LocalKind(localId: FunOrVarId, introducingAstNode: Ast, typeAnnot: Option[Type])
  case PhiKind(localId: FunOrVarId, inputValues: Set[Value], controlFlowNode: Asts.Ast)
  case IntermediateKind(introducingAstNode: Ast)
  case UndefinedKind(astNode: Ast)

  def referencedLocal: Option[Identifier] = this match {
    case FunParamKind(funOwnerId, funId, paramId) => Some(paramId)
    case ObjectKind(objectName) => Some(objectName)
    case LocalKind(localId, introducingAstNode, typeAnnot) => Some(localId)
    case PhiKind(localId, inputValues, loop) => Some(localId)
    case IntermediateKind(introducingAstNode) => None
    case UndefinedKind(astNode) => None
  }

}
