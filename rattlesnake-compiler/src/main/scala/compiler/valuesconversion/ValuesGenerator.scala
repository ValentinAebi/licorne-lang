package compiler.valuesconversion

import compiler.irs.Asts
import compiler.irs.Asts.Ast
import compiler.valuesconversion.ValueKind.*
import identifiers.{FunOrVarId, Identifier, NormalFunOrVarId, TypeIdentifier}
import lang.Types.Type
import lang.Values.{IdValue, Value}

import scala.collection.mutable

final class ValuesGenerator(globalValuesContext: GlobalValuesContext) {
  private val uidGen = mutable.Map.empty[Identifier, Int]

  def newParam(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId): IdValue =
    newValue(FunParamKind(funOwnerId, funId, paramId))

  def newObject(objectId: TypeIdentifier): IdValue =
    newValue(ObjectKind(objectId))

  def newLocal(localId: FunOrVarId, astNode: Ast, typeAnnotOpt: Option[Type]): IdValue =
    newValue(LocalKind(localId, astNode, typeAnnotOpt))

  def newIntermediate(astNode: Ast): IdValue =
    newValue(IntermediateKind(astNode))

  def newPhi(localId: FunOrVarId, inputValues: Set[Value], controlFlowNode: Asts.Ast): IdValue =
    newValue(PhiKind(localId, inputValues, controlFlowNode))

  def newMissingValue(missingId: FunOrVarId, astNode: Ast): IdValue =
    newValue(MissingValueKind(missingId, astNode))

  def newIllegalConstruct(construct: Ast): IdValue =
    newValue(IllegalConstructKind(construct))

  private def newValue(kind: ValueKind): IdValue = {
    val varId = kind.referencedSourceId.getOrElse(NormalFunOrVarId("unk"))
    val uidIdx = uidGen.getOrElse(varId, 0)
    uidGen(varId) = uidIdx + 1
    val value = IdValue(s"$varId$$$uidIdx")
    globalValuesContext.saveDebugInfo(value, kind)
    value
  }
}

enum ValueKind {
  case FunParamKind(funOwnerId: TypeIdentifier, funId: FunOrVarId, paramId: FunOrVarId)
  case ObjectKind(objectName: TypeIdentifier)
  case LocalKind(localId: FunOrVarId, introducingAstNode: Ast, typeAnnot: Option[Type])
  case PhiKind(localId: FunOrVarId, inputValues: Set[Value], controlFlowNode: Asts.Ast)
  case IntermediateKind(introducingAstNode: Ast)
  case MissingValueKind(missingId: FunOrVarId, astNode: Ast)
  case IllegalConstructKind(construct: Ast)

  def referencedSourceId: Option[Identifier] = this match {
    case FunParamKind(funOwnerId, funId, paramId) => Some(paramId)
    case ObjectKind(objectName) => Some(objectName)
    case LocalKind(localId, introducingAstNode, typeAnnot) => Some(localId)
    case PhiKind(localId, inputValues, loop) => Some(localId)
    case IntermediateKind(introducingAstNode) => None
    case MissingValueKind(missingId, astNode) => None
  }

}
