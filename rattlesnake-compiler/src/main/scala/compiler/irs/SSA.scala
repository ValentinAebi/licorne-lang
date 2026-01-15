package compiler.irs

import compiler.irs.Asts.Ast
import compiler.reporting.Position
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.FunctionSignature
import lang.Types.{PrimitiveType, Type}
import lang.Values.*

object SSA {

  sealed abstract class Instr {
    private var astNode: Option[Ast] = None

    def setAstNode(astNode: Ast): this.type = {
      if (this.astNode.isDefined) {
        throw IllegalStateException("node has already been set")
      }
      this.astNode = Some(astNode)
      this
    }

    def getAstNodeOpt: Option[Ast] = astNode
  }
  
  final case class Function(signature: FunctionSignature, bodyOpt: Option[List[Instr]], posOpt: Option[Position])
  
  final case class LoopVarData(varId: FunOrVarId, beforeLoopVal: IdValue, condVal: IdValue, var bodyLastVal: IdValue) {
    override def toString: String = s"$varId: $beforeLoopVal ; ($condVal) { ... $bodyLastVal }"
  }

  sealed trait ControlFlowInstr extends Instr
  final case class Loop(cond: Formula, body: List[Instr], variables: List[LoopVarData]) extends ControlFlowInstr
  final case class Disjunction(cond: Formula, thenBr: List[Instr], elseBr: List[Instr], postMerges: List[Phi]) extends ControlFlowInstr

  sealed trait AssigningInstr extends Instr {
    val assignedValue: IdValue
  }
  
  final case class Phi(assignedValue: IdValue, inValues: Set[IdValue]) extends AssigningInstr
  
  final case class StaticTypeAssert(value: Value, tpe: Type) extends Instr
  final case class StaticAssert(formula: Formula) extends Instr
  
  final case class Assignment(assignedValue: IdValue, rhs: Formula) extends AssigningInstr
  final case class Instantiate(assignedValue: IdValue, classOrRecordName: TypeIdentifier, typeArgs: List[Type], initialization: List[Instr]) extends AssigningInstr
  final case class ClosureCreation(assignedValue: IdValue, params: List[(IdValue, Type)], body: List[Instr]) extends AssigningInstr
  final case class Conversion(assignedValue: IdValue, inValue: IdValue, targetType: PrimitiveType) extends AssigningInstr
  
  final case class FieldWrite(owner: Value, fieldName: FunOrVarId, rhs: Formula) extends Instr
  final case class Return(retVal: Value) extends Instr
  final case class Panic(msg: Value) extends Instr
  final case class Evaluate(formula: Formula) extends Instr
  final case class Cast(inValue: IdValue, target: TypeIdentifier) extends Instr
  final case class DynamicAssert(formula: Formula) extends Instr
  
  final case class LocalDecl(localId: FunOrVarId, tpe: Type) extends Instr

}
