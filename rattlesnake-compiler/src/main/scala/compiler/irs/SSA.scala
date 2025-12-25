package compiler.irs

import compiler.irs.Asts.Ast
import compiler.reporting.Position
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.FunctionSignature
import lang.Types.Type
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
  
  final case class LoopVarInfo(varId: FunOrVarId, beforeLoopVal: Value, bodyStartVal: IdValue, bodyEndVal: Value, afterLoopVal: IdValue) {
    override def toString: String = s"$varId: $beforeLoopVal ($bodyStartVal ; <body> ; $bodyEndVal) $afterLoopVal"
  }

  sealed trait ControlFlowInstr extends Instr
  final case class Loop(cond: Formula, body: List[Instr], variables: List[LoopVarInfo]) extends ControlFlowInstr
  final case class Disjunction(cond: Formula, thenBr: List[Instr], elseBr: List[Instr], postMerges: List[Phi]) extends ControlFlowInstr

  sealed trait AssigningInstr extends Instr {
    val assignedValue: IdValue
  }
  
  final case class Phi(assignedValue: IdValue, inValues: Set[Value]) extends AssigningInstr
  
  final case class StaticTypeAssert(value: Value, tpe: Type) extends Instr
  final case class StaticAssert(formula: Formula) extends Instr
  
  final case class Assignment(assignedValue: IdValue, rhs: Formula) extends AssigningInstr
  final case class Instantiate(assignedValue: IdValue, classOrRecordName: TypeIdentifier, typeArgs: List[Type], initialization: List[Instr]) extends AssigningInstr
  final case class ClosureCreation(assignedValue: IdValue, params: List[(IdValue, Type)], body: List[Instr]) extends AssigningInstr
  final case class Cast(assignedValue: IdValue, inValue: IdValue, target: TypeIdentifier) extends AssigningInstr
  
  final case class FieldWrite(owner: Value, fieldName: FunOrVarId, rhs: Formula) extends Instr
  final case class Return(retValOpt: Option[Value]) extends Instr
  final case class Panic(msg: Value) extends Instr
  final case class Evaluate(formula: Formula) extends Instr
  final case class DynamicAssert(formula: Formula) extends Instr
  
  final case class LocalDecl(localId: FunOrVarId, tpe: Type) extends Instr

}
