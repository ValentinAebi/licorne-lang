package compiler.irs

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.Asts.Ast
import compiler.lang.Formulas.{Formula, IdValue, Value}
import compiler.lang.FunctionSignature
import compiler.reporting.Position
import compiler.lang.Types.{PrimitiveType, Type}

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
  
  final case class Function(owner: TypeIdentifier, funId: FunOrVarId, bodyOpt: Option[List[Instr]], posOpt: Option[Position])
  
  final case class LoopVarData(varId: FunOrVarId, beforeLoopVal: IdValue, condVal: IdValue, var bodyLastVal: IdValue) {
    override def toString: String = s"$varId: $beforeLoopVal ; ($condVal) { ... $bodyLastVal }"
  }
  
  final case class DisjunctionVarData(varIdOpt: Option[FunOrVarId], afterThenVal: IdValue, afterElseVal: IdValue, joinedVal: IdValue) {
    override def toString: String = {
      val varIdDescr = varIdOpt.getOrElse("")
      s"$varIdDescr: $joinedVal := phi($afterThenVal, $afterElseVal)"
    }
  }

  sealed trait ControlFlowInstr extends Instr
  final case class Loop(cond: Formula, body: List[Instr], variables: List[LoopVarData]) extends ControlFlowInstr
  final case class Disjunction(cond: Formula, thenBr: List[Instr], elseBr: List[Instr], variables: List[DisjunctionVarData]) extends ControlFlowInstr

  sealed trait AssigningInstr extends Instr {
    val assignedValue: IdValue
  }
  
  final case class StaticTypeAssert(value: IdValue, tpe: Type) extends Instr
  final case class StaticAssert(formula: Formula) extends Instr
  
  final case class Assignment(assignedValue: IdValue, rhs: Formula) extends AssigningInstr
  final case class Instantiate(assignedValue: IdValue, classOrRecordName: TypeIdentifier, typeArgs: List[Type], initialization: List[Instr]) extends AssigningInstr
  final case class ClosureCreation(assignedValue: IdValue, params: List[(IdValue, Type)], var body: List[Instr]) extends AssigningInstr
  final case class Conversion(assignedValue: IdValue, inValue: IdValue, targetType: PrimitiveType) extends AssigningInstr
  
  final case class FieldWrite(owner: IdValue, fieldName: FunOrVarId, rhs: Formula) extends Instr
  final case class Return(retVal: Value) extends Instr
  final case class Panic(msg: Value) extends Instr
  final case class Evaluate(formula: Formula) extends Instr
  final case class Cast(inValue: IdValue, target: TypeIdentifier) extends Instr
  final case class DynamicAssert(formula: Formula) extends Instr
  
  final case class LocalDecl(localId: FunOrVarId, tpe: Type) extends Instr
  
  final case class ErrorInstr(instrOpt: Option[Instr], errorMsg: String) extends Instr

}
