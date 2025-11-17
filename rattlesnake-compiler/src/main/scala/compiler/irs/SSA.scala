package compiler.irs

import compiler.irs.Asts.{Ast, TypeTree}
import compiler.reporting.Position
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.{FunctionSignature, Values}
import lang.Values.*
import lang.Types.{Type, BasicType}

object SSA {

  sealed abstract class Instr {
    private var astNode: Option[Ast] = None

    def setAstNode(astNode: Ast): Unit = {
      if (this.astNode.isDefined) {
        throw IllegalStateException("node has already been set")
      }
      this.astNode = Some(astNode)
    }

    def getAstNodeOpt: Option[Ast] = astNode
  }
  
  final case class Function(signature: FunctionSignature, body: List[Instr], codeProviderNameOpt: Option[String])

  sealed trait ControlFlowInstr extends Instr
  final case class Loop(preBodyCond: List[LoopIterPhi], cond: Formula, body: List[Instr], postMerges: List[LoopExitPhi]) extends ControlFlowInstr
  final case class Disjunction(cond: Formula, thenBr: List[Instr], elseBr: List[Instr], postMerges: List[Phi]) extends ControlFlowInstr

  sealed trait AssigningInstr extends Instr {
    val assignedValue: IdValue
  }
  
  sealed trait Phi extends AssigningInstr {
    def inValues: Set[Value]
  }
  final case class RegPhi(assignedValue: IdValue, inValues: Set[Value]) extends Phi
  final case class LoopIterPhi(assignedValue: IdValue, baseCaseValue: Value, prevIterValue: Value) extends Phi {
    override def inValues: Set[Value] = Set(baseCaseValue, prevIterValue)
  }
  final case class LoopExitPhi(assignedValue: IdValue, bodyEndValue: Value, skipLoopValue: Value) extends Phi {
    override def inValues: Set[Value] = Set(bodyEndValue, skipLoopValue)
  }
  
  final case class StaticTypeAssert(value: Value, tpe: Type) extends Instr
  final case class StaticAssert(formula: Formula) extends Instr
  
  final case class Assignment(assignedValue: IdValue, rhs: Formula) extends AssigningInstr
  final case class Instantiate(assignedValue: IdValue, classOrStructName: TypeIdentifier) extends AssigningInstr
  final case class Cast(assignedValue: IdValue, inValue: Value, targetType: BasicType) extends AssigningInstr
  
  final case class FieldWrite(owner: Value, fieldName: FunOrVarId, rhs: Formula) extends Instr
  final case class Return(retVal: Option[Value]) extends Instr
  final case class Panic(msg: Value) extends Instr
  final case class Evaluate(formula: Formula) extends Instr

}
