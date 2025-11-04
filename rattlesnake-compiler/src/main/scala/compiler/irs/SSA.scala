package compiler.irs

import compiler.irs.Asts.{Ast, TypeTree}
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.{FunctionSignature, Values}
import lang.Values.*
import lang.Types.{Type, TypeShape}

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
  
  final case class Function(signature: FunctionSignature, body: List[Instr])

  final case class Loop(preBodyCond: List[PhiMerge], cond: Formula, body: List[Instr], postMerges: List[PhiMerge]) extends Instr
  final case class Disjunction(cond: Formula, thenBr: List[Instr], elseBr: List[Instr], postMerges: List[PhiMerge]) extends Instr

  sealed trait AssigningInstr extends Instr {
    val assignedValue: Value
  }
  final case class PhiMerge(assignedValue: Value, inValues: Set[Value]) extends AssigningInstr
  final case class Assignment(assignedValue: Value, rhs: Formula) extends AssigningInstr
  final case class Instantiate(assignedValue: Value, classOrStructName: TypeIdentifier) extends AssigningInstr
  final case class Cast(assignedValue: Value, inValue: Value, targetType: Type) extends AssigningInstr
  
  final case class FieldWrite(owner: Formula, fieldName: String, value: Formula) extends Instr
  final case class Return(retVal: Option[Formula]) extends Instr
  final case class Panic(msg: Formula) extends Instr
  final case class Evaluate(formula: Formula) extends Instr

}
