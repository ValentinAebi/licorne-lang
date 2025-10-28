package compiler.irs

import compiler.irs.Asts.{Ast, TypeTree}
import identifiers.TypeIdentifier
import lang.FunctionSignature
import lang.Values.*
import lang.Types.TypeShape

object SSA {

  sealed abstract class Instr {
    private var astNode: Option[Ast] = None
    private var nextInstr: Option[Instr] = None

    def setAstNode(astNode: Ast): Unit = {
      if (this.astNode.isDefined) {
        throw IllegalStateException("node has already been set")
      }
      this.astNode = Some(astNode)
    }

    def getAstNodeOpt: Option[Ast] = astNode

    def setNextInstr(nextInstr: Instr): Unit = {
      if (this.nextInstr.isDefined) {
        throw IllegalStateException("next instruction has already been set")
      }
      this.nextInstr = Some(nextInstr)
    }

    def nextInstrOpt: Option[Instr] = nextInstr
  }

  sealed trait FunctionsContainer {
    def methods: List[Function]
  }
  final case class Package(pkgId: TypeIdentifier, methods: List[Function]) extends FunctionsContainer
  final case class Class(classId: TypeIdentifier, fields: List[Field], methods: List[Function]) extends FunctionsContainer

  final case class Field(name: String, tpe: TypeTree)
  final case class Function(signature: FunctionSignature, body: List[Instr])

  final case class Assignment(value: Value, rhs: Formula) extends Instr
  final case class ShapeSmartCast(out: Value, in: Value, newShape: TypeShape) extends Instr
  final case class Assumption(formula: Formula) extends Instr {
    private var discardedFlag: Boolean = false

    def discard(): Unit = {
      discardedFlag = true
    }
    
    def isDiscarded: Boolean = discardedFlag
  }

  final case class Jump(jumpCondition: Formula, target: JumpTarget) extends Instr
  final case class JumpTarget() extends Instr
  final case class FieldWrite(owner: Formula, fieldName: String, value: Formula) extends Instr
  final case class Return(retVal: Option[Formula]) extends Instr
  final case class Panic(msg: Formula) extends Instr

}
