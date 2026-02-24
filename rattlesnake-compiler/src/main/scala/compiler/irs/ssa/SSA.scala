package compiler.irs.ssa

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.Asts.Ast
import compiler.irs.ssa.egraphs.EGraph
import compiler.lang.{FunctionSignature, Operator, RuntimeTypeSignature, TypeSignature, UserInstantiable}
import compiler.lang.Types.{PrimitiveType, Type}
import compiler.reporting.Position

import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable

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

  final case class Loop(condEval: List[Instr], cond: IdValue, body: List[Instr], variables: List[LoopVarData]) extends ControlFlowInstr
  final case class Disjunction(cond: IdValue, thenBr: List[Instr], elseBr: List[Instr], variables: List[DisjunctionVarData]) extends ControlFlowInstr

  final case class StaticTypeAssert(value: IdValue, tpe: Type) extends Instr
  final case class StaticAssert(value: IdValue) extends Instr

  sealed trait AssigningInstr extends Instr {
    val assigned: IdValue
  }

  final case class Assignment(assigned: IdValue, src: IdValue) extends AssigningInstr
  final case class FieldRead(assigned: IdValue, owner: IdValue, field: FieldResolutionTarget) extends AssigningInstr
  final case class InvokeFunc(assigned: IdValue, receiver: IdValue, var func: InvocationTarget, args: List[IdValue]) extends AssigningInstr
  final case class InvokeClosure(assigned: IdValue, callee: IdValue, args: List[IdValue]) extends AssigningInstr
  final case class Instantiate(assigned: IdValue, classOrRecordName: TypeIdentifier, typeArgs: List[Type], initialization: List[Instr]) extends AssigningInstr
  final case class MkClosure(assigned: IdValue, params: List[(IdValue, Type)], var body: List[Instr]) extends AssigningInstr

  final case class Conversion(assigned: IdValue, inValue: IdValue, targetType: PrimitiveType) extends AssigningInstr

  final case class FieldWrite(owner: IdValue, field: FieldResolutionTarget, rhs: IdValue) extends Instr
  final case class Return(retVal: IdValue) extends Instr
  final case class Panic(msg: IdValue) extends Instr
  final case class Cast(inValue: IdValue, target: TypeIdentifier) extends Instr

  final case class LocalDecl(localId: FunOrVarId, tpe: Type) extends Instr

  enum FieldResolutionTarget {
    case Unresolved(receiver: IdValue)
    case Resolved(receiver: IdValue, receiverSig: UserInstantiable, fieldId: FunOrVarId)
  }

  enum InvocationTarget {
    case Unresolved(funId: FunOrVarId)
    case Resolved(funSig: FunctionSignature)
  }

  final class Scope(
                     val ctxGraph: EGraph,
                     val instructions: List[Instr],
                     val outScopeOpt: Option[Scope]
                   ) extends Instr {

    val depth: Int = outScopeOpt match {
      case Some(outScope) => outScope.depth + 1
      case None => 0
    }

    private val uidGen = AtomicLong(0)
    private val values = mutable.LinkedHashSet.empty[IdValue]

    def newParam(srcId: FunOrVarId): ParamIdValue = newValue {
      ParamIdValue(srcId, this, _)
    }

    def newVal(srcId: FunOrVarId): ValIdValue = newValue {
      ValIdValue(srcId, this, _)
    }

    def newVar(srcId: FunOrVarId): VarIdValue = newValue {
      VarIdValue(srcId, this, _)
    }

    def newIntermediate(): IntermediateIdValue = newValue {
      IntermediateIdValue(this, _)
    }
    
    def newUninterpretedConst(descr: String): UninterpretedConst = newValue {
      UninterpretedConst(descr, this, _)
    }

    private def newValue[T <: IdValue](creation: Long => T): T = {
      creation(uidGen.incrementAndGet())
    }

  }

  sealed trait IdValue {
    def uid: Long

    def definingScope: Scope
  }

  sealed trait UserDefinedIdValue extends IdValue {
    def srcId: FunOrVarId
  }

  final case class ParamIdValue(srcId: FunOrVarId, definingScope: Scope, uid: Long) extends UserDefinedIdValue

  final case class ValIdValue(srcId: FunOrVarId, definingScope: Scope, uid: Long) extends UserDefinedIdValue

  final case class VarIdValue(srcId: FunOrVarId, definingScope: Scope, uid: Long) extends UserDefinedIdValue

  final case class IntermediateIdValue(definingScope: Scope, uid: Long) extends IdValue
  
  final case class UninterpretedConst(descr: String, definingScope: Scope, uid: Long) extends IdValue

}
