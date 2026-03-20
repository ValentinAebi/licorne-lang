package compiler.irs

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.Asts.Ast
import compiler.irs.SSA.Scope.scopeUidGen
import compiler.lang.*
import compiler.lang.Formulas.*
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.lang.Types.{PrimitiveType, Type}
import compiler.recurrences.Recurrence
import compiler.typing.{ImmutableUnionFind, MutableUnionFind, UnionFind}
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext, ValuesContext}

import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable
import scala.compiletime.uninitialized

object SSA {

  sealed abstract class Instr {
    private var astNodeOpt: Option[Ast] = None
    private var _uf: Option[ImmutableUnionFind] = None

    def setAstNode(astNode: Ast): this.type = {
      if (this.astNodeOpt.isDefined) {
        throw IllegalStateException("node has already been set")
      }
      this.astNodeOpt = Some(astNode)
      this
    }

    def getAstNodeOpt: Option[Ast] = astNodeOpt

    def uf_=(unionFind: ImmutableUnionFind): Unit = {
      _uf = Some(unionFind)
    }

    def uf: ImmutableUnionFind = _uf.get
  }

  final case class Function(owner: TypeIdentifier, funId: FunOrVarId, bodyOpt: Option[Scope])

  trait VarData

  final case class LoopVarData(varId: FunOrVarId, beforeLoopVal: IdValue, condVal: IdValue, bodyLastVal: IdValue) extends VarData {
    var recurrenceOpt: Option[Recurrence] = None

    override def toString: String = {
      val baseStr = s"$varId: $beforeLoopVal ; ($condVal) { ... $bodyLastVal }"
      recurrenceOpt match {
        case Some(recurrence) =>
          s"$baseStr  RECUR: $recurrence"
        case None => baseStr
      }
    }
  }

  final case class DisjunctionVarData(varIdOpt: Option[FunOrVarId], afterThenVal: IdValue, afterElseVal: IdValue, joinedVal: IdValue) extends VarData {
    override def toString: String = {
      val varIdDescr = varIdOpt match {
        case Some(varId) => s"$varId: "
        case None => ""
      }
      s"$varIdDescr$joinedVal := phi($afterThenVal, $afterElseVal)"
    }
  }

  sealed trait ControlFlowInstr extends Instr

  final case class Loop(cond: Scope, condVal: IdValue, body: Scope, variables: List[LoopVarData]) extends ControlFlowInstr
  final case class Disjunction(condVal: IdValue, thenBr: Scope, elseBr: Scope, variables: List[DisjunctionVarData]) extends ControlFlowInstr
  final case class StaticTypeAssert(value: IdValue, tpe: Type) extends Instr
  final case class StaticAssert(value: IdValue) extends Instr

  sealed trait AssigningInstr extends Instr {
    val assigned: IdValue
  }

  final case class AssignVal(assigned: IdValue, src: IdValue) extends AssigningInstr

  final case class AssignIntConst(assigned: IdValue, src: Int) extends AssigningInstr
  final case class AssignBoolConst(assigned: IdValue, src: Boolean) extends AssigningInstr
  final case class AssignStringConst(assigned: IdValue, src: String) extends AssigningInstr

  final case class NumNeg(assigned: IdValue, operand: IdValue) extends AssigningInstr
  final case class Add(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr
  final case class Sub(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr
  final case class Mul(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr
  final case class Div(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr
  final case class Rem(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr

  final case class LogicNeg(assigned: IdValue, operand: IdValue) extends AssigningInstr
  final case class And(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr
  final case class Or(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr

  final case class Equal(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr
  final case class Leq(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr
  final case class Lt(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr

  final case class FieldRead(assigned: IdValue, owner: IdValue, field: FieldResolutionTarget) extends AssigningInstr
  final case class InvokeFunc(assigned: IdValue, receiver: IdValue, var func: InvocationTarget, typeArgs: List[Type], args: List[IdValue]) extends AssigningInstr
  final case class InvokeClosure(assigned: IdValue, callee: IdValue, args: List[IdValue]) extends AssigningInstr

  final case class Instantiate(assigned: IdValue, classOrRecordName: TypeIdentifier, typeArgs: List[Type]) extends AssigningInstr
  final case class MkClosure(assigned: IdValue, params: List[(ValIdValue, Type)], var body: Scope) extends AssigningInstr

  final case class TypeTest(assigned: IdValue, testedValue: IdValue, testedTypeId: TypeIdentifier) extends AssigningInstr
  final case class Conversion(assigned: IdValue, inValue: IdValue, targetType: PrimitiveType) extends AssigningInstr

  final case class FieldWrite(owner: IdValue, field: FieldResolutionTarget, rhs: IdValue) extends Instr
  final case class Return(retVal: IdValue) extends Instr
  final case class Panic(msg: IdValue) extends Instr
  final case class Cast(inValue: IdValue, target: TypeIdentifier) extends Instr
  final case class Drop(droppedValue: IdValue) extends Instr

  final case class LocalDecl(localId: FunOrVarId, tpe: Type) extends Instr

  enum FieldResolutionTarget {
    case Unresolved(fieldId: FunOrVarId)
    case Unresolvable(fieldId: FunOrVarId)
    case Resolved(receiverSig: UserInstantiableTypeSig, fieldId: FunOrVarId, instantiatedFieldType: Type)

    override def toString: String = this match {
      case Unresolved(fieldId) =>
        s"$fieldId<resol=?>"
      case Unresolvable(fieldId) =>
        s"$fieldId<unres>"
      case Resolved(receiverSig, fieldId, instantiatedFieldType) =>
        s"$fieldId<res=${receiverSig.id}:$instantiatedFieldType>"
    }
  }

  enum InvocationTarget {
    case Unresolved(funId: FunOrVarId)
    case Unresolvable(funId: FunOrVarId)
    case Resolved(ownerSig: EncapsulatedTypeSig, funSig: FunctionSignature, instantiatedReturnType: Type)

    override def toString: String = this match {
      case Unresolved(funId) =>
        s"$funId<resol=?>"
      case Unresolvable(funId) =>
        s"$funId<unres>"
      case Resolved(encapsulatedTypeSig, funSig, instantiatedReturnType) =>
        s"${funSig.functionName}<res=${funSig.ownerName}:$instantiatedReturnType>"
    }
  }

  final class Scope private(val outScopeOpt: Option[Scope], val valuesCtx: ValuesContext) extends Instr {

    var movingUf: MutableUnionFind = uninitialized

    def saveType(idVal: IdValue, tpe: Type): Unit = {
      if (idVal.definingScope == this) {
        movingUf.saveType(idVal, tpe)
      } else if (idVal.definingScope.depth < this.depth && outScopeOpt.isDefined) {
        outScopeOpt.get.saveType(idVal, tpe)
      } else {
        throw IllegalArgumentException(s"illegal type save: $idVal in $this")
      }
    }

    def saveSmartcast(f: Formula, tpe: Type): Unit = {
      movingUf.saveSmartcast(f, tpe)
    }

    def currentTypeOf(idValue: IdValue): Type = {
      uf.currentTypeOf(idValue)
        .orElse(outScopeOpt.map(_.currentTypeOf(idValue)))
        .getOrElse(NothingType)
    }

    def typeOfNoSmartcast(idValue: IdValue): Type = {
      uf.typeOfNoSmartcast(idValue)
        .orElse(outScopeOpt.map(_.typeOfNoSmartcast(idValue)))
        .getOrElse(NothingType)
    }

    def smartcastFor(f: Formula): Option[Type] = {
      uf.smartcastTypeOf(f)
        .orElse(outScopeOpt.flatMap(_.smartcastFor(f)))
    }

    val scopeUid: Long = scopeUidGen.incrementAndGet()

    override def toString: String = {
      val outerScopeDescr = outScopeOpt match {
        case Some(outScope) => s" nested inside ${outScope.uidGen}"
        case None => ""
      }
      s"scope $scopeUid (depth $depth)" + outerScopeDescr
    }

    def getLocalValuesContextOpt: Option[LocalValuesContext] = valuesCtx match {
      case valuesCtx: LocalValuesContext => Some(valuesCtx)
      case _ => None
    }

    def getLocalValuesContextUnsafe: LocalValuesContext = valuesCtx.asInstanceOf[LocalValuesContext]

    def hasExited: Boolean = getLocalValuesContextOpt match {
      case Some(localValsCtx) => localValsCtx.hasExited
      case None => false
    }

    export valuesCtx.globalCtx as globalValuesCtx

    val instructions: mutable.ListBuffer[Instr] = mutable.ListBuffer.empty[Instr]

    val depth: Int = outScopeOpt match {
      case Some(outScope) => outScope.depth + 1
      case None => 0
    }

    private val uidGen = AtomicLong(-1)
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
      IntermediateIdValue(this, _, None)
    }

    def newIntermediate(nameHint: String): IntermediateIdValue = newValue {
      IntermediateIdValue(this, _, Some(nameHint))
    }

    def newUninterpretedConst(name: String): UninterpretedConstIdValue = newValue {
      UninterpretedConstIdValue(name, this, _)
    }

    private def newValue[T <: IdValue](creation: Long => T): T = {
      creation(uidGen.incrementAndGet())
    }

  }

  object Scope {

    def nestedInside(outScope: Scope): Scope = {
      new Scope(Some(outScope), outScope.valuesCtx.withOneMoreFrame)
    }

    def root(globalValuesCtx: GlobalValuesContext): Scope =
      new Scope(None, globalValuesCtx)

    private val scopeUidGen = new AtomicLong(-1)
  }

}
