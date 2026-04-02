package compiler.irs

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.Asts.Ast
import compiler.irs.SSA.InvocationTarget.*
import compiler.irs.SSA.Scope.scopeUidGen
import compiler.lang.*
import compiler.lang.Formulas.*
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.lang.Types.{PrimitiveType, Type}
import compiler.pipeline.CompilationStep
import compiler.recurrences.Recurrence
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.smt.Simplifier
import compiler.typing.MeetJoinComputer
import compiler.typing.contexts.{ResolutionContext, TypeParamsContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext, ValuesContext}

import java.util.concurrent.atomic.AtomicLong
import scala.collection.{immutable, mutable}
import scala.compiletime.uninitialized

object SSA {

  sealed abstract class Instr {
    private var astNodeOpt: Option[Ast] = None

    def setAstNode(astNode: Ast): this.type = {
      if (this.astNodeOpt.isDefined) {
        throw IllegalStateException("node has already been set")
      }
      this.astNodeOpt = Some(astNode)
      this
    }

    def getAstNodeOpt: Option[Ast] = astNodeOpt

    def getPosition: Option[Position] = getAstNodeOpt.flatMap(_.getPosition)
  }

  final case class Function(owner: TypeIdentifier, funId: FunOrVarId, bodyOpt: Option[Scope])

  trait VarData

  final case class LoopVarData(varId: FunOrVarId, beforeLoopVal: IdValue, condVal: IdValue, bodyLastVal: IdValue) extends VarData {
    var recurrenceOpt: Option[Recurrence] = None
    var handledThroughRecurrenceFlag: Boolean = false

    def recurDescr: String = {
      recurrenceOpt match {
        case Some(recurrence) =>
          s"RECUR: $recurrence"
        case None => ""
      }
    }

    override def toString: String = {
      val baseStr = s"$varId: $beforeLoopVal ; ($condVal) { ... $bodyLastVal }"
      baseStr ++ "  " ++ recurDescr
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

  final case class Loop(cond: Scope, condVal: IdValue, body: Scope, variables: List[LoopVarData]) extends ControlFlowInstr {
    val invariants: mutable.Seq[Formula] = mutable.ListBuffer.empty[Formula]
  }
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

  final case class FieldRead(assigned: IdValue, owner: IdValue, var field: FieldResolutionTarget) extends AssigningInstr
  final case class InvokeFunc(assigned: IdValue, receiver: IdValue, var func: InvocationTarget, typeArgs: List[Type], args: List[IdValue]) extends AssigningInstr
  final case class InvokeClosure(assigned: IdValue, callee: IdValue, args: List[IdValue]) extends AssigningInstr

  final case class Instantiate(assigned: IdValue, classOrRecordName: TypeIdentifier, typeArgs: List[Type]) extends AssigningInstr
  final case class MkClosure(assigned: IdValue, params: List[(ValIdValue, Type)], var body: Scope) extends AssigningInstr

  final case class TypeTest(assigned: IdValue, testedValue: IdValue, testedTypeId: TypeIdentifier) extends AssigningInstr
  final case class Conversion(assigned: IdValue, inValue: IdValue, targetType: PrimitiveType) extends AssigningInstr

  final case class FieldWrite(owner: IdValue, var field: FieldResolutionTarget, rhs: IdValue) extends Instr
  final case class Return(retVal: IdValue) extends Instr
  final case class Panic(msg: IdValue) extends Instr
  final case class Cast(inValue: IdValue, target: TypeIdentifier) extends Instr
  final case class Drop(droppedValue: IdValue) extends Instr

  final case class LocalDecl(localId: FunOrVarId, tpe: Type) extends Instr

  enum FieldResolutionTarget {
    case UnresolvedField(fieldId: FunOrVarId)
    case UnresolvableField(fieldId: FunOrVarId)
    case ResolvedField(receiverSig: UserInstantiableTypeSig, fieldId: FunOrVarId, instantiatedFieldType: Type)

    override def toString: String = this match {
      case UnresolvedField(fieldId) =>
        s"$fieldId<resol:?>"
      case UnresolvableField(fieldId) =>
        s"$fieldId<unresolved>"
      case ResolvedField(receiverSig, fieldId, instantiatedFieldType) =>
        s"$fieldId<rec:${receiverSig.id};ret:$instantiatedFieldType>"
    }
  }

  enum InvocationTarget {
    case UnresolvedFun(funId: FunOrVarId)
    case UnresolvableFun(funId: FunOrVarId)
    case ResolvedFun(ownerSig: EncapsulatedTypeSig, funSig: FunctionSignature, instantiatedReturnType: Type)

    def functionName: FunOrVarId = this match {
      case UnresolvedFun(funId) => funId
      case UnresolvableFun(funId) => funId
      case ResolvedFun(ownerSig, funSig, instantiatedReturnType) => funSig.functionName
    }

    override def toString: String = this match {
      case UnresolvedFun(funId) =>
        s"$funId<resol:?>"
      case UnresolvableFun(funId) =>
        s"$funId<unresolved>"
      case ResolvedFun(encapsulatedTypeSig, funSig, instantiatedReturnType) =>
        s"${funSig.functionName}<rec:${funSig.ownerName};ret:$instantiatedReturnType>"
    }
  }

  final class Scope private(val outScopeOpt: Option[Scope], val valuesCtx: ValuesContext) extends Instr {
    private val types = mutable.Map.empty[IdValue, Type]
    private val smartcasts = mutable.SeqMap.empty[Formula, Type]

    export valuesCtx.globalCtx as globalValuesCtx

    val instructions: mutable.ListBuffer[Instr] = mutable.ListBuffer.empty[Instr]

    val depth: Int = outScopeOpt match {
      case Some(outScope) => outScope.depth + 1
      case None => 0
    }

    private val uidGen = AtomicLong(-1)
    private val values = mutable.LinkedHashSet.empty[IdValue]

    val scopeUid: Long = scopeUidGen.incrementAndGet()

    def getSmartcasts: immutable.SeqMap[Formula, Type] = immutable.SeqMap.from(smartcasts)

    def isNestedIn(outerScope: Scope): Boolean =
      outerScope.depth < this.depth && (
        outScopeOpt.contains(outerScope) ||
          (outScopeOpt.isDefined && outScopeOpt.get.isNestedIn(outerScope)))

    def saveType(idVal: IdValue, tpe: Type)(using tpCtx: TypeParamsContext, resolCtx: ResolutionContext, proxyStore: ProxyStore): Unit = {
      if (idVal.definingScope == this) {
        if (types.contains(idVal)){
          throw IllegalStateException(s"$idVal has already been assigned a type")
        }
        types.put(idVal, tpe)
      } else if (idVal.definingScope.depth < this.depth && outScopeOpt.isDefined) {
        outScopeOpt.get.saveType(idVal, tpe.filtered(idVal, Some(this, proxyStore)))
      } else {
        throw IllegalArgumentException(s"illegal type save: $idVal in $this")
      }
    }

    def saveSmartcast(f: Formula, smartcastType: Type)(using meetJoin: MeetJoinComputer, proxyStore: ProxyStore): Unit = {
      val oldType = currentTypeOf(f)
      val newType = meetJoin.computeMeet(oldType, smartcastType)
      smartcasts.put(f, newType)
    }

    def currentTypeOf(formula: Formula)(using ProxyStore): Type = {
      smartcastFor(formula)
        .orElse(formula match {
          case f: IdValue => types.get(f)
          case _ => None
        }).orElse(outScopeOpt.map(_.currentTypeOf(formula)))
        .getOrElse(NothingType)
    }

    def smartcastFor(f: Formula)(using proxyStore: ProxyStore): Option[Type] = {
      smartcasts.get(f).orElse {
        outScopeOpt.flatMap(_.smartcastFor(f))
      }
    }

    private def typeOfNoSmartcast(idValue: IdValue): Type = {
      types.get(idValue).orElse {
        outScopeOpt.map(_.typeOfNoSmartcast(idValue))
      }.getOrElse(NothingType)
    }

    override def toString: String = {
      val outerScopeDescr = outScopeOpt match {
        case Some(outScope) => s" nested inside ${outScope.scopeUid}"
        case None => ""
      }
      s"scope $scopeUid (depth $depth)" + outerScopeDescr
    }

    def getLocalValuesContextOpt: Option[LocalValuesContext] = valuesCtx match {
      case valuesCtx: LocalValuesContext => Some(valuesCtx)
      case _ => None
    }

    def getLocalValuesContextUnsafe: LocalValuesContext = valuesCtx.asInstanceOf[LocalValuesContext]

    def resetHasExited(): Unit = {
      getLocalValuesContextUnsafe.resetHasExited()
    }

    def markHasExited(): Unit = {
      getLocalValuesContextUnsafe.markHasExited()
    }

    def markHasExitedIfNothing(tpe: Type): Unit = {
      if (tpe == NothingType) {
        markHasExited()
      }
    }

    def hasExited: Boolean = getLocalValuesContextOpt match {
      case Some(localValsCtx) => localValsCtx.hasExited
      case None => false
    }

    def reportHasExitedIfNeeded(er: ErrorReporter, posOpt: Option[Position])
                               (using CompilationStep): Unit = {
      getLocalValuesContextUnsafe.reportHasExitedIfNeeded(er, posOpt)
    }

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

    def nestedInside(outScope: Scope): Scope =
      new Scope(Some(outScope), outScope.valuesCtx.withOneMoreFrame)

    def root(globalValuesCtx: GlobalValuesContext): Scope =
      new Scope(None, globalValuesCtx)

    private val scopeUidGen = new AtomicLong(-1)
  }

}
