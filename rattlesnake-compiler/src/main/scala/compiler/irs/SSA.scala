package compiler.irs

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.Asts.Ast
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
import compiler.typing.{MeetJoinComputer, Typer}
import compiler.typing.contexts.{ResolutionContext, TypeParamsContext}
import compiler.typing.smartcasting.egraphs.{EClass, EGraph}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext, ValuesContext}

import java.util.concurrent.atomic.AtomicLong
import scala.collection.{immutable, mutable}

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

  sealed trait RealInstr extends Instr

  sealed trait ControlFlowInstr extends RealInstr

  final case class Loop(cond: Scope, condVal: IdValue, body: Scope, variables: List[LoopVarData]) extends ControlFlowInstr {
    val invariants: mutable.Seq[Formula] = mutable.ListBuffer.empty[Formula]
  }
  final case class Disjunction(condVal: IdValue, thenBr: Scope, elseBr: Scope, variables: List[DisjunctionVarData]) extends ControlFlowInstr
  final case class StaticTypeAssert(value: IdValue, tpe: Type) extends RealInstr
  final case class StaticAssert(value: IdValue) extends RealInstr

  sealed trait AssigningInstr extends RealInstr {
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
  final case class HeapVarRead(assigned: IdValue, heapVar: HeapVarIdValue) extends AssigningInstr
  final case class InvokeFunc(assigned: IdValue, receiver: IdValue, var func: InvocationTarget, typeArgs: List[Type], args: List[IdValue]) extends AssigningInstr
  final case class InvokeClosure(assigned: IdValue, callee: IdValue, args: List[IdValue]) extends AssigningInstr

  final case class Instantiate(assigned: IdValue, classOrRecordName: TypeIdentifier, typeArgs: List[Type]) extends AssigningInstr
  final case class MkClosure(assigned: IdValue, params: List[(ParamIdValue, Type)], var body: Scope) extends AssigningInstr
  final case class MkHeapVar(assigned: HeapVarIdValue) extends AssigningInstr

  final case class TypeTest(assigned: IdValue, testedValue: IdValue, testedTypeId: TypeIdentifier) extends AssigningInstr
  final case class Conversion(assigned: IdValue, inValue: IdValue, targetType: PrimitiveType) extends AssigningInstr

  final case class FieldWrite(owner: IdValue, var field: FieldResolutionTarget, rhs: IdValue) extends RealInstr
  final case class HeapVarWrite(heapVar: HeapVarIdValue, newValue: IdValue) extends RealInstr
  final case class Return(retVal: IdValue) extends RealInstr
  final case class Panic(msg: IdValue) extends RealInstr
  final case class Cast(inValue: IdValue, target: TypeIdentifier) extends RealInstr
  final case class Drop(droppedValue: IdValue) extends RealInstr

  final class FieldResolutionTarget(val fieldId: FunOrVarId) {
    private var receiverSigOpt = Option.empty[UserInstantiableTypeSig]
    private var instantiatedFieldTypeOpt = Option.empty[Type]
    private var cannotResolveFlag = false

    def isResolved: Boolean = receiverSigOpt.isDefined

    def isResolvedAndStable: Boolean =
      receiverSigOpt.exists(_.fields.get(fieldId).exists(_.isStable))

    def isUnresolvable: Boolean = cannotResolveFlag

    def isNotResolvedYet: Boolean = !isResolved && !isUnresolvable

    def resolve(receiverSig: UserInstantiableTypeSig, instantiatedFieldType: Type): Unit = {
      if (isResolved) {
        throw AssertionError("trying to resolve an already resolved field resolution target")
      } else if (isUnresolvable) {
        throw AssertionError("trying to resolve a field resolution target marked as unresolvable")
      }
      receiverSigOpt = Some(receiverSig)
      instantiatedFieldTypeOpt = Some(instantiatedFieldType)
    }

    def getReceiverSigUnsafe: UserInstantiableTypeSig = receiverSigOpt.get

    def getInstantiatedFieldTypeUnsafe: Type = instantiatedFieldTypeOpt.get

    def markUnresolvable(): Unit = {
      cannotResolveFlag = true
    }

    override def toString: String = {
      if isResolved then s"$fieldId<rec:${getReceiverSigUnsafe.id};ret:$getInstantiatedFieldTypeUnsafe>"
      else if isUnresolvable then s"$fieldId<unresolved>"
      else s"$fieldId<resol:?>"
    }
  }

  final class InvocationTarget(val funId: FunOrVarId) {
    private var receiverSigOpt = Option.empty[EncapsulatedTypeSig]
    private var funSigOpt = Option.empty[FunctionSignature]
    private var instantiatedReturnTypeOpt = Option.empty[Type]
    private var cannotResolveFlag = false

    def isResolved: Boolean = receiverSigOpt.isDefined

    def isResolvedAndPure: Boolean = funSigOpt.exists(_.isPure)

    def isUnresolvable: Boolean = cannotResolveFlag

    def isNotResolvedYet: Boolean = !isResolved && !isUnresolvable

    def resolve(receiverSig: EncapsulatedTypeSig, funSig: FunctionSignature, instantiatedReturnType: Type): Unit = {
      if (isResolved) {
        throw AssertionError("trying to resolve an already resolved field resolution target")
      } else if (isUnresolvable) {
        throw AssertionError("trying to resolve a field resolution target marked as unresolvable")
      }
      receiverSigOpt = Some(receiverSig)
      funSigOpt = Some(funSig)
      instantiatedReturnTypeOpt = Some(instantiatedReturnType)
    }

    def getReceiverSigUnsafe: EncapsulatedTypeSig = receiverSigOpt.get

    def getFunSigUnsafe: FunctionSignature = funSigOpt.get

    def getInstantiatedReturnTypeUnsafe: Type = instantiatedReturnTypeOpt.get

    def markUnresolvable(): Unit = {
      cannotResolveFlag = true
    }

    override def toString: String = {
      if isResolved then s"$funId<rec:${getFunSigUnsafe.ownerName};ret:$getInstantiatedReturnTypeUnsafe>"
      else if isUnresolvable then s"$funId<unresolved>"
      else s"$funId<resol:?>"
    }
  }

  final class Scope private(
                             val outScopeOpt: Option[Scope],
                             val valuesCtx: ValuesContext,
                             objectInitializedInThisScopeOpt: Option[IdValue]
                           ) extends RealInstr {
    private val types = mutable.Map.empty[IdValue, Type]

    /**
     * WARNING: To be used only by Typer, might contain incorrect data during later phases because of insertion of
     * smartcasts in the middle of scopes
     */
    private lazy val smartcastsEGraph: EGraph = outScopeOpt match {
      case Some(outEGraph) => outEGraph.smartcastsEGraph.deepCopy
      case None => EGraph.newEmpty
    }

    export valuesCtx.globalCtx as globalValuesCtx

    val instructions: mutable.ListBuffer[Instr] = mutable.ListBuffer.empty[Instr]

    val depth: Int = outScopeOpt match {
      case Some(outScope) => outScope.depth + 1
      case None => 0
    }

    private val uidGen = AtomicLong(-1)
    private val values = mutable.LinkedHashSet.empty[IdValue]

    val scopeUid: Long = scopeUidGen.incrementAndGet()

    private var realInstrIterOpt = Option.empty[Scope.RealInstrIter]

    def forTraversal[T](action: Scope.RealInstrIter => T): T = {
      if (realInstrIterOpt.isDefined){
        throw IllegalStateException(s"another traversal of $this is already underway")
      }
      val iter = Scope.RealInstrIter(this)
      realInstrIterOpt = Some(iter)
      val result = action(iter)
      realInstrIterOpt = None
      result
    }

    def insertPseudoInstr(pseudoInstr: PseudoInstr): Unit = {
      realInstrIterOpt match {
        case None =>
          val idx = instructions.indexWhere(_.isInstanceOf[RealInstr])
          instructions.insert(idx, pseudoInstr)
        case Some(iter) =>
          iter.insertPseudoInstr(pseudoInstr)
      }
    }

    def isNestedIn(outerScope: Scope): Boolean =
      outerScope.depth < this.depth && (
        outScopeOpt.contains(outerScope) ||
          (outScopeOpt.isDefined && outScopeOpt.get.isNestedIn(outerScope)))

    def saveType(idVal: IdValue, tpe: Type)(using tpCtx: TypeParamsContext, resolCtx: ResolutionContext, proxyStore: ProxyStore): Unit = {
      if (idVal.definingScope == this) {
        if (types.contains(idVal)) {
          throw IllegalStateException(s"$idVal has already been assigned a type")
        }
        types.put(idVal, tpe)
      } else if (idVal.definingScope.depth < this.depth && outScopeOpt.isDefined) {
        outScopeOpt.get.saveType(idVal, tpe.filtered(idVal, Some(this, proxyStore)))
      } else {
        throw IllegalArgumentException(s"illegal type save: $idVal in $this")
      }
    }

    def saveSmartcast(f: Formula, smartcastType: Type)(using meetJoin: MeetJoinComputer, simplifier: Simplifier, proxyStore: ProxyStore): Unit = {
      smartcastsEGraph.saveSmartcast(f, smartcastType).foreach { newSmartcastType =>
        val eClId = smartcastsEGraph.classIdOf(f)
        insertPseudoInstr(Smartcast(eClId, newSmartcastType, smartcastsEGraph.deepCopy))
      }
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
      smartcastsEGraph.smartcastFor(f)
    }

    def isInitScopeOf(idValue: IdValue): Boolean =
      objectInitializedInThisScopeOpt.contains(idValue)

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

    def newParam(srcId: FunOrVarId, posOpt: Option[Position]): ParamIdValue = newValue {
      ParamIdValue(srcId, this, _, posOpt)
    }

    def newVal(srcId: FunOrVarId, posOpt: Option[Position]): ValIdValue = newValue {
      ValIdValue(srcId, this, _, posOpt)
    }

    def newVar(srcId: FunOrVarId, descrOpt: Option[String], posOpt: Option[Position]): VarIdValue = newValue {
      VarIdValue(srcId, this, _, descrOpt, posOpt)
    }

    def newHeapVar(srcId: FunOrVarId, posOpt: Option[Position]): HeapVarIdValue = newValue {
      HeapVarIdValue(srcId, this, _, posOpt)
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

    def nestedInside(outScope: Scope, astNode: Asts.Ast, objInitializedHereOpt: Option[IdValue] = None): Scope =
      nestedInsideNodeOpt(outScope, Some(astNode), objInitializedHereOpt)

    def nestedInsideNodeOpt(outScope: Scope, astNodeOpt: Option[Asts.Ast], objInitializedHereOpt: Option[IdValue] = None): Scope = {
      val newScope = new Scope(Some(outScope), outScope.valuesCtx.withOneMoreFrame, objInitializedHereOpt)
      astNodeOpt.foreach { astNode =>
        newScope.setAstNode(astNode)
      }
      newScope
    }

    def root(globalValuesCtx: GlobalValuesContext): Scope =
      new Scope(None, globalValuesCtx, None)

    private val scopeUidGen = new AtomicLong(-1)

    final class RealInstrIter(scope: Scope) extends Iterator[RealInstr] {
      private var nextIdx = 0

      override def hasNext: Boolean = {
        skipPseudoInstr()
        nextIdx < scope.instructions.size
      }

      override def next(): RealInstr = {
        skipPseudoInstr()
        val result = scope.instructions(nextIdx)
        nextIdx += 1
        result.asInstanceOf[RealInstr]
      }

      def insertPseudoInstr(pseudoInstr: PseudoInstr): Unit = {
        scope.instructions.insert(nextIdx, pseudoInstr)
      }

      private def skipPseudoInstr(): Unit = {
        while (nextIdx < scope.instructions.size && scope.instructions(nextIdx).isInstanceOf[PseudoInstr]) {
          nextIdx += 1
        }
      }
    }

  }

  sealed trait PseudoInstr extends Instr
  final case class LocalDecl(localId: FunOrVarId, tpe: Type) extends PseudoInstr
  final case class Smartcast(subject: EClass.Id, tpe: Type, eGraphSnapshot: EGraph) extends PseudoInstr

}
