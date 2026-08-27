package compiler.irs.ssa

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.asts.Asts
import compiler.irs.asts.Asts.Ast
import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.SSA.HybridCastMode.{AssertNonNull, AssertPredicate}
import compiler.irs.ssa.SSA.Scope.scopeUidGen
import compiler.lang.*
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.pipeline.CompilationStep
import compiler.reasoning.{Recurrence, Simplifier, Solver}
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, TypeParamsContext}
import compiler.typing.smartcasting.egraphs.EGraph
import compiler.util.SeqSet
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext, ValuesContext}

import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable
import scala.compiletime.uninitialized

object SSA {

  sealed abstract class Instr {
    private var astNodeOpt: Option[Ast] = None
    private var idxInScopeOpt: Option[Int] = None
    
    {
      for (idVal <- consumedVals) {
        idVal.users.addOne(this)
      }
    }

    def setAstNode(astNode: Ast): this.type = {
      if (this.astNodeOpt.isDefined) {
        throw IllegalStateException("node has already been set")
      }
      this.astNodeOpt = Some(astNode)
      this
    }

    def getAstNodeOpt: Option[Ast] = astNodeOpt

    def getPosition: Option[Position] = getAstNodeOpt.flatMap(_.getPosition)
    
    def setIdxInScope(idx: Int): Unit = {
      if (idxInScopeOpt.isDefined) {
        throw IllegalStateException("index in scope already set")
      }
      idxInScopeOpt = Some(idx)
    }
    
    def getIdxInScopeOpt: Option[Int] = idxInScopeOpt

    def consumedVals: List[IdValue]
    
    def producedValOpt: Option[IdValue] = this match {
      case assign: AssigningInstr => Some(assign.assigned)
      case _ => None
    }

    def freeVals: SeqSet[IdValue] = this match {
      case mkClosure@MkClosure(assigned, params, body, isPure) =>
        val paramsSet = params.map(_._1).toSet[IdValue]
        body.freeVals.filter(!paramsSet.contains(_))
      case _ =>
        val prodOpt = producedValOpt
        SeqSet(consumedVals.filterNot(prodOpt.contains))
    }
    
    def children: List[Instr]
  }

  final case class Function(owner: TypeIdentifier, funId: FunOrVarId, bodyOpt: Option[Scope]) {
    private val scopes = mutable.ListBuffer.empty[Scope]

    bodyOpt.foreach { body =>
      body.setEnclosingFunction(this)
    }

    def scopesView: Iterable[Scope] = scopes

    private[SSA] def addScope(scope: Scope): Unit = {
      scopes.addOne(scope)
    }
  }

  trait VarData

  final case class LoopVarData(varId: FunOrVarId, beforeLoopVal: IdValue, inCondVal: VarIdValue, bodyLastVal: VarIdValue, varDefScope: Scope) extends VarData {
    var recurrenceOpt: Option[Recurrence] = None

    def recurDescr: String = {
      recurrenceOpt match {
        case Some(recurrence) =>
          s"RECUR: $recurrence"
        case None => ""
      }
    }

    override def toString: String = {
      val baseStr = s"$varId: $beforeLoopVal ; ($inCondVal) { ... $bodyLastVal }"
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

  sealed abstract class RealInstr extends Instr

  sealed trait ScopeEndingInstr {
    this: Instr =>
  }

  sealed trait PureInstr {
    this: Instr =>
  }

  sealed trait ConsumesNoVal {
    this: Instr =>
    override final def consumedVals: List[IdValue] = List.empty
  }
  
  sealed trait NoChildren {
    this: Instr =>
    override def children: List[Instr] = List.empty
  }

  sealed trait ControlFlowInstr extends RealInstr

  final case class Loop(cond: Scope, condVal: IdValue, body: Scope, variables: List[LoopVarData]) extends ControlFlowInstr {
    override def consumedVals: List[IdValue] = List(condVal)

    override def children: List[Instr] = List(cond, body)
  }

  final case class Disjunction(condVal: IdValue, thenBr: Scope, elseBr: Scope, variables: List[DisjunctionVarData]) extends ControlFlowInstr {
    override def consumedVals: List[IdValue] = List(condVal)

    override def children: List[Instr] = List(thenBr, elseBr)
  }

  // TODO maybe this should become a PseudoInstr?
  final case class StaticTypeAssert(value: IdValue, var tpe: Type) extends RealInstr, PureInstr, NoChildren {
    override def consumedVals: List[IdValue] = List.empty
  }

  sealed trait AssigningInstr extends RealInstr {
    val assigned: IdValue
  }

  sealed trait UnaryOp extends NoChildren {
    this: AssigningInstr =>

    def operand: IdValue

    override def consumedVals: List[IdValue] = List(operand)
  }

  sealed trait BinaryOp extends NoChildren {
    this: AssigningInstr =>

    def lhs: IdValue

    def rhs: IdValue

    override def consumedVals: List[IdValue] = List(lhs, rhs)
  }

  final case class AssignVal(assigned: IdValue, src: IdValue) extends AssigningInstr, PureInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(src)
  }

  final case class AssignIntConst(assigned: IdValue, src: Int) extends AssigningInstr, PureInstr, ConsumesNoVal, NoChildren

  final case class AssignBoolConst(assigned: IdValue, src: Boolean) extends AssigningInstr, PureInstr, ConsumesNoVal, NoChildren

  final case class AssignStringConst(assigned: IdValue, src: String) extends AssigningInstr, PureInstr, ConsumesNoVal, NoChildren

  final case class NumNeg(assigned: IdValue, operand: IdValue) extends AssigningInstr, PureInstr, UnaryOp

  final case class Add(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class Sub(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class Mul(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class Div(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class Rem(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class LogicNeg(assigned: IdValue, operand: IdValue) extends AssigningInstr, PureInstr, UnaryOp

  final case class And(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class Or(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class Equal(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class Leq(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class Lt(assigned: IdValue, lhs: IdValue, rhs: IdValue) extends AssigningInstr, PureInstr, BinaryOp

  final case class FieldRead(assigned: IdValue, owner: IdValue, var field: FieldResolutionTarget) extends AssigningInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(owner)
  }

  final case class HeapVarRead(assigned: IdValue, heapVar: HeapVarIdValue) extends AssigningInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(heapVar)
  }

  final case class InvokeFunc(assigned: IdValue, receiver: IdValue, var func: InvocationTarget, var typeArgs: List[Type], args: List[IdValue]) extends AssigningInstr, NoChildren {
    override def consumedVals: List[IdValue] = receiver :: args
  }

  final case class InvokeClosure(assigned: IdValue, callee: IdValue, closureTypingTarget: ClosureTypingTarget, args: List[IdValue]) extends AssigningInstr, NoChildren {
    override def consumedVals: List[IdValue] = callee :: args
  }

  final case class Instantiate(assigned: IdValue, classOrRecordName: TypeIdentifier, var typeArgs: List[Type], fieldsInit: List[(FunOrVarId, IdValue)]) extends AssigningInstr, NoChildren {
    private var outType: Option[Type] = None
    
    def resolveOutType(tpe: Type): Unit = {
      outType = Some(tpe)
    }
    
    def getOutType: Type = outType.get

    override def consumedVals: List[IdValue] = fieldsInit.map(_._2)
  }

  final case class MkClosure(assigned: IdValue, params: List[(ParamIdValue, Type)], body: Scope, var isPure: Boolean) extends AssigningInstr, ConsumesNoVal {
    override def children: List[Instr] = List(body)
  }

  final case class MkHeapVar(assigned: HeapVarIdValue) extends AssigningInstr, ConsumesNoVal, NoChildren

  final case class TypeTest(assigned: IdValue, testedValue: IdValue, testedTypeId: TypeIdentifier) extends AssigningInstr, PureInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(testedValue)
  }

  final case class Conversion(assigned: IdValue, inValue: IdValue, targetType: PrimitiveType) extends AssigningInstr, PureInstr, NoChildren {
    private var tConvOpt: Option[Option[TypeConversion]] = None
    
    def resolveTypeConversion(tcOpt: Option[TypeConversion]): Unit = {
      tConvOpt = Some(tcOpt)
    }

    def forceGetTypeConversion: Option[TypeConversion] = tConvOpt.get

    override def consumedVals: List[IdValue] = List(inValue)
  }

  final case class FieldWrite(owner: IdValue, var field: FieldResolutionTarget, rhs: IdValue) extends RealInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(owner, rhs)
  }

  final case class HeapVarWrite(heapVar: HeapVarIdValue, newValue: IdValue) extends RealInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(heapVar, newValue)
  }

  final case class Return(retVal: IdValue) extends RealInstr, ScopeEndingInstr, PureInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(retVal)
  }

  final case class Panic(msg: IdValue) extends RealInstr, ScopeEndingInstr, PureInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(msg)
  }

  final case class Cast(inValue: IdValue, target: TypeIdentifier) extends RealInstr, PureInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(inValue)
  }

  final case class HybridCast(inValue: IdValue) extends RealInstr, PureInstr, NoChildren {
    private var modeOpt = Option.empty[HybridCastMode]

    def setMode(mode: HybridCastMode): Unit = {
      modeOpt = Some(mode)
    }

    def isNonNullAssertion: Boolean = modeOpt.contains(AssertNonNull)

    def getTargetRefinement: Option[Formula] = modeOpt.flatMap {
      case AssertNonNull => None
      case AssertPredicate(newPredicate) => Some(newPredicate)
    }

    override def consumedVals: List[IdValue] = List.empty
  }

  final case class Drop(droppedValue: IdValue) extends RealInstr, PureInstr, NoChildren {
    override def consumedVals: List[IdValue] = List(droppedValue)
  }

  final case class LocalDecl(localId: FunOrVarId, var tpe: Type) extends RealInstr, ConsumesNoVal, NoChildren

  final class Scope private(
                             val outScopeOpt: Option[Scope],
                             val valuesCtx: ValuesContext,
                             private val proxyStore: ProxyStore
                           ) extends RealInstr {
    private var enclosingFunctionOpt = Option.empty[Function]

    private val types = mutable.Map.empty[IdValue, Type]

    /**
     * WARNING: To be used only by Typer, might contain incorrect data during later phases because of insertion of
     * smartcasts in the middle of scopes
     */
    private var smartcastsEGraphOpt = Option.empty[EGraph]

    export valuesCtx.globalCtx as globalValuesCtx

    val instructions: mutable.ListBuffer[Instr] = mutable.ListBuffer.empty[Instr]

    override def children: List[Instr] = instructions.toList

    val depth: Int = outScopeOpt match {
      case Some(outScope) => outScope.depth + 1
      case None => 0
    }

    private val uidGen = AtomicLong(-1)
    private val valuesDefinedHere = mutable.LinkedHashSet.empty[IdValue]

    val scopeUid: Long = scopeUidGen.incrementAndGet()

    private val _persistingEqualities = mutable.ListBuffer.empty[(Formula, Formula)]

    private var realInstrIterOpt = Option.empty[Scope.RealInstrIter]

    def setEnclosingFunction(func: Function): Unit = {
      if (enclosingFunctionOpt.isDefined) {
        throw IllegalStateException("enclosing function set more than once for the same scope")
      }
      enclosingFunctionOpt = Some(func)
      func.addScope(this)
    }

    def forTraversal[T](action: Scope.RealInstrIter => T): T = {
      if (realInstrIterOpt.isDefined) {
        throw IllegalStateException(s"another traversal of $this is already underway")
      }
      val iter = Scope.RealInstrIter(this)
      realInstrIterOpt = Some(iter)
      val result = try {
        action(iter)
      } finally {
        realInstrIterOpt = None
      }
      result
    }

    def insertInstrDuringTraversal(instr: Instr): Unit = {
      realInstrIterOpt match {
        case None =>
          throw IllegalStateException(s"no traversal is currently underway for scope $scopeUid")
        case Some(iter) =>
          iter.insertInstr(instr)
      }
    }

    def persistingEqualities: Iterable[(Formula, Formula)] = _persistingEqualities

    def eMerge(f1: Formula, f2: Formula, persist: Boolean = false)(using typeParamsCtx: TypeParamsContext, resolCtx: ResolutionContext, simplifier: Simplifier): Unit = {
      smartcastsEGraph.merge(f1, f2)(using typeParamsCtx, resolCtx, proxyStore)
      if (persist) {
        outScopeOpt.foreach { outScope =>
          outScope.eMerge(f1, f2)
        }
        _persistingEqualities.addOne((f1, f2))
      }
    }

    def isNestedIn(outerScope: Scope): Boolean =
      outerScope.depth < this.depth && (
        outScopeOpt.contains(outerScope) ||
          (outScopeOpt.isDefined && outScopeOpt.get.isNestedIn(outerScope)))

    def saveType(idVal: IdValue, rawType: Type, allowOverwrite: Boolean = false)
                (using tpCtx: TypeParamsContext, dealiasingCtx: DealiasingContext, simplifier: Simplifier, resolCtx: ResolutionContext, proxyStore: ProxyStore, solver: Solver, globalValsCtx: GlobalValuesContext): Unit = {
      val tpe = rawType.withDependenciesTransformed(d => proxyStore.developNearest(d).getOrElse(d))
      smartcastsEGraph.saveSmartcast(idVal, tpe)
      if (idVal.definingScope == this) {
        if (!allowOverwrite && types.contains(idVal)) {
          throw IllegalStateException(s"$idVal has already been assigned a type")
        }
        types.put(idVal, tpe)
      } else if (idVal.definingScope.depth < this.depth && outScopeOpt.isDefined) {
        outScopeOpt.get.saveType(idVal, tpe.filtered(idVal, Some(this, proxyStore))(using getLocalValuesContextUnsafe.globalCtx), allowOverwrite)
      } else {
        throw IllegalArgumentException(s"illegal type save: $idVal in $this")
      }
      solver.takeType(idVal, tpe)
      tpe match {
        case ClosureType(params, result, enforcedPure) if enforcedPure =>
          proxyStore.validateClosurePurity(idVal)
        case _ => ()
      }
    }

    def saveSmartcast(f: Formula, smartcastType: Type): Unit = {
      smartcastsEGraph.saveSmartcast(f, smartcastType)
    }

    def saveNonNull(f: Formula): Unit = {
      smartcastsEGraph.saveNonNull(f)
    }

    def getCurrentTypeOf(formula: Formula)(using ProxyStore, Simplifier, TypeParamsContext): Type = {
      val maybeNullableType = smartcastFor(formula)
        .orElse(typeOfNoSmartcastIfIdVal(formula))
        .getOrElse(NothingType)
      maybeNullableType match {
        case NullableType(nullatedType) if smartcastsEGraph.isKnownNonNull(formula) => nullatedType
        case nonNullableType => nonNullableType
      }
    }

    def absorbSmartcastsEGraphFrom(src: Scope): Unit = {
      smartcastsEGraphOpt = src.smartcastsEGraphOpt
    }

    def smartcastFor(f: Formula)(using Simplifier, TypeParamsContext): Option[Type] = {
      smartcastsEGraph.smartcastFor(f) match {
        case someType@Some(_) => someType
        case None => None
      }
    }

    private def smartcastsEGraph: EGraph = smartcastsEGraphOpt match {
      case Some(eGraph) => eGraph
      case None =>
        val eGraph = outScopeOpt match {
          case Some(outEGraph) => outEGraph.smartcastsEGraph.deepCopy
          case None => EGraph.newEmpty
        }
        smartcastsEGraphOpt = Some(eGraph)
        eGraph
    }

    def typeOfNoSmartcastIfIdVal(f: Formula): Option[Type] = f match {
      case f: IdValue => typeOfNoSmartcast(f)
      case _ => None
    }

    def typeOfNoSmartcast(idValue: IdValue): Option[Type] = {
      types.get(idValue).orElse {
        outScopeOpt.flatMap(_.typeOfNoSmartcast(idValue))
      }
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

    override def consumedVals: List[IdValue] = List.empty
    
    def writeInstrIndices(): Unit = {
      for ((instr, idx) <- instructions.zipWithIndex) {
        instr.setIdxInScope(idx)
      }
    }

    def newParam(srcId: FunOrVarId, posOpt: Option[Position]): ParamIdValue = newValue {
      ParamIdValue(srcId, this, _, posOpt)
    }

    def newVal(srcId: FunOrVarId, posOpt: Option[Position]): ValIdValue = newValue {
      ValIdValue(srcId, this, _, posOpt)
    }

    def newVar(srcId: FunOrVarId, declOpt: Option[LocalDecl], descrOpt: Option[String], posOpt: Option[Position]): VarIdValue = newValue {
      VarIdValue(srcId, declOpt, this, _, descrOpt, posOpt)
    }

    def newHeapVar(srcId: FunOrVarId, posOpt: Option[Position]): HeapVarIdValue = newValue {
      HeapVarIdValue(srcId, this, _, posOpt)
    }

    def newIntermediate(nameHint: String, allocMode: AllocMode): IntermediateIdValue = newValue {
      IntermediateIdValue(this, _, nameHint, allocMode)
    }

    def newUninterpretedConst(name: String): UninterpretedConstIdValue = newValue {
      UninterpretedConstIdValue(name, this, _)
    }

    private def newValue[T <: IdValue](creation: Long => T): T = {
      val value = creation(uidGen.incrementAndGet())
      valuesDefinedHere.add(value)
      value
    }

  }

  object Scope {

    def nestedInside(outScope: Scope, astNode: Asts.Ast): Scope =
      nestedInsideNodeOpt(outScope, Some(astNode))

    def nestedInsideNodeOpt(outScope: Scope, astNodeOpt: Option[Asts.Ast]): Scope = {
      val newScope = new Scope(Some(outScope), outScope.valuesCtx.withOneMoreFrame, outScope.proxyStore)
      astNodeOpt.foreach { astNode =>
        newScope.setAstNode(astNode)
      }
      outScope.enclosingFunctionOpt.foreach { enclosingFunc =>
        newScope.setEnclosingFunction(enclosingFunc)
      }
      newScope
    }

    def root(globalValuesCtx: GlobalValuesContext): Scope =
      new Scope(None, globalValuesCtx, globalValuesCtx.proxyStore)

    private val scopeUidGen = new AtomicLong(-1)

    final class RealInstrIter(scope: Scope) extends Iterator[RealInstr] {
      private var nextIdx = 0

      override def hasNext: Boolean = {
        skipPseudoInstr()
        nextIdx < scope.instructions.size
      }

      override def next(): RealInstr = {
        skipPseudoInstr()
        val result = scope.instructions(nextIdx).asInstanceOf[RealInstr]
        nextIdx += 1
        result
      }

      def insertInstr(instr: Instr): Unit = {
        scope.instructions.insert(nextIdx, instr)
        nextIdx += 1
      }

      private def skipPseudoInstr(): Unit = {
        while (nextIdx < scope.instructions.size && scope.instructions(nextIdx).isInstanceOf[PseudoInstr]) {
          nextIdx += 1
        }
      }
    }

  }

  sealed trait PseudoInstr extends Instr

  final case class Unreachable() extends PseudoInstr, ScopeEndingInstr, ConsumesNoVal, NoChildren

  enum HybridCastMode {
    case AssertNonNull
    case AssertPredicate(newPredicate: Formula)
  }

}
