package compiler.typing.phases

import compiler.irs.ssa.SSA
import compiler.lang.FunctionSignature
import compiler.lang.Types.PrimitiveType.{BoolType, NullType, UnitType}
import compiler.lang.Types.{IntRangeType, Type}
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.smt.{AbstractInterpreter, MeetJoinComputer, Reasoning, Simplifier, Solver}
import compiler.typing.contexts.*
import compiler.typing.*
import compiler.valproxies.{BranchingInfo, ProxyStore}
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeChecker(
                         typeVarsCtx: TypeVariablesContext,
                         proxyStore: ProxyStore,
                         typeHintsStore: TypeHintsStore,
                         heapVarsTypeStore: HeapVarsTypeStore,
                         er: ErrorReporter,
                         continueIfErrors: Boolean = false
                       ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = TypeChecking

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val resolCtx = ResolutionContext(program, typeVarsCtx, er)

    Reasoning.usingFreshReasoningToolkit(dealiasingCtx, resolCtx, proxyStore) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, er)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>

      saveTypesOfGlobalConstants(program.globalValuesContext, resolCtx, proxyStore, simplifier)

      for {
        (funSig, func) <- program.functions
        if !funSig.isSynthetic
      } {
        checkFunc(funSig, func, dealiasingCtx, resolCtx, subtypingCtx, meetJoin, heapVarsTypeStore, solver, simplifier, absInt)
      }

      typeVarsCtx.checkAllTypeVariablesHaveBeenResolved(
        Typer(None, dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeHintsStore, heapVarsTypeStore, solver, simplifier, absInt, er),
        er
      )
    }

    if (continueIfErrors) {
      er.displayErrors()
    } else {
      er.displayAndTerminateIfErrors()
    }
    input
  }

  // TODO check that user-provided assignments of type parameters match bounds

  private def saveTypesOfGlobalConstants(globalValsCtx: GlobalValuesContext, resolCtx: ResolutionContext,
                                         proxyStore: ProxyStore, simplifier: Simplifier): Unit = {

    // @formatter:off
    given TypeParamsContext = TypeParamsContext.empty
    given ResolutionContext = resolCtx
    given ProxyStore = proxyStore
    given Simplifier = simplifier
    // @formatter:on

    globalValsCtx.globalScope.saveType(globalValsCtx.unitVal, UnitType)
    globalValsCtx.globalScope.saveType(globalValsCtx.trueVal, BoolType)
    globalValsCtx.globalScope.saveType(globalValsCtx.falseVal, BoolType)
    globalValsCtx.globalScope.saveType(globalValsCtx.nullVal, NullType)
  }

  private def checkFunc(
                         funSig: FunctionSignature,
                         func: SSA.Function,
                         dealiasingCtx: DealiasingContext,
                         resolCtx: ResolutionContext,
                         subtypingCtx: SubtypingContext,
                         meetJoin: MeetJoinComputer,
                         heapVarsTypeStore: HeapVarsTypeStore,
                         solver: Solver,
                         simplifier: Simplifier,
                         absInt: AbstractInterpreter
                       ): Unit =
    func.bodyOpt.foreach { funcBody =>
      val closuresCollector = mutable.Queue.empty[ClosureInfo]
      val funcTyper = Typer(Some(funSig), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin,
        proxyStore, typeHintsStore, heapVarsTypeStore, solver, simplifier, absInt, er, closuresCollector.enqueue)
      val ownerSig = resolCtx.resolveTypeSig(funSig.ownerName).get
      val precondInfos = funSig.precondOpt match {
        case Some(precond) =>
          val (infosIfPrecondTrue, _) = proxyStore.rawInfosFor(precond, funSig.sigScope)(using dealiasingCtx)
          infosIfPrecondTrue
        case None => BranchingInfo.empty
      }
      solver.onNewFrame {
        funSig.paramsInclThis.foreach {
          case (paramVal, range: IntRangeType) =>
            solver.assertInRange(paramVal, range)
          case _ => ()
        }
        funcTyper.typeScopeInstructions(funcBody, precondInfos)(using TypeParamsContext(ownerSig.typeParams))
      }
      checkReturns(funSig.retType, funcBody.hasExited, funcBody.getPosition, "method")

      while (closuresCollector.nonEmpty) {
        val closureInfo@ClosureInfo(closureParams, closureBody, closureRetType, branchingInfo, requiresPurityInBody, containingFunction, typeParamsCtx) = closuresCollector.dequeue()
        val closureTyper = Typer(Some(closureInfo), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin,
          proxyStore, typeHintsStore, heapVarsTypeStore, solver, simplifier, absInt, er, closuresCollector.enqueue)
        solver.onNewFrame {
          for ((paramVal, paramType) <- closureParams) {
            paramType.withTypeVarsExpanded match {
              case range: IntRangeType =>
                solver.assertInRange(paramVal, range)
              case _ => ()
            }
          }
          closureTyper.typeScopeInstructions(closureBody, branchingInfo)(using typeParamsCtx)
          if (!closureRetType.isResolved) {
            closureRetType.resolve(UnitType)
          }
        }
        checkReturns(closureRetType.withTypeVarsExpanded, closureBody.hasExited, closureBody.getPosition, "closure")
      }
    }

  private def checkReturns(retType: Type, bodyHasExited: Boolean, posOpt: Option[Position], methodOrClosure: String): Unit = {
    if (retType != UnitType && !bodyHasExited) {
      er.reportError(s"missing return in non-$UnitType $methodOrClosure", posOpt)
    }
  }

}
