package compiler.typing.phases

import compiler.irs.ircorne.IRcorne
import compiler.irs.ircorne.IRcorne.AssigningInstr
import compiler.lang.FunctionSignature
import compiler.lang.Types.PrimitiveType.{BoolType, NullType, UnitType}
import compiler.lang.Types.Type
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reasoning.*
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.*
import compiler.typing.contexts.*
import compiler.valproxies.{BranchingInfo, ProxyStore}
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeChecker(
                         ihm: IntHandlingMode[?],
                         typeVarsCtx: TypeVariablesContext,
                         proxyStore: ProxyStore,
                         typeCandidatesStore: TypeCandidatesStore,
                         heapVarsTypeStore: HeapVarsTypeStore,
                         er: ErrorReporter,
                         counterExBoxOpt: Option[CounterexampleBox],
                         handleErrors: ErrorReporter => Unit = _.displayAndTerminateIfErrors()
                       ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = TypeChecking

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input

    given globalValsCtx: GlobalValuesContext = program.globalValuesContext

    given dealiasingCtx: DealiasingContext = DealiasingContext(program.typeAliases)

    val resolCtx = ResolutionContext(program, er)

    Reasoning.usingFreshReasoningToolkit(ihm, dealiasingCtx, resolCtx, proxyStore, program.globalValuesContext, counterExBoxOpt) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, globalValsCtx, er, counterExBoxOpt)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>

      saveTypesOfGlobalConstants(resolCtx, proxyStore, solver, simplifier)

      for {
        ((ownerId, funId), func) <- program.functions
        funSig <- resolCtx.resolveFunSig(ownerId, funId)(using subtypingCtx).asOption
        if !funSig.isSyntheticAccessor
      } {
        checkFunc(funSig, func, resolCtx, subtypingCtx, meetJoin, heapVarsTypeStore, solver, simplifier, absInt)
      }

      typeVarsCtx.checkAllTypeVariablesHaveBeenResolved(
        Typer(None, dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er),
        er
      )
    }

    handleErrors(er)
    input
  }

  private def saveTypesOfGlobalConstants(resolCtx: ResolutionContext, proxyStore: ProxyStore, solver: Solver, simplifier: Simplifier)
                                        (using globalValsCtx: GlobalValuesContext, dealiasingCtx: DealiasingContext): Unit = {

    // @formatter:off
    given TypeParamsContext = TypeParamsContext.empty
    given ResolutionContext = resolCtx
    given ProxyStore = proxyStore
    given Solver = solver
    given Simplifier = simplifier
    // @formatter:on

    globalValsCtx.globalScope.saveType(globalValsCtx.unitVal, UnitType)
    globalValsCtx.globalScope.saveType(globalValsCtx.trueVal, BoolType)
    globalValsCtx.globalScope.saveType(globalValsCtx.falseVal, BoolType)
    globalValsCtx.globalScope.saveType(globalValsCtx.nullVal, NullType)
  }

  private def checkFunc(
                         funSig: FunctionSignature,
                         func: IRcorne.Function,
                         resolCtx: ResolutionContext,
                         subtypingCtx: SubtypingContext,
                         meetJoin: MeetJoinComputer,
                         heapVarsTypeStore: HeapVarsTypeStore,
                         solver: Solver,
                         simplifier: Simplifier,
                         absInt: AbstractInterpreter
                       )(using globalValsCtx: GlobalValuesContext, dealiasingCtx: DealiasingContext): Unit =
    func.bodyOpt.foreach { funcBody =>

      val closuresCollector = mutable.Queue.empty[ClosureInfo]
      val funcTyper = Typer(Some(funSig), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin,
        proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er, closuresCollector.enqueue)
      val ownerSig = resolCtx.resolveTypeSig(funSig.ownerName).get
      val precondInfos = funSig.precondOpt match {
        case Some(precond) =>
          val (infosIfPrecondTrue, _) = proxyStore.rawInfosFor(precond, funSig.sigScope)(using dealiasingCtx)
          infosIfPrecondTrue
        case None => BranchingInfo.empty
      }
      solver.onNewFrame {
        for ((paramVal, paramType) <- funSig.paramsInclThis) {
          solver.takeType(paramVal, dealiasingCtx.dealiasType(paramType).withTypeVarsExpanded)
        }
        funcTyper.typeScopeInstructions(funcBody, precondInfos)(using TypeParamsContext(ownerSig.typeParams ++ funSig.typeParams))
      }
      checkReturns(funSig.retType, funcBody.hasExited, funcBody.getPosition, "method")

      while (closuresCollector.nonEmpty) {
        val closureInfo@ClosureInfo(closureParams, closureBody, closureRetType, branchingInfo, requiresPurityInBody, containingFunction, typeParamsCtx) = closuresCollector.dequeue()
        val closureTyper = Typer(Some(closureInfo), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin,
          proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er, closuresCollector.enqueue)
        solver.onNewFrame {
          for ((paramVal, paramType) <- closureParams) {
            solver.takeType(paramVal, dealiasingCtx.dealiasType(paramType.withTypeVarsExpanded))
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
