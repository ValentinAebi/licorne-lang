package compiler.typing.phases

import compiler.irs.SSA
import compiler.lang.FunctionSignature
import compiler.lang.Types.PrimitiveType.{BoolType, UnitType}
import compiler.lang.Types.{IntRangeType, Type}
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.smt.{AbstractInterpreter, Reasoning, Simplifier, Solver}
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
                       ) extends CompilerStep[(Program, SubtypingInfo), Program] {

  private given CompilationStep = TypeChecking

  override def apply(input: (Program, SubtypingInfo)): Program = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val resolCtx = ResolutionContext(program, typeVarsCtx, er)

    Reasoning.usingFreshReasoningToolkit { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, er)
    } { (solver, subtypingCtx, simplifier, absInt) =>

      saveTypesOfGlobalConstants(program.globalValuesContext, resolCtx, proxyStore)

      val meetJoin = MeetJoinComputer(dealiasingCtx, resolCtx, subtypingCtx, simplifier, solver)
      for ((funSig, func) <- program.functions) {
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
    program
  }

  // TODO check that user-provided assignments of type parameters match bounds

  private def saveTypesOfGlobalConstants(globalValsCtx: GlobalValuesContext, resolCtx: ResolutionContext, proxyStore: ProxyStore): Unit = {

    // @formatter:off
    given TypeParamsContext = TypeParamsContext.empty
    given ResolutionContext = resolCtx
    given ProxyStore = proxyStore
    // @formatter:on

    globalValsCtx.globalScope.saveType(globalValsCtx.unitVal, UnitType)
    globalValsCtx.globalScope.saveType(globalValsCtx.trueVal, BoolType)
    globalValsCtx.globalScope.saveType(globalValsCtx.falseVal, BoolType)
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
      val funcTyper = Typer(Some(funSig.retType), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin,
        proxyStore, typeHintsStore, heapVarsTypeStore, solver, simplifier, absInt, er, closuresCollector.enqueue)
      val ownerSig = resolCtx.resolveTypeSig(funSig.ownerName).get
      solver.onNewFrame {
        funSig.paramsInclThis.foreach {
          case (paramVal, range: IntRangeType) =>
            solver.assertInRange(paramVal, range)
          case _ => ()
        }
        funcTyper.typeScopeInstructions(funcBody, BranchingInfo.empty)(using TypeParamsContext(ownerSig.typeParams))
      }
      checkReturns(funSig.retType, funcBody.hasExited, funcBody.getPosition, "method")

      while (closuresCollector.nonEmpty) {
        val ClosureInfo(closureParams, closureBody, closureRetType, branchingInfo, typeParamsCtx) = closuresCollector.dequeue()
        val closureTyper = Typer(Some(closureRetType), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin,
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
