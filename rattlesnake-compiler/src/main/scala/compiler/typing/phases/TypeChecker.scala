package compiler.typing.phases

import compiler.irs.SSA
import compiler.lang.FunctionSignature
import compiler.lang.Types.IntRangeType
import compiler.lang.Types.PrimitiveType.UnitType
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.{AbstractInterpreter, Reasoning, Simplifier, Solver}
import compiler.typing.contexts.*
import compiler.typing.{MeetJoinComputer, SubtypingInfo, TypeHintsStore, Typer}
import compiler.valproxies.{BranchingInfo, ProxyStore}

final class TypeChecker(
                         typeVarsCtx: TypeVariablesContext,
                         proxyStore: ProxyStore,
                         typeHintsStore: TypeHintsStore,
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

      val meetJoin = MeetJoinComputer(dealiasingCtx, resolCtx, subtypingCtx, simplifier, solver)
      for ((funSig, func) <- program.functions) {
        checkFunc(funSig, func, dealiasingCtx, resolCtx, subtypingCtx, meetJoin, solver, simplifier, absInt)
      }

      typeVarsCtx.checkAllTypeVariablesHaveBeenResolved(
        Typer(None, dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeHintsStore, solver, simplifier, absInt, er),
        er
      )
    }

    if (continueIfErrors){
      er.displayErrors()
    } else {
      er.displayAndTerminateIfErrors()
    }
    program
  }

  // TODO check that user-provided assignments of type parameters match bounds

  private def checkFunc(funSig: FunctionSignature, func: SSA.Function, dealiasingCtx: DealiasingContext, resolCtx: ResolutionContext, subtypingCtx: SubtypingContext, meetJoin: MeetJoinComputer, solver: Solver, simplifier: Simplifier, absInt: AbstractInterpreter): Unit =
    func.bodyOpt.foreach { body =>
      val typer = Typer(Some(funSig.retType), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeHintsStore, solver, simplifier, absInt, er)
      val ownerSig = resolCtx.resolveTypeSig(funSig.ownerName).get
      solver.onNewFrame {
        funSig.paramsInclThis.foreach {
          case (paramVal, IntRangeType(lowerBoundOpt, upperBoundOpt)) =>
            lowerBoundOpt.foreach { lb =>
              solver.assertLeq(lb, paramVal)
            }
            upperBoundOpt.foreach { ub =>
              solver.assertLeq(paramVal, ub)
            }
          case _ => ()
        }
        typer.typeScopeInstructions(body, BranchingInfo.empty)(using TypeParamsContext(ownerSig.typeParams))
      }
      if (funSig.retType != UnitType && !body.hasExited) {
        // TODO also check for closures
        er.reportError(s"cannot prove that method ${funSig.functionName} with non-$UnitType return type always returns", body.getPosition)
      }
    }

}
