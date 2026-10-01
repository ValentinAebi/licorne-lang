package compiler.typing.phases

import compiler.irs.ircorne.Formulas.FunCall
import compiler.irs.ircorne.{FieldResolutionTarget, Formulas, IRcorne, InvocationTarget}
import compiler.irs.ircorne.IRcorne.AssigningInstr
import compiler.lang.Field.StableField
import compiler.lang.{FunctionDescriptor, FunctionSignature, RuntimeTypeSignature, UserInstantiableTypeSig}
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
        ((ownerId, funDescr), func) <- program.functions
      } {
        val funSig = resolCtx.forceGetFunction(ownerId, funDescr)
        if (!funSig.isSyntheticAccessor) {
          checkFunc(funSig, func, resolCtx, subtypingCtx, meetJoin, heapVarsTypeStore, solver, simplifier, absInt)
        }
      }

      typeVarsCtx.checkAllTypeVariablesHaveBeenResolved(
        Typer(None, dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er, None),
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
        proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er, Some(closuresCollector.enqueue(_)))
      val ownerSig = resolCtx.resolveTypeSigAs(funSig.ownerName).get

      given TypeParamsContext = TypeParamsContext(ownerSig.typeParams ++ funSig.typeParams)

      given ResolutionContext = resolCtx

      given Simplifier = simplifier

      val precondInfos = funSig.precondOpt match {
        case Some(precond) =>
          val (infosIfPrecondTrue, _) = proxyStore.rawInfosFor(precond, funSig.sigScope)
          infosIfPrecondTrue
        case None => BranchingInfo.empty
      }
      solver.onNewFrame {
        ownerSig match {
          case ownerSig: UserInstantiableTypeSig =>
            ownerSig.encapsulatedFields.foreach {
              case (_, StableField(fldId, fldType, fldVal, isPublishedAsMethod, Some(initializer))) =>
                val thisVal = funSig.sigScope.getLocalValuesContextUnsafe.getThisValue.get
                val invkTarget = InvocationTarget(fldId)
                val accessorFunSig = resolCtx.forceGetFunction(ownerSig.id, FunctionDescriptor(fldId, 0))
                invkTarget.resolve(ownerSig, accessorFunSig, fldType)
                val accessorCall = FunCall(thisVal, invkTarget, List.empty, List.empty)
                solver.assertEq(accessorCall, initializer, SimplifiedType.from(fldType))
                funSig.sigScope.eMerge(accessorCall, initializer)
              case _ => ()
            }
          case _ => ()
        }
        for ((paramVal, paramType) <- funSig.paramsInclThis) {
          solver.takeType(paramVal, dealiasingCtx.dealiasType(paramType).withTypeVarsExpanded)
        }
        funcTyper.typeScopeInstructions(funcBody, precondInfos)
        checkReturns(funSig.retType, funcBody.hasExited, funcBody.getPosition, "method")

        while (closuresCollector.nonEmpty) {
          val closureInfo@ClosureInfo(closureParams, closureBody, closureRetType, branchingInfo, requiresPurityInBody, typeParamsCtx) = closuresCollector.dequeue()
          val closureTyper = Typer(Some(closureInfo), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin,
            proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er, Some(closuresCollector.enqueue(_)))
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
    }

  private def checkReturns(retType: Type, bodyHasExited: Boolean, posOpt: Option[Position], methodOrClosure: String): Unit = {
    if (retType != UnitType && !bodyHasExited) {
      er.reportError(s"missing return in non-$UnitType $methodOrClosure", posOpt)
    }
  }

}
