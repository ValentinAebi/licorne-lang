package compiler.typing.phases

import compiler.pipeline.CompilationStep.DeclarationsAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.{CounterexampleBox, IntHandlingMode, MeetJoinComputer, Reasoning}
import compiler.typing.{HeapVarsTypeStore, SubtypingInfo, TypeCandidatesStore, Typer}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeParamsContext, TypeVariablesContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

final class DeclarationsChecker(
                                 ihm: IntHandlingMode[?],
                                 typeVarsCtx: TypeVariablesContext,
                                 proxyStore: ProxyStore,
                                 typeCandidatesStore: TypeCandidatesStore,
                                 heapVarsTypeStore: HeapVarsTypeStore,
                                 er: ErrorReporter,
                                 counterExBoxOpt: Option[CounterexampleBox]
                               ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = DeclarationsAnalysis

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (programOld, subtypingInfo@SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input

    given globalValsCtx: GlobalValuesContext = programOld.globalValuesContext

    val dealiasingCtx = DealiasingContext(programOld.typeAliases)
    val resolCtx = ResolutionContext(programOld, er)

    Reasoning.usingFreshReasoningToolkit(ihm, dealiasingCtx, resolCtx, proxyStore, programOld.globalValuesContext, counterExBoxOpt) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, globalValsCtx, er, counterExBoxOpt)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>

      val typer = Typer(None, dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er)

      val programNew = Program(globalValsCtx,
        for ((id, interfaceSig) <- programOld.interfaces) yield {
          id -> typer.typeInterfaceSig(interfaceSig)
        },
        for ((id, classSig) <- programOld.classes) yield {
          id -> typer.typeClassSig(classSig)
        },
        for ((id, objectSig) <- programOld.objects) yield {
          id -> typer.typeObjectSig(objectSig)
        },
        for ((id, datatypeSig) <- programOld.datatypes) yield {
          id -> typer.typeDatatypeSig(datatypeSig)
        },
        for ((id, recordSig) <- programOld.records) yield {
          id -> typer.typeRecordSig(recordSig)
        },
        programOld.typeAliases,
        programOld.functions,
        programOld.loops
      )

      er.displayAndTerminateIfErrors()
      (programNew, subtypingInfo)
    }
  }

}
