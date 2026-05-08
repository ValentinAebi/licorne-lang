package compiler.typing.phases

import compiler.pipeline.CompilationStep.DeclarationsAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.{IntHandlingMode, MeetJoinComputer, Reasoning}
import compiler.typing.{HeapVarsTypeStore, SubtypingInfo, TypeHintsStore, Typer}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeParamsContext, TypeVariablesContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

final class DeclarationsChecker(
                                 ihm: IntHandlingMode[?],
                                 typeVarsCtx: TypeVariablesContext,
                                 proxyStore: ProxyStore,
                                 typeHintsStore: TypeHintsStore,
                                 heapVarsTypeStore: HeapVarsTypeStore,
                                 er: ErrorReporter
                               ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = DeclarationsAnalysis

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input
    
    given globalValsCtx: GlobalValuesContext = program.globalValuesContext

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val resolCtx = ResolutionContext(program, er)

    Reasoning.usingFreshReasoningToolkit(ihm, dealiasingCtx, resolCtx, proxyStore, program.globalValuesContext) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, globalValsCtx, er)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>

      // save types of objects
      val globalValsCtx = program.globalValuesContext
      val globalScope = globalValsCtx.globalScope
      for ((objectId, objectSig) <- program.objects) {
        val objVal = globalValsCtx.resolveObject(objectId)
        globalScope.saveType(objVal, objectSig.toType(Map.empty))(using TypeParamsContext.empty, simplifier, resolCtx, proxyStore)
      }

      val typer = Typer(None, dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeHintsStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er)

      for ((_, interfaceSig) <- program.interfaces) {
        typer.typeInterfaceSig(interfaceSig)
      }
      for ((_, classSig) <- program.classes) {
        typer.typeClassSig(classSig)
      }
      for ((_, objectSig) <- program.objects) {
        typer.typeObjectSig(objectSig)
      }
      for ((_, datatypeSig) <- program.datatypes) {
        typer.typeDatatypeSig(datatypeSig)
      }
      for ((_, recordSig) <- program.records) {
        typer.typeRecordSig(recordSig)
      }

      er.displayAndTerminateIfErrors()
      input
    }
  }

}
