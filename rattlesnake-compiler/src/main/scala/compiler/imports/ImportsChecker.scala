package compiler.imports

import compiler.irs.asts.Asts
import compiler.irs.asts.Asts.ImportStat
import compiler.lang.ObjectSignature
import compiler.pipeline.CompilationStep.ImportsAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.Reasoning
import compiler.typing.SubtypingInfo
import compiler.typing.contexts.ResolutionContext.FuncResolResult
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeVariablesContext}
import compiler.valproxies.ProxyStore

final class ImportsChecker(proxyStore: ProxyStore, typeVarsCtx: TypeVariablesContext, er: ErrorReporter) extends CompilerStep[(Program, SubtypingInfo, List[ImportStat]), (Program, SubtypingInfo)] {

  private given CompilationStep = ImportsAnalysis

  override def apply(input: (Program, SubtypingInfo, List[ImportStat])): (Program, SubtypingInfo) = {
    val (program, subtypingInfo@SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions), imports) = input
    val dealiasingCtx = DealiasingContext(program.typeAliases)
    Reasoning.usingFreshSolver(dealiasingCtx, proxyStore) { solver =>
      val resolCtx = ResolutionContext(program, typeVarsCtx, er)
      val subtypingCtx = SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, er)
      for (imp <- imports) {
        checkImport(imp)(using resolCtx, subtypingCtx)
      }
    }
    er.displayAndTerminateIfErrors()
    (program, subtypingInfo)
  }

  private def checkImport(importStat: ImportStat)(using resolCtx: ResolutionContext, subtypingCtx: SubtypingContext): Unit = importStat match {
    case Asts.FunctionImportStat(receiverObj, funId, aliasOpt) =>
      resolCtx.resolveFunSig(receiverObj, funId) match {
        case FuncResolResult.OwnerNotFound =>
          er.reportError(s"type not found: $receiverObj", importStat.getPosition)
        case FuncResolResult.FuncNotFound(ownerSig) =>
          er.reportError(s"method not found: $receiverObj.$funId", importStat.getPosition)
        case FuncResolResult.Success(ownerSig: ObjectSignature, funSig) => ()
        case FuncResolResult.Success(ownerSig, funSig) =>
          er.reportError(s"$ownerSig is not an object", importStat.getPosition)
      }
    case Asts.TypeImportStat(imported, aliasOpt) =>
      resolCtx.resolveTypeSig(imported) match {
        case None =>
          er.reportError(s"type not found: $imported", importStat.getPosition)
        case Some(sig) => ()
      }
  }

}
