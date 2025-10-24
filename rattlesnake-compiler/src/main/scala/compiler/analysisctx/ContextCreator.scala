package compiler.analysisctx

import compiler.importscanner.ModuleImports
import compiler.irs.Asts.*
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.ErrorReporter
import identifiers.TypeIdentifier

/**
 * Compiler pass to generate an [[AnalysisContext]]
 */
final class ContextCreator(errorReporter: ErrorReporter)
  extends CompilerStep[(List[Source], Map[TypeIdentifier, ModuleImports]), (List[Source], AnalysisContext)] {

  override def apply(input: (List[Source], Map[TypeIdentifier, ModuleImports])): (List[Source], AnalysisContext) = {
    val (sources, imports) = input
    val ctx = buildContext(sources)(using imports)
    errorReporter.displayAndTerminateIfErrors()
    (sources, ctx)
  }

  private def buildContext(sources: List[Source])(using Map[TypeIdentifier, ModuleImports]): AnalysisContext = {
    val ctxBuilder = new AnalysisContextBuilder(errorReporter)
    for src <- sources do {
      for df <- src.defs do {
        df match
          case moduleDef: ModuleDef =>
            ctxBuilder.addModule(moduleDef)
          case packageDef: PackageDef =>
            ctxBuilder.addPackage(packageDef)
          case structDef: StructDef =>
            ctxBuilder.addStruct(structDef)
          case constDef: ConstDef =>
            ctxBuilder.addConstant(constDef)
      }
    }
    ctxBuilder.build()
  }

}
