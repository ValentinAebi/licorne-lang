package compiler.ssagen

import compiler.analysisctx.AnalysisContext
import compiler.irs.Asts.TopLevelDef
import compiler.irs.{Asts, SSA}
import compiler.pipeline.CompilerStep

final class SSAGeneration extends CompilerStep[(List[Asts.Source], AnalysisContext), (List[SSA.FunctionsContainer], AnalysisContext)] {

  override def apply(input: (List[Asts.Source], AnalysisContext)): (List[SSA.FunctionsContainer], AnalysisContext) = {
    val (sources, ctx) = input
    val funContainers = sources.flatMap(traverseSource)
    (funContainers, ctx)
  }

  private def traverseSource(src: Asts.Source): List[SSA.FunctionsContainer] = {
    ??? // TODO
  }

}
