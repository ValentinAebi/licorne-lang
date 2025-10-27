package compiler.analysisctx

import compiler.irs.Asts.Source
import compiler.pipeline.CompilerStep

final class DefsAnalyzer extends CompilerStep[List[Source], (List[Source], AnalysisContext)] {

  override def apply(input: List[Source]): (List[Source], AnalysisContext) = {
    ??? // TODO
  }
  
}
