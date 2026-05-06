package compiler.ssagen

import compiler.irs.asts.Asts.{Source, TopLevelDef}
import compiler.pipeline.CompilerStep
import compiler.ssagen.ImportsScanner.PackagesInfo
import compiler.util.mapVals

import scala.collection.mutable


final class ImportsScanner extends CompilerStep[List[Source], (List[Source], PackagesInfo)] {

  override def apply(sources: List[Source]): (List[Source], PackagesInfo) = {
    val packages = mutable.Map.empty[List[String], mutable.Map[String, TopLevelDef]]
    for (source <- sources) {
      val pkgPrefix = source.pkgDeclOpt.map(_.nameParts).getOrElse(List.empty)
      val pkgMap = packages.getOrElseUpdate(pkgPrefix, mutable.Map.empty)
      for (df <- source.defs) {
        pkgMap.put(df.name, df)
      }
    }
    (sources, packages.mapVals(_.toMap).toMap)
  }

}

object ImportsScanner {

  type PackagesInfo = Map[List[String], Map[String, TopLevelDef]]

}
