package compiler.typing.phases

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.lang.{Formulas, Types}
import compiler.lang.Types.*
import compiler.pipeline.CompilationStep.TypeAliasesAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.typing.{TypeStore, Typer}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, TypeParamsContext, TypeVariablesContext}

final class TypeAliasesAnalyzer(ts: TypeStore, typeVarsCtx: TypeVariablesContext, er: ErrorReporter) extends CompilerStep[Program, Program] {
  
  private given CompilationStep = TypeAliasesAnalysis

  override def apply(program: Program): Program = {
    checkTypeAliasesCyclicity(program, ResolutionContext.fromProgram(program))
    er.displayAndTerminateIfErrors()

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val typer = Typer(ts, dealiasingCtx, ResolutionContext.fromProgram(program), typeVarsCtx, er)
    for (tid, tsig) <- program.typeAliases do {
      val typeParamsCtx = TypeParamsContext(tsig.typeParams)
      typer.dealiasAndTypeType(tsig.rhs, None, tsig.declPosOpt)(using typeParamsCtx)
    }
    
    program
  }

  private def checkTypeAliasesCyclicity(program: Program, resolutionCtx: ResolutionContext): Unit = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for ((id, sig) <- program.typeAliases) {
      val rhsFreeTypes = findMentionedTypes(sig.rhs) -- sig.typeParams.map(_._1)
      graphB.addDescendants(id, rhsFreeTypes)
    }
    graphB.build().findShortestCycle().foreach { cycle =>
      resolutionCtx.resolveTypeSig(cycle.head).foreach { sig =>
        er.reportError("cyclic dependencies between the following type aliases: " ++ cycle.mkString(" -> "), sig.declPosOpt)
      }
    }
  }

  private def findMentionedTypes(tpe: Type): Set[TypeIdentifier] = tpe match {
    case primitiveType: Types.PrimitiveType => Set.empty
    case NamedType(typeName, typeParams, params) =>
      Set(typeName) ++ typeParams.flatMap(findMentionedTypes)
    case _: TypeVariable => Set.empty
    case UnionType(types) =>
      types.flatMap(findMentionedTypes)
    case IntersectionType(types) =>
      types.flatMap(findMentionedTypes)
    case ClosureType(params, resultType) =>
      params.flatMap(findMentionedTypes).toSet ++ findMentionedTypes(resultType)
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      Set.empty
  }

}
