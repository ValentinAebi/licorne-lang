package compiler.typing.phases

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.irs.ssa.Formulas
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.pipeline.CompilationStep.TypeAliasesAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.Reasoning
import compiler.typing.contexts.*
import compiler.typing.{HeapVarsTypeStore, TypeHintsStore, Typer}
import compiler.valproxies.ProxyStore

import scala.collection.mutable

final class TypeAliasesAnalyzer(
                                 typeVarsCtx: TypeVariablesContext,
                                 proxyStore: ProxyStore,
                                 typeHintsStore: TypeHintsStore,
                                 heapVarsTypeStore: HeapVarsTypeStore,
                                 er: ErrorReporter
                               ) extends CompilerStep[Program, Program] {

  private given CompilationStep = TypeAliasesAnalysis

  override def apply(program: Program): Program = {
    val resolutionCtx = ResolutionContext(program, er)
    checkTypeAliasesCyclicity(program, resolutionCtx)
    er.displayAndTerminateIfErrors()

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    Reasoning.usingFreshReasoningToolkit(dealiasingCtx, resolutionCtx, proxyStore, program.globalValuesContext) { solver =>
      SubtypingContext(Graph.empty, mutable.SeqMap.empty, dealiasingCtx, resolutionCtx, solver, proxyStore, er)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      
      val typer = Typer(None, dealiasingCtx, resolutionCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeHintsStore, heapVarsTypeStore, solver, simplifier, absInt, er)
      for (tid, tSig) <- program.typeAliases do {
        val sigScope = tSig.sigScope
        val typeParamsCtx = TypeParamsContext(tSig.typeParams)
        for ((paramId, (paramType, paramVal)) <- tSig.params) {
          sigScope.saveType(paramVal, paramType)(using typeParamsCtx, simplifier, resolutionCtx, proxyStore)
        }
        typer.typeTypeApp(tSig.rhs, None, sigScope, tSig.declPosOpt)(using typeParamsCtx)
      }
    }

    er.displayAndTerminateIfErrors()
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
    case ClosureType(params, resultType, enforcedPure) =>
      params.flatMap(findMentionedTypes).toSet ++ findMentionedTypes(resultType)
    case RefinedType(baseType, itVal, scope, predicate) =>
      findMentionedTypes(baseType)
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      Set.empty
    case NullableType(nullatedType) =>
      findMentionedTypes(nullatedType)
  }

}
