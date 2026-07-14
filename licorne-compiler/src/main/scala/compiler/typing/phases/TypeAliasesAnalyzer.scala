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
import compiler.reasoning.{CounterexampleBox, IntHandlingMode, Reasoning, Solver}
import compiler.typing.contexts.*
import compiler.typing.{HeapVarsTypeStore, SubtypingInfo, TypeCandidatesStore, Typer}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeAliasesAnalyzer(
                                 ihm: IntHandlingMode[?],
                                 typeVarsCtx: TypeVariablesContext,
                                 proxyStore: ProxyStore,
                                 typeCandidatesStore: TypeCandidatesStore,
                                 heapVarsTypeStore: HeapVarsTypeStore,
                                 er: ErrorReporter,
                                 counterExBoxOpt: Option[CounterexampleBox]
                               ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = TypeAliasesAnalysis

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (programOld, subtypingInfo@SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input
    
    given globalValsCtx: GlobalValuesContext = programOld.globalValuesContext
    
    val resolutionCtx = ResolutionContext(programOld, er)
    checkTypeAliasesCyclicity(programOld, resolutionCtx)
    er.displayAndTerminateIfErrors()

    val dealiasingCtx = DealiasingContext(programOld.typeAliases)
    val programNew = Reasoning.usingFreshReasoningToolkit(ihm, dealiasingCtx, resolutionCtx, proxyStore, programOld.globalValuesContext, counterExBoxOpt) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolutionCtx, solver, proxyStore, globalValsCtx, er, counterExBoxOpt)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      
      given Solver = solver

      // save types of objects
      val globalValsCtx = programOld.globalValuesContext
      val globalScope = globalValsCtx.globalScope
      for ((objectId, objectSig) <- programOld.objects) {
        val objVal = globalValsCtx.resolveObject(objectId)
        globalScope.saveType(objVal, objectSig.toType(Map.empty))(using TypeParamsContext.empty, dealiasingCtx, simplifier, resolutionCtx, proxyStore)
      }
      
      val typer = Typer(None, dealiasingCtx, resolutionCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er)
      programOld.copy(typeAliases = for (tid, tSig) <- programOld.typeAliases yield tid -> typer.typeTypeAliasSig(tSig))
    }

    er.displayAndTerminateIfErrors()
    (programNew, subtypingInfo)
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
    case RefinedType(baseType, predicate) =>
      findMentionedTypes(baseType)
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      Set.empty
    case NullableType(nullatedType) =>
      findMentionedTypes(nullatedType)
  }

}
