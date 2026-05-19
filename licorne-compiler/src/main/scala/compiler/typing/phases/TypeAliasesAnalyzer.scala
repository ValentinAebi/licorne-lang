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
import compiler.smt.{IntHandlingMode, Reasoning, Solver}
import compiler.typing.contexts.*
import compiler.typing.{HeapVarsTypeStore, SubtypingInfo, TypeHintsStore, Typer}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeAliasesAnalyzer(
                                 ihm: IntHandlingMode[?],
                                 typeVarsCtx: TypeVariablesContext,
                                 proxyStore: ProxyStore,
                                 typeHintsStore: TypeHintsStore,
                                 heapVarsTypeStore: HeapVarsTypeStore,
                                 er: ErrorReporter
                               ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = TypeAliasesAnalysis

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input
    
    given globalValsCtx: GlobalValuesContext = program.globalValuesContext
    
    val resolutionCtx = ResolutionContext(program, er)
    checkTypeAliasesCyclicity(program, resolutionCtx)
    er.displayAndTerminateIfErrors()

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    Reasoning.usingFreshReasoningToolkit(ihm, dealiasingCtx, resolutionCtx, proxyStore, program.globalValuesContext) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolutionCtx, solver, proxyStore, globalValsCtx, er)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      
      given Solver = solver

      // save types of objects
      val globalValsCtx = program.globalValuesContext
      val globalScope = globalValsCtx.globalScope
      for ((objectId, objectSig) <- program.objects) {
        val objVal = globalValsCtx.resolveObject(objectId)
        globalScope.saveType(objVal, objectSig.toType(Map.empty))(using TypeParamsContext.empty, simplifier, resolutionCtx, proxyStore)
      }
      
      val typer = Typer(None, dealiasingCtx, resolutionCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeHintsStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er)
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
    input
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
