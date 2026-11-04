package compiler.typing.phases

import compiler.datastructures.Graph
import compiler.identifiers.{FunOrVarId, ConstructorFunId, TypeIdentifier}
import compiler.irs.ircorne.Formulas
import compiler.irs.ircorne.Formulas.{IdValue, NamedIdValue}
import compiler.lang.{RuntimeTypeSignature, Types, UserInstantiableTypeSig}
import compiler.lang.Types.*
import compiler.pipeline.CompilationStep.TypeAliasesAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reasoning.Solver.TimeoutConfig
import compiler.reporting.Errors.ErrorReporter
import compiler.reasoning.{CounterexampleBox, IntHandlingMode, Reasoning, Solver}
import compiler.typing.contexts.*
import compiler.typing.{HeapVarsTypeStore, SubtypingInfo, TypeCandidatesStore, Typer}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.immutable.SeqMap
import scala.collection.mutable

final class TypeAliasesAnalyzer(
                                 ihm: IntHandlingMode[?],
                                 timeoutConfig: TimeoutConfig,
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

    val oldDealiasingCtx = DealiasingContext(programOld.typeAliases)
    val programNew = Reasoning.usingFreshReasoningToolkit(ihm, timeoutConfig, oldDealiasingCtx, resolutionCtx, proxyStore, programOld.globalValuesContext, counterExBoxOpt, er) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, oldDealiasingCtx, resolutionCtx, solver, proxyStore, globalValsCtx, er, counterExBoxOpt)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>

      given Solver = solver

      val typer = Typer(None, oldDealiasingCtx, resolutionCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er, closuresCollectorFuncOpt = None /* TODO maybe we can allow closures in type aliases */)
      val newTypeAliases = for (tid, tSig) <- programOld.typeAliases yield tid -> typer.typeTypeAliasSig(tSig)

      val newDealiasingCtx = DealiasingContext(newTypeAliases)
      val newObjects = for ((objId, objSig) <- programOld.objects) yield objId -> (if objId.isCompanionObject then {
        objSig.copy(functions = for ((funDesc, funSig) <- objSig.functions) yield funDesc -> {
          assert(funSig.sigName == ConstructorFunId)
          resolutionCtx.resolveTypeSigAs[UserInstantiableTypeSig](objId.copy(isCompanionObject = false)) match {
            case Some(instantiatedTypeSig) =>
              val newParamsWithoutThisB = SeqMap.newBuilder[NamedIdValue, Type]
              val valsSubst = mutable.Map.empty[FunOrVarId, IdValue]
              for (((paramVal, paramType), paramId) <- funSig.paramsWithoutThis zip instantiatedTypeSig.constructorParams.keys) {
                newParamsWithoutThisB.addOne(paramVal, newDealiasingCtx.dealiasType(paramType).withDependenciesTransformed(_.convertThisDotFieldToFieldVal(instantiatedTypeSig, valsSubst)))
                valsSubst.put(paramId, paramVal)
              }
              funSig.copy(paramsInclThis = funSig.paramsInclThis.take(1) ++ newParamsWithoutThisB.result())
            case None => funSig
          }
        })
      } else objSig)

      programOld.copy(typeAliases = newTypeAliases, objects = newObjects)
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

  private def findMentionedTypes(tpe: Type): Set[TypeIdentifier] = {
    val tidsB = Set.newBuilder[TypeIdentifier]
    tpe.traversePreOrder {
      case NamedType(tid, _, _) =>
        tidsB.addOne(tid)
      case _ => ()
    }
    tidsB.result()
  }

}
