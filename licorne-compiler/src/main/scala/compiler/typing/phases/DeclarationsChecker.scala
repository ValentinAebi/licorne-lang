package compiler.typing.phases

import compiler.lang.Types.PrimitiveType.UnitType
import compiler.lang.Types.TypeVariable
import compiler.lang.UserInstantiableTypeSig
import compiler.pipeline.CompilationStep.DeclarationsAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reasoning.{CounterexampleBox, IntHandlingMode, Reasoning}
import compiler.typing.{ClosureInfo, HeapVarsTypeStore, SubtypingInfo, TypeCandidatesStore, Typer}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeParamsContext, TypeVariablesContext}
import compiler.valproxies.{BranchingInfo, ProxyStore}
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable


final class DeclarationsChecker(
                                 ihm: IntHandlingMode[?],
                                 typeVarsCtx: TypeVariablesContext,
                                 proxyStore: ProxyStore,
                                 typeCandidatesStore: TypeCandidatesStore,
                                 heapVarsTypeStore: HeapVarsTypeStore,
                                 er: ErrorReporter,
                                 counterExBoxOpt: Option[CounterexampleBox]
                               ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = DeclarationsAnalysis

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (programOld, subtypingInfo@SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input

    given globalValsCtx: GlobalValuesContext = programOld.globalValuesContext

    given dealiasingCtx: DealiasingContext = DealiasingContext(programOld.typeAliases)

    val resolCtx = ResolutionContext(programOld, er)

    Reasoning.usingFreshReasoningToolkit(ihm, dealiasingCtx, resolCtx, proxyStore, programOld.globalValuesContext, counterExBoxOpt) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, globalValsCtx, er, counterExBoxOpt)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>

      val closuresCollector = mutable.Queue.empty[ClosureInfo]
      val typer = Typer(None, dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin, proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er, Some(closuresCollector.enqueue(_)))

      val programNew = Program(globalValsCtx,
        for ((id, interfaceSig) <- programOld.interfaces) yield {
          id -> typer.typeInterfaceSig(interfaceSig)
        },
        for ((id, classSig) <- programOld.classes) yield {
          id -> typer.typeClassSig(classSig)
        },
        for ((id, objectSig) <- programOld.objects) yield {
          id -> typer.typeObjectSig(objectSig)
        },
        for ((id, datatypeSig) <- programOld.datatypes) yield {
          id -> typer.typeDatatypeSig(datatypeSig)
        },
        for ((id, recordSig) <- programOld.records) yield {
          id -> typer.typeRecordSig(recordSig)
        },
        programOld.typeAliases,
        programOld.functions,
        programOld.constructorFieldsInit
      )

      for {
        (tid, constructorFields) <- programNew.constructorFieldsInit
        tSig <- resolCtx.resolveTypeSigAs[UserInstantiableTypeSig](tid)
        tpCtx <- Some(TypeParamsContext(tSig.typeParams))
        (fieldId, (fieldInitInstructions, fieldInitVal)) <- constructorFields
      } {
        given TypeParamsContext = tpCtx

        for (instr <- fieldInitInstructions) {
          typer.typeInstr(instr, tSig.sigScope, BranchingInfo.empty)
        }
        val fieldType = tSig.encapsulatedFields.apply(fieldId).tpe
        val initializerType = tSig.sigScope.getCurrentTypeOf(fieldInitVal)(using proxyStore, simplifier)
        val isSubtype = subtypingCtx.enforceIsSubtype(initializerType, fieldType,
          s"initializer of field $fieldId does not conform to its declared type $fieldType", tSig.declPosOpt)
        if (!fieldType.isInstanceOf[TypeVariable] && isSubtype && !subtypingCtx.isSubtype(fieldType, initializerType) && tSig.encapsulatedFields.apply(fieldId).isStable) {
          val fieldPos = fieldInitInstructions.headOption.flatMap(_.getPosition).orElse(tSig.declPosOpt)
          er.warn(s"type annotation $fieldType on field $fieldId hides its actual type $initializerType (inferred from the initializer), which might cause type checking errors at field use sites", fieldPos)
        }
      }

      while (closuresCollector.nonEmpty) {
        val closureInfo@ClosureInfo(closureParams, closureBody, closureRetType, branchingInfo, requiresPurityInBody, typeParamsCtx) = closuresCollector.dequeue()
        val closureTyper = Typer(Some(closureInfo), dealiasingCtx, resolCtx, typeVarsCtx, subtypingCtx, meetJoin,
          proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValsCtx, er, Some(closuresCollector.enqueue(_)))
        solver.onNewFrame {
          for ((paramVal, paramType) <- closureParams) {
            solver.takeType(paramVal, dealiasingCtx.dealiasType(paramType.withTypeVarsExpanded))
          }
          closureTyper.typeScopeInstructions(closureBody, branchingInfo)(using typeParamsCtx)
          if (!closureRetType.isResolved) {
            er.reportError("I could not infer the return type of the closure", closureBody.getPosition)
          } else if (!closureBody.hasExited && closureRetType.withTypeVarsExpanded == UnitType) {
            er.reportError(s"missing return in non-$UnitType closure", closureBody.getPosition)
          }
        }
      }

      for {
        (tid, constructorFields) <- programNew.constructorFieldsInit
        tSig <- resolCtx.resolveTypeSigAs[UserInstantiableTypeSig](tid)
        tpCtx <- Some(TypeParamsContext(tSig.typeParams))
        (fieldId, (fieldInitInstructions, fieldInitVal)) <- constructorFields
      } {
        tSig.encapsulatedFields.apply(fieldId).tpe match {
          case fieldType: TypeVariable if fieldType.allTypeVariables.exists(!_.isResolved) =>
            er.reportError(s"could not infer type of field $fieldId", tSig.declPosOpt)
          case _ => ()
        }
      }

      er.displayAndTerminateIfErrors()
      (programNew, subtypingInfo)
    }
  }

}
