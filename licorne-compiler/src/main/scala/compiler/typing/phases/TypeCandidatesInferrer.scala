package compiler.typing.phases

import compiler.identifiers.{ItId, NormalFunOrVarId, TypeIdentifier}
import compiler.irs.ircorne.Formulas.{Formula, IdValue}
import compiler.irs.ircorne.{Formulas, IRcorne}
import compiler.irs.ircorne.IRcorne.*
import compiler.lang.Types.*
import compiler.lang.{ExecutionEnvironment, FunctionDescriptor, RuntimeTypeSignature, TypeParamInfo, UserInstantiableTypeSig}
import compiler.pipeline.CompilationStep.TypeCandidatesInference
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reasoning.Solver.TimeoutConfig
import compiler.reporting.Errors.ErrorReporter
import compiler.reasoning.{CounterexampleBox, IntHandlingMode, MeetJoinComputer, Reasoning}
import compiler.typing.contexts.*
import compiler.typing.*
import compiler.valproxies.{BranchingInfo, ProxyStore}
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeCandidatesInferrer(
                                    ihm: IntHandlingMode[?],
                                    timeoutConfig: TimeoutConfig,
                                    proxyStore: ProxyStore,
                                    typeCandidatesStore: TypeCandidatesStore,
                                    externalTypeVarsCtx: TypeVariablesContext,
                                    counterExBoxOpt: Option[CounterexampleBox],
                                    er: ErrorReporter
                                  ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = TypeCandidatesInference

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input

    // @formatter:off
    given tmpTypeVarsCtx: TypeVariablesContext = TypeVariablesContext()
    given globalValsCtx: GlobalValuesContext = program.globalValuesContext
    // @formatter:on

    val fakeEr = ErrorReporter(
      _ => throw AssertionError("error reported during type candidates inference phase"),
      _ => throw AssertionError("fatal error during type candidates inference phase")
    )
    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val resolCtx = ResolutionContext(program, fakeEr)
    Reasoning.usingFreshReasoningToolkit(ihm, timeoutConfig, dealiasingCtx, resolCtx, proxyStore, program.globalValuesContext, counterExBoxOpt, er) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, globalValsCtx, fakeEr, counterExBoxOpt)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      val typer = Typer(None, dealiasingCtx, resolCtx, tmpTypeVarsCtx, subtypingCtx, meetJoin, proxyStore, TypeCandidatesStore.newEmpty, HeapVarsTypeStore.newEmpty, solver, simplifier, absInt, globalValsCtx, fakeEr, allowWriteToIR = false, closuresCollectorFuncOpt = None)
      fakeEr.withReportingSuspended {
        for {
          ((ownerId, funDescr), func) <- program.functions
          funSig <- Some(resolCtx.forceGetFunction(ownerId, funDescr))
          body <- func.bodyOpt
        } {
          val resolCtx = ResolutionContext(program, fakeEr)
          val meetJoinComputer = MeetJoinComputer(dealiasingCtx, resolCtx, subtypingCtx, solver, proxyStore, globalValsCtx)
          val typeParamsCtx = TypeParamsContext(resolCtx.resolveTypeSig(ownerId).toList.flatMap(_.typeParams) ++ funSig.typeParams)
          val lightweightTyper = LightweightTyper(typer, dealiasingCtx, meetJoinComputer, resolCtx, funSig.sigScope, typeParamsCtx)
          traverseScope(body, funSig)(using typeParamsCtx, resolCtx, program.globalValuesContext, subtypingCtx, dealiasingCtx, tmpTypeVarsCtx, lightweightTyper)
        }
      }
    }
    input
  }

  private def traverseScope(scope: Scope, currEnvir: ExecutionEnvironment)
                           (using TypeParamsContext, ResolutionContext, GlobalValuesContext, SubtypingContext, DealiasingContext, TypeVariablesContext, LightweightTyper): Unit = {
    for (instr <- scope.instructions.reverse) {
      traverseInstr(instr, currEnvir)
    }
  }

  private def traverseInstr(instr: Instr, currEnvir: ExecutionEnvironment)
                           (using typeParamsCtx: TypeParamsContext, resolutionCtx: ResolutionContext, globalValsCtx: GlobalValuesContext,
                            subtypingCtx: SubtypingContext, dealiasingCtx: DealiasingContext, tmpTypeVarsCtx: TypeVariablesContext, lt: LightweightTyper): Unit = instr match {
    case Loop(cond, condVal, body, variables) =>
      for {
        LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal, varDefScope) <- variables
        th <- typeCandidatesStore.getCandidates(condVal)
      } {
        typeCandidatesStore.offerCandidate(beforeLoopVal, th)
        typeCandidatesStore.offerCandidate(bodyLastVal, th)
      }
      traverseScope(body, currEnvir)
      traverseScope(cond, currEnvir)
    case Disjunction(condVal, thenBr, elseBr, variables) =>
      for {
        DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables
        th <- typeCandidatesStore.getCandidates(joinedVal)
      } {
        typeCandidatesStore.offerCandidate(afterThenVal, th)
        typeCandidatesStore.offerCandidate(afterElseVal, th)
      }
      traverseScope(thenBr, currEnvir)
      traverseScope(elseBr, currEnvir)
    case StaticTypeAssert(value, tpe) =>
      typeCandidatesStore.offerCandidate(value, tpe)
    case AssignVal(assigned, src) =>
      for (th <- typeCandidatesStore.getCandidates(assigned)) {
        typeCandidatesStore.offerCandidate(src, th)
      }
    case AssignIntConst(assigned, src) => ()
    case AssignBoolConst(assigned, src) => ()
    case AssignCharConst(assigned, src) => ()
    case AssignStringConst(assigned, src) => ()
    case NumNeg(assigned, operand) => ()
    case Add(assigned, lhs, rhs) => ()
    case Sub(assigned, lhs, rhs) => ()
    case Mul(assigned, lhs, rhs) => ()
    case Div(assigned, lhs, rhs) => ()
    case Rem(assigned, lhs, rhs) => ()
    case LogicNeg(assigned, operand) => ()
    case And(assigned, lhs, rhs) => ()
    case Or(assigned, lhs, rhs) => ()
    case Equal(assigned, lhs, rhs) => ()
    case Leq(assigned, lhs, rhs) => ()
    case Lt(assigned, lhs, rhs) => ()
    case invkFunc@InvokeFunc(assigned, receiver, func, typeArgs, args) =>
      for {
        (receiverTypeId, owTypesSubst, owValsSubst) <- resolveReceiver(receiver, currEnvir).orElse {
          lt.findPossibleTypesFor(receiver)
            .flatMap(tSig => tSig.functions.toList.map((_, funSig) => (tSig, funSig)))
            .find((tSig, funSig) => funSig.functionName == func.funId)
            .map { (tSig, funSig) =>
              val typesSubst = tSig.typeParams.map { tp =>
                tp.tid -> tmpTypeVarsCtx.newTypeVariable(tp.tid, tp.upperBoundOpt, tp.lowerBoundOpt, typeParamsCtx, invkFunc.getPosition)
              }.toMap
              (tSig.id, typesSubst, Map.empty[IdValue, Formula])
            }
        }
        funSig <- resolutionCtx.resolveFunSig(receiverTypeId, FunctionDescriptor(func.funId, args.size), args.map(lt.detectDealiasedTypeOf)).asOptionWithoutReceiver
      } {
        val typeParams = funSig.typeParams
        val typesSubst = owTypesSubst ++ createTypeParamsSubst(typeParams, typeArgs)
        typeCandidatesStore.getCandidates(assigned).headOption.foreach { candidate =>
          unifyTypes(candidate, funSig.retType.substitute(typesSubst, owValsSubst))
        }
        val valsSubst = mutable.Map.from(owValsSubst)
        for (((paramVal, paramTypeRaw), argVal) <- funSig.paramsInclThis.zip(receiver +: args)) {
          val paramTypeSubst = paramTypeRaw.substitute(typesSubst, valsSubst)
          typeCandidatesStore.offerCandidate(argVal, paramTypeSubst)
          valsSubst.put(paramVal, argVal)
        }
      }
    case InvokeClosure(assigned, callee, closureTypingTarget, args) => ()
    case mkClosure@MkClosure(assigned, params, body, uniqueRetOpt, _, closureTypeName) =>

      def isClosureTypeWithoutArgs(tpe: Type): Boolean = tpe match {
        case ClosureType(params, result, enforcedPure) => params.isEmpty
        case _ => false
      }

      val closureTypeCandidates = typeCandidatesStore.getCandidates(assigned)
      if (params.size == 1 && params.headOption.exists(_._1.id == ItId) && closureTypeCandidates.nonEmpty && closureTypeCandidates.forall(isClosureTypeWithoutArgs)) {
        mkClosure.params = List.empty
        proxyStore.getClosureProxy(assigned).foreach { closureValue =>
          closureValue.params = List.empty
        }
        val itType = params.head._2.asInstanceOf[TypeVariable]
        tmpTypeVarsCtx.forgetTypeVar(itType)
        externalTypeVarsCtx.forgetTypeVar(itType)
      }
      val requirePure = closureTypeCandidates.exists {
        case ClosureType(params, result, enforcedPure) => enforcedPure
        case _ => false
      }
      if (requirePure) {
        proxyStore.validateClosurePurity(assigned)
      }
      val closureInfo = ClosureInfo(params, body, tmpTypeVarsCtx.newTypeVariable(NormalFunOrVarId(assigned.toString), None, None, typeParamsCtx, mkClosure.getPosition), BranchingInfo.empty, requirePure, TypeParamsContext.empty /* TODO check this */)
      traverseScope(body, closureInfo)
    case MkHeapVar(assigned) => ()
    case TypeTest(assigned, testedValue, testedTypeId) => ()
    case Conversion(assigned, inValue, targetType) => ()
    case FieldRead(assigned, owner, field) => ()
    case FieldWrite(owner, fieldResolTarget, rhs) =>
      for {
        (ownerTypeId, owTypesSubst, owValsSubst) <- resolveReceiver(owner, currEnvir)
        ownerTypeSig <- resolutionCtx.resolveTypeSigAs[UserInstantiableTypeSig](ownerTypeId)
        field <- ownerTypeSig.fields.get(fieldResolTarget.fieldId)
      } {
        typeCandidatesStore.offerCandidate(rhs, field.tpe.substitute(owTypesSubst, owValsSubst))
      }
    case HeapVarRead(assigned, heapVar) => ()
    case HeapVarWrite(heapVar, newValue) => ()
    case Return(retVal) =>
      typeCandidatesStore.offerCandidate(retVal, currEnvir.expectedResultType)
    case Panic(msg) => ()
    case Cast(inValue, target) => ()
    case HybridCast(inValue) => ()
    case LocalDecl(localId, tpe) => ()
    case Unreachable() => ()
    case scope: Scope =>
      traverseScope(scope, currEnvir)
  }

  private def resolveReceiver(receiver: IdValue, currEnvir: ExecutionEnvironment)
                             (using globalValsCtx: GlobalValuesContext, resolCtx: ResolutionContext, lt: LightweightTyper): Option[(TypeIdentifier, Map[TypeIdentifier, Type], Map[IdValue, Formula])] = {
    lt.detectDealiasedTypeOf(receiver).asRefinedType.baseType match {
      case NamedType(typeName, typeArgs, args) =>
        resolCtx.resolveTypeSigAs[RuntimeTypeSignature](typeName).map { sig =>
          val typesSubst = sig.typeParams.map(_.tid).zip(typeArgs).toMap
          val valsSubst = sig.fields.map(_._2.value).zip(args).toMap[IdValue, Formula]
          (typeName, typesSubst, valsSubst)
        }
      case _ => None
    }
  }

  private def createTypeParamsSubst(typeParams: List[TypeParamInfo], typeArgs: List[Type])(using tpCtx: TypeParamsContext, tvCtx: TypeVariablesContext): Map[TypeIdentifier, Type] = {
    val substB = Map.newBuilder[TypeIdentifier, Type]
    val typeParamsIter = typeParams.iterator
    val typeArgsIter = typeArgs.iterator
    while (typeParamsIter.nonEmpty) {
      val tParam = typeParamsIter.next()
      val tArg = typeArgsIter.nextOption().getOrElse(tvCtx.newTypeVariable(tParam.tid, None, None, tpCtx, None))
      substB.addOne(tParam.tid -> tArg)
    }
    substB.result()
  }

  private class LightweightTyper(typer: Typer, dealiasingCtx: DealiasingContext, meetJoinComputer: MeetJoinComputer, resolCtx: ResolutionContext, funSigScope: Scope, typeParamsCtx: TypeParamsContext) {

    def detectDealiasedTypeOf(formula: Formula): Type = {
      val dev = proxyStore.developDeep(formula, bypassPurityChecks = true, acceptPhis = true)(using resolCtx)
      val typeRaw = typer.typeFormula(dev, funSigScope, None)(using typeParamsCtx)
      dealiasingCtx.dealiasType(typeRaw)
    }

    def findPossibleTypesFor(idValue: IdValue): Iterable[RuntimeTypeSignature] =
      proxyStore.findInitializationTypesOf(idValue) match {
        case Some(typesIter) =>
          meetJoinComputer.computeJoinOfTypeIds(typesIter)
        case None => List.empty
      }
  }

}
