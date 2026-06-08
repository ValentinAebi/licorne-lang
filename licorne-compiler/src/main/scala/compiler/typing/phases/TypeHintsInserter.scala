package compiler.typing.phases

import compiler.identifiers.{NormalFunOrVarId, TypeIdentifier}
import compiler.irs.ssa.Formulas.{Formula, IdValue, UninterpretedConstIdValue}
import compiler.irs.ssa.SSA
import compiler.irs.ssa.SSA.*
import compiler.lang.Types.*
import compiler.lang.{ExecutionEnvironment, FunctionSignature, RuntimeTypeSignature, TypeParamInfo, UserInstantiableTypeSig}
import compiler.pipeline.CompilationStep.TypeHintsInsertion
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.{CounterexampleBox, IntHandlingMode, Reasoning}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeParamsContext, TypeVariablesContext}
import compiler.typing.{ClosureInfo, HeapVarsTypeStore, SubtypingInfo, TypeHintsStore, Typer}
import compiler.valproxies.{BranchingInfo, ProxyStore}
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeHintsInserter(
                               ihm: IntHandlingMode[?],
                               proxyStore: ProxyStore,
                               typeHintsStore: TypeHintsStore,
                               er: ErrorReporter,
                               counterExBoxOpt: Option[CounterexampleBox]
                             ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = TypeHintsInsertion

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input

    // @formatter:off
    given tmpTypeVarsCtx: TypeVariablesContext = TypeVariablesContext()
    given globalValsCtx: GlobalValuesContext = program.globalValuesContext
    // @formatter:on

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val resolCtx = ResolutionContext(program, er)
    Reasoning.usingFreshReasoningToolkit(ihm, dealiasingCtx, resolCtx, proxyStore, program.globalValuesContext, counterExBoxOpt) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, globalValsCtx, er, counterExBoxOpt)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      val fakeEr = ErrorReporter(
        _ => throw AssertionError("error reported during type hints insertion"),
        _ => throw AssertionError("fatal error during type hints insertion")
      )
      val typer = Typer(None, dealiasingCtx, resolCtx, tmpTypeVarsCtx, subtypingCtx, meetJoin, proxyStore, TypeHintsStore.newEmpty, HeapVarsTypeStore.newEmpty, solver, simplifier, absInt, globalValsCtx, fakeEr, allowWriteToIR = false)
      fakeEr.withReportingSuspended {
        for {
          ((ownerId, funId), func) <- program.functions
          funSig <- resolCtx.resolveFunSig(ownerId, funId)(using subtypingCtx).asOption
          body <- func.bodyOpt
        } {
          val resolCtx = ResolutionContext(program, fakeEr)
          val typeParamsCtx = TypeParamsContext(resolCtx.resolveTypeSig(ownerId).toList.flatMap(_.typeParams) ++ funSig.typeParams)
          val lightweightTyper = LightweightTyper(typer, dealiasingCtx, resolCtx, funSig.sigScope, typeParamsCtx)
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
                            subtypingCtx: SubtypingContext, dealiasingCtx: DealiasingContext, typeVarsCtx: TypeVariablesContext, lt: LightweightTyper): Unit = instr match {
    case Loop(cond, condVal, body, variables) =>
      for {
        LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal, varDefScope) <- variables
        th <- typeHintsStore.getHints(condVal)
      } {
        typeHintsStore.offerHint(beforeLoopVal, th)
        typeHintsStore.offerHint(bodyLastVal, th)
      }
      traverseScope(body, currEnvir)
      traverseScope(cond, currEnvir)
    case Disjunction(condVal, thenBr, elseBr, variables) =>
      for {
        DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables
        th <- typeHintsStore.getHints(joinedVal)
      } {
        typeHintsStore.offerHint(afterThenVal, th)
        typeHintsStore.offerHint(afterElseVal, th)
      }
      traverseScope(thenBr, currEnvir)
      traverseScope(elseBr, currEnvir)
    case StaticTypeAssert(value, tpe) =>
      typeHintsStore.offerHint(value, tpe)
    case AssignVal(assigned, src) =>
      for (th <- typeHintsStore.getHints(assigned)) {
        typeHintsStore.offerHint(src, th)
      }
    case AssignIntConst(assigned, src) => ()
    case AssignBoolConst(assigned, src) => ()
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
        (receiverTypeId, owTypesSubst, owValsSubst) <- resolveReceiver(receiver, currEnvir)
        funSig <- resolutionCtx.resolveFunSig(receiverTypeId, func.funId).asOption
      } {
        val typeParams = funSig.typeParams
        val typesSubst = owTypesSubst ++ createTypeParamsSubst(typeParams, typeArgs)
        typeHintsStore.getHints(assigned).headOption.foreach { hint =>
          unifyTypes(hint, funSig.retType.substitute(typesSubst, owValsSubst))
        }
        val valsSubst = mutable.Map.from(owValsSubst)
        valsSubst.put(funSig.receiverVal, receiver)
        for (((paramVal, paramTypeRaw), argVal) <- funSig.paramsWithoutThis.zip(args)) {
          val paramTypeSubst = paramTypeRaw.substitute(typesSubst, valsSubst)
          typeHintsStore.offerHint(argVal, paramTypeSubst)
          valsSubst.put(paramVal, argVal)
        }
      }
    case InvokeClosure(assigned, callee, closureTypingTarget, args) => ()
    case Instantiate(assigned, classOrRecordName, typeArgs, fieldsInit) =>
      for {
        hint <- typeHintsStore.getHints(assigned).headOption
        tSig <- resolutionCtx.resolveTypeSigAs[UserInstantiableTypeSig](classOrRecordName)
      } {
        val subst = createTypeParamsSubst(tSig.typeParams, typeArgs)
        for {
          (fldId, fldVal) <- fieldsInit
          fld <- tSig.fields.get(fldId)
        } {
          val expFldType = fld.tpe.substitute(subst, Map.empty)
          typeHintsStore.offerHint(fldVal, expFldType)
        }
      }
    case mkClosure@MkClosure(assigned, params, body, declaredPure) =>
      val closureInfo = ClosureInfo(params, body, typeVarsCtx.newTypeVariable(NormalFunOrVarId(assigned.toString), None, None, typeParamsCtx, mkClosure.getPosition), BranchingInfo.empty, declaredPure, currEnvir, TypeParamsContext.empty /* TODO check this */)
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
        typeHintsStore.offerHint(rhs, field.tpe.substitute(owTypesSubst, owValsSubst))
      }
    case HeapVarRead(assigned, heapVar) => ()
    case HeapVarWrite(heapVar, newValue) => ()
    case Return(retVal) =>
      typeHintsStore.offerHint(retVal, currEnvir.expectedResultType)
    case Panic(msg) => ()
    case Cast(inValue, target) => ()
    case SoftCast(inValue) => ()
    case Drop(droppedValue) => ()
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
          val valsSubst = sig.params.map(_._2._2).zip(args).toMap
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

  private def unifyTypes(hint: Type, shape: Type)
                        (using dealiasingCtx: DealiasingContext, subtypingCtx: SubtypingContext, resolCtx: ResolutionContext): Unit = {
    (dealiasingCtx.dealiasType(hint).withTypeVarsExpanded, dealiasingCtx.dealiasType(shape).withTypeVarsExpanded) match {
      case (tv: TypeVariable, shape) =>
        tv.resolve(shape)
      case (hint, tv: TypeVariable) =>
        tv.resolve(hint)
      case (NamedType(hintTypeId, hintTypeArgs, hintArgs), NamedType(shapeTypeId, shapeTypeArgs, shapeArgs)) =>
        for {
          subtypingSubst <- subtypingCtx.subToSuperSubst(shapeTypeId, hintTypeId)
          hintTSig <- resolCtx.resolveTypeSigAs[RuntimeTypeSignature](hintTypeId)
          shapeTypeSig <- resolCtx.resolveTypeSigAs[RuntimeTypeSignature](shapeTypeId)
        } {
          val shapeSubst = shapeTypeSig.typeParams.map(_.tid).zip(shapeTypeArgs).toMap
          val composedSubst = subtypingSubst.map {
            case (tParam, tArg@NamedType(tArgId, Nil, Nil)) =>
              tParam -> shapeSubst.getOrElse(tArgId, tArg)
            case (tParam, tArg) =>
              tParam -> tArg
          }
          val upcastShapeType = shapeTypeSig.toType(composedSubst)
          for ((h, s) <- hintTypeArgs.zip(upcastShapeType.typeArgs)) {
            unifyTypes(h, s)
          }
        }
      case (ClosureType(hintParams, hintResult, _), ClosureType(shapeParams, shapeResult, _)) =>
        for ((ht, st) <- hintParams.zip(shapeParams)) {
          unifyTypes(ht, st)
        }
        unifyTypes(hintResult, shapeResult)
      case (NullableType(nullatedHint), shape) =>
        unifyTypes(nullatedHint, shape)
      case (hint, NullableType(nullatedShape)) =>
        unifyTypes(hint, nullatedShape)
      case (RefinedType(hintBase, _), shape) =>
        unifyTypes(hintBase, shape)
      case (hint, RefinedType(shapeBase, _)) =>
        unifyTypes(hint, shapeBase)
      case _ => ()
      // TODO also handle IntersectionTypes and UnionTypes?
    }
  }

  private class LightweightTyper(typer: Typer, dealiasingCtx: DealiasingContext, resolCtx: ResolutionContext, funSigScope: Scope, typeParamsCtx: TypeParamsContext) {
    def detectDealiasedTypeOf(formula: Formula): Type = {
      val dev = proxyStore.developDeep(formula, bypassPurityChecks = true)(using resolCtx).getOrElse(formula)
      val typeRaw = typer.typeFormula(dev, funSigScope, None)(using typeParamsCtx)
      dealiasingCtx.dealiasType(typeRaw)
    }
  }

}
