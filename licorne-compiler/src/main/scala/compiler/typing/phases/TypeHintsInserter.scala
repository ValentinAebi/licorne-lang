package compiler.typing.phases

import compiler.identifiers.{NormalFunOrVarId, TypeIdentifier}
import compiler.irs.ssa.Formulas.{Formula, IdValue, UninterpretedConstIdValue}
import compiler.irs.ssa.SSA
import compiler.irs.ssa.SSA.*
import compiler.lang.Types.*
import compiler.lang.{ExecutionEnvironment, FunctionSignature, RuntimeTypeSignature, UserInstantiableTypeSig}
import compiler.pipeline.CompilationStep.TypeHintsInsertion
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.{CounterexampleBox, IntHandlingMode, Reasoning}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeParamsContext, TypeVariablesContext}
import compiler.typing.{ClosureInfo, SubtypingInfo, TypeHintsStore}
import compiler.valproxies.{BranchingInfo, ProxyStore}
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeHintsInserter(
                               ihm: IntHandlingMode[?],
                               typeVarsCtx: TypeVariablesContext,
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
      for {
        ((ownerId, funId), func) <- program.functions
        funSig <- resolCtx.resolveFunSig(ownerId, funId)(using subtypingCtx).asOption
        body <- func.bodyOpt
      } {
        val fakeEr = ErrorReporter(
          _ => throw AssertionError("error reported during type hints insertion"),
          _ => throw AssertionError("fatal error during type hints insertion")
        )
        val resolCtx = ResolutionContext(program, fakeEr)
        traverseScope(body, funSig)(using resolCtx, program.globalValuesContext, subtypingCtx, dealiasingCtx)
      }
    }
    input
  }

  private def traverseScope(scope: Scope, currEnvir: ExecutionEnvironment)
                           (using ResolutionContext, GlobalValuesContext, SubtypingContext, DealiasingContext, TypeVariablesContext): Unit = {
    for (instr <- scope.instructions.reverse) {
      traverseInstr(instr, currEnvir)
    }
  }

  private def traverseInstr(instr: Instr, currEnvir: ExecutionEnvironment)
                           (using resolutionCtx: ResolutionContext, globalValsCtx: GlobalValuesContext,
                            subtypingCtx: SubtypingContext, dealiasingCtx: DealiasingContext, typeVarsCtx: TypeVariablesContext): Unit = instr match {
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
    case StaticAssert(value) => ()
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
        receiverTypeId <- resolveReceiver(receiver, currEnvir)
        funSig <- resolutionCtx.resolveFunSig(receiverTypeId, func.funId).asOption
      } {
        val typeParams = funSig.typeParams
        val typesSubst = Map.from(
          if typeArgs.isEmpty
          then typeParams.map(tp => tp.tid -> typeVarsCtx.newTypeVariable(tp.tid, None, None, invkFunc.getPosition))
          else typeParams.map(_.tid).zip(typeArgs)
        )
        val valsSubst = mutable.Map.empty[IdValue, Formula]
        typeHintsStore.getHints(assigned).headOption.foreach { hint =>
          unifyTypes(hint, funSig.retType.substitute(typesSubst, Map.empty))
        }
        for (((paramVal, paramTypeRaw), argVal) <- funSig.paramsWithoutThis.zip(args)) {
          val paramTypeSubst = paramTypeRaw.substitute(typesSubst, valsSubst)
          typeHintsStore.offerHint(argVal, paramTypeSubst)
          valsSubst.put(paramVal, argVal)
        }
      }
    case InvokeClosure(assigned, callee, closureTypingTarget, args) => ()
    case Instantiate(assigned, classOrRecordName, typeArgs) => ()
    case mkClosure@MkClosure(assigned, params, body, declaredPure) =>
      val closureInfo = ClosureInfo(params, body, typeVarsCtx.newTypeVariable(NormalFunOrVarId(assigned.toString), None, None, mkClosure.getPosition), BranchingInfo.empty, declaredPure, currEnvir, TypeParamsContext.empty /* TODO check this */)
      traverseScope(body, closureInfo)
    case MkHeapVar(assigned) => ()
    case TypeTest(assigned, testedValue, testedTypeId) => ()
    case Conversion(assigned, inValue, targetType) => ()
    case FieldRead(assigned, owner, field) => ()
    case FieldWrite(owner, fieldResolTarget, rhs) =>
      for {
        ownerTypeId <- resolveReceiver(owner, currEnvir)
        ownerTypeSig <- resolutionCtx.resolveTypeSigAs[UserInstantiableTypeSig](ownerTypeId)
        field <- ownerTypeSig.fields.get(fieldResolTarget.fieldId)
      } {
        typeHintsStore.offerHint(rhs, field.tpe)
      }
    case HeapVarRead(assigned, heapVar) => ()
    case HeapVarWrite(heapVar, newValue) => ()
    case Return(retVal) =>
      typeHintsStore.offerHint(retVal, currEnvir.expectedResultType)
    case Panic(msg) => ()
    case Cast(inValue, target) => ()
    case WeakCast(inValue) => ()
    case Drop(droppedValue) => ()
    case LocalDecl(localId, tpe) => ()
    case Unreachable() => ()
    case scope: Scope =>
      traverseScope(scope, currEnvir)
  }

  private def resolveReceiver(receiver: IdValue, currEnvir: ExecutionEnvironment)
                             (using globalValsCtx: GlobalValuesContext): Option[TypeIdentifier] = {
    proxyStore.developDeep(receiver).getOrElse(receiver) match {
      case value: UninterpretedConstIdValue => globalValsCtx.getNameOfObject(value)
      case value if value == currEnvir.root.receiverVal => Some(currEnvir.root.ownerName)
      case _ => None
    }
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

}
