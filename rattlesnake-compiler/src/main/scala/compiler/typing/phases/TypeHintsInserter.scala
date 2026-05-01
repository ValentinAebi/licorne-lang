package compiler.typing.phases

import compiler.identifiers.TypeIdentifier
import compiler.irs.ssa.SSA.*
import compiler.irs.ssa.SSA
import compiler.irs.ssa.Formulas.{Formula, IdValue, UninterpretedConstIdValue}
import compiler.lang.{FunctionSignature, RuntimeTypeSignature, UserInstantiableTypeSig}
import compiler.lang.Types.{ClosureType, NamedType, Type}
import compiler.pipeline.CompilationStep.TypeHintsInsertion
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.Reasoning
import compiler.typing.{SubtypingInfo, TypeHintsStore}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeVariablesContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class TypeHintsInserter(
                               typeVarsCtx: TypeVariablesContext,
                               proxyStore: ProxyStore,
                               typeHintsStore: TypeHintsStore,
                               er: ErrorReporter
                             ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = TypeHintsInsertion

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSupertypesSubstitutions)) = input
    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val resolCtx = ResolutionContext(program, typeVarsCtx, er)
    Reasoning.usingFreshReasoningToolkit(dealiasingCtx, resolCtx, proxyStore) { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, er)
    } { (solver, subtypingCtx, simplifier, meetJoin, absInt) =>
      for {
        (funSig, func) <- program.functions
        body <- func.bodyOpt
      } {
        val fakeEr = ErrorReporter(
          _ => throw AssertionError("error reported during type hints insertion"),
          _ => throw AssertionError("fatal error during type hints insertion")
        )
        val resolCtx = ResolutionContext(program, typeVarsCtx, fakeEr)
        traverseScope(body, funSig)(using resolCtx, program.globalValuesContext, subtypingCtx, dealiasingCtx)
      }
    }
    input
  }

  private def traverseScope(scope: Scope, currFunSig: FunctionSignature)
                           (using ResolutionContext, GlobalValuesContext, SubtypingContext, DealiasingContext): Unit = {
    for (instr <- scope.instructions.reverse) {
      traverseInstr(instr, currFunSig)
    }
  }

  private def traverseInstr(instr: Instr, currFunSig: FunctionSignature)
                           (using resolutionCtx: ResolutionContext, globalValsCtx: GlobalValuesContext, subtypingCtx: SubtypingContext, dealiasingCtx: DealiasingContext): Unit = instr match {
    case Loop(cond, condVal, body, variables) =>
      for {
        LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- variables
        th <- typeHintsStore.getHints(condVal)
      } {
        typeHintsStore.addHint(beforeLoopVal, th)
        typeHintsStore.addHint(bodyLastVal, th)
      }
      traverseScope(body, currFunSig)
      traverseScope(cond, currFunSig)
    case Disjunction(condVal, thenBr, elseBr, variables) =>
      for {
        DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables
        th <- typeHintsStore.getHints(joinedVal)
      } {
        typeHintsStore.addHint(afterThenVal, th)
        typeHintsStore.addHint(afterElseVal, th)
      }
      traverseScope(thenBr, currFunSig)
      traverseScope(elseBr, currFunSig)
    case StaticTypeAssert(value, tpe) =>
      typeHintsStore.addHint(value, tpe)
    case StaticAssert(value) => ()
    case AssignVal(assigned, src) =>
      for (th <- typeHintsStore.getHints(assigned)) {
        typeHintsStore.addHint(src, th)
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
    case InvokeFunc(assigned, receiver, func, typeArgs, args) =>
      for {
        receiverTypeId <- resolveReceiver(receiver, currFunSig)
        funSig <- resolutionCtx.resolveFunSig(receiverTypeId, func.funId).asOption
      } {
        val typesSubst = mutable.Map.from(funSig.typeParams.map(_.tid).zip(typeArgs))
        val valsSubst = mutable.Map.empty[IdValue, Formula]
        typeHintsStore.getHints(assigned).headOption.foreach { hint =>
          unifyTypes(hint, funSig.retType)(using typesSubst)
        }
        for (((paramVal, paramTypeRaw), argVal) <- funSig.paramsWithoutThis.zip(args)) {
          val paramTypeSubst = paramTypeRaw.substitute(typesSubst, valsSubst)
          typeHintsStore.addHint(argVal, paramTypeSubst)
          valsSubst.put(paramVal, argVal)
        }
      }
    case InvokeClosure(assigned, callee, closureTypingTarget, args) => ()
    case Instantiate(assigned, classOrRecordName, typeArgs) => ()
    case MkClosure(assigned, params, body, declaredPure) => ()
    case MkHeapVar(assigned) => ()
    case TypeTest(assigned, testedValue, testedTypeId) => ()
    case Conversion(assigned, inValue, targetType) => ()
    case FieldRead(assigned, owner, field) => ()
    case FieldWrite(owner, fieldResolTarget, rhs) =>
      for {
        ownerTypeId <- resolveReceiver(owner, currFunSig)
        ownerTypeSig <- resolutionCtx.resolveTypeSigAs[UserInstantiableTypeSig](ownerTypeId)
        field <- ownerTypeSig.fields.get(fieldResolTarget.fieldId)
      } {
        typeHintsStore.addHint(rhs, field.tpe)
      }
    case HeapVarRead(assigned, heapVar) => ()
    case HeapVarWrite(heapVar, newValue) => ()
    case Return(retVal) =>
      typeHintsStore.addHint(retVal, currFunSig.retType)
    case Panic(msg) => ()
    case Cast(inValue, target) => ()
    case Drop(droppedValue) => ()
    case LocalDecl(localId, tpe) => ()
    case Unreachable() => ()
    case scope: Scope =>
      traverseScope(scope, currFunSig)
  }

  private def resolveReceiver(receiver: IdValue, currFunSig: FunctionSignature)
                             (using globalValsCtx: GlobalValuesContext): Option[TypeIdentifier] = {
    proxyStore.getProxy(receiver).getOrElse(receiver) match {
      case value: UninterpretedConstIdValue => globalValsCtx.getNameOfObject(value)
      case value if value == currFunSig.receiverVal => Some(currFunSig.ownerName)
      case _ => None
    }
  }

  private def unifyTypes(hint: Type, shape: Type)
                        (using typesSubst: mutable.Map[TypeIdentifier, Type], dealiasingCtx: DealiasingContext, subtypingCtx: SubtypingContext, resolCtx: ResolutionContext): Unit = {
    (dealiasingCtx.dealiasType(hint), dealiasingCtx.dealiasType(shape)) match {
      case (NamedType(hintTypeId, Nil, Nil), tpe) =>
        typesSubst.put(hintTypeId, tpe)
      case (tpe, NamedType(hintTypeId, Nil, Nil)) =>
        typesSubst.put(hintTypeId, tpe)
      case (NamedType(hintTypeId, hintTypeArgs, hintArgs), NamedType(shapeTypeId, shapeTypeArgs, shapeArgs)) =>
        for {
          subtypingSubst <- subtypingCtx.subToSuperSubst(shapeTypeId, hintTypeId)
          upcastShapeType <- resolCtx.resolveTypeSigAs[RuntimeTypeSignature](hintTypeId).map(_.toType(subtypingSubst))
          (hintTypeArg, shapeTypeArg) <- hintTypeArgs.zip(upcastShapeType.typeArgs)
        } {
          unifyTypes(hintTypeArg, shapeTypeArg)
        }
      case (ClosureType(hintParams, hintResult, _), ClosureType(shapeParams, shapeResult, _)) =>
        for ((ht, st) <- hintParams.zip(shapeParams)) {
          unifyTypes(ht, st)
        }
        unifyTypes(hintResult, shapeResult)
      case _ => ()
      // TODO also handle IntersectionTypes and UnionTypes?
    }
  }

}
