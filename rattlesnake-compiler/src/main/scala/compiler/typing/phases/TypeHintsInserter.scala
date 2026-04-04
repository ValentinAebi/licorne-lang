package compiler.typing.phases

import compiler.identifiers.TypeIdentifier
import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.lang.Formulas.{Formula, IdValue, UninterpretedConstIdValue}
import compiler.lang.RuntimeTypeSignature
import compiler.lang.Types.{ClosureType, NamedType, Type}
import compiler.pipeline.CompilationStep.TypeHintsInsertion
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.Reasoning
import compiler.typing.{SubtypingInfo, TypeHintsStore}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeVariablesContext}
import compiler.util.zipCommons
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
    Reasoning.usingFreshReasoningToolkit { solver =>
      SubtypingContext(subtypingGraph, flattenedSupertypesSubstitutions, dealiasingCtx, resolCtx, solver, proxyStore, er)
    } { (solver, subtypingCtx, simplifier, absInt) =>
      for {
        (funSig, func) <- program.functions
        body <- func.bodyOpt
      } {
        val fakeEr = ErrorReporter(
          _ => throw AssertionError("error reported during type hints insertion"),
          _ => throw AssertionError("fatal error during type hints insertion")
        )
        val resolCtx = ResolutionContext(program, typeVarsCtx, fakeEr)
        traverseScope(body, funSig.retType)(using resolCtx, program.globalValuesContext, subtypingCtx, dealiasingCtx)
      }
    }
    input
  }

  private def traverseScope(scope: Scope, expRetType: Type)
                           (using ResolutionContext, GlobalValuesContext, SubtypingContext, DealiasingContext): Unit = {
    for (instr <- scope.instructions.reverse) {
      traverseInstr(instr, expRetType)
    }
  }

  private def traverseInstr(instr: Instr, expRetType: Type)
                           (using resolutionCtx: ResolutionContext, globalValsCtx: GlobalValuesContext, subtypingCtx: SubtypingContext, dealiasingCtx: DealiasingContext): Unit = instr match {
    case Loop(cond, condVal, body, variables) =>
      for {
        LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- variables
        th <- typeHintsStore.getHints(condVal)
      } {
        typeHintsStore.addHint(beforeLoopVal, th)
        typeHintsStore.addHint(bodyLastVal, th)
      }
      traverseScope(body, expRetType)
      traverseScope(cond, expRetType)
    case Disjunction(condVal, thenBr, elseBr, variables) =>
      for {
        DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables
        th <- typeHintsStore.getHints(joinedVal)
      } {
        typeHintsStore.addHint(afterThenVal, th)
        typeHintsStore.addHint(afterElseVal, th)
      }
      traverseScope(thenBr, expRetType)
      traverseScope(elseBr, expRetType)
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
    case FieldRead(assigned, owner, field) => ()
    case InvokeFunc(assigned, receiver, func, typeArgs, args) =>
      proxyStore.getProxy(receiver).getOrElse(receiver) match {
        case receiverObj: UninterpretedConstIdValue =>
          for {
            objId <- globalValsCtx.getNameOfObject(receiverObj)
            funSig <- resolutionCtx.resolveFunSig(objId, func.funId).asOption
          } {
            val typesSubst = mutable.Map.from(funSig.typeParams.map(_.tid).zipCommons(typeArgs))
            val valsSubst = mutable.Map.empty[IdValue, Formula]
            typeHintsStore.getHints(assigned).headOption.foreach { hint =>
              unifyTypes(hint, funSig.retType)(using typesSubst)
            }
            for (((paramVal, paramTypeRaw), argVal) <- funSig.paramsWithoutThis.zipCommons(args)) {
              val paramTypeSubst = paramTypeRaw.substitute(typesSubst, valsSubst)
              typeHintsStore.addHint(argVal, paramTypeSubst)
              valsSubst.put(paramVal, argVal)
            }
          }
        case proxy => ()
      }
    case InvokeClosure(assigned, callee, args) => ()
    case Instantiate(assigned, classOrRecordName, typeArgs) => ()
    case MkClosure(assigned, params, body) => ()
    case TypeTest(assigned, testedValue, testedTypeId) => ()
    case Conversion(assigned, inValue, targetType) => ()
    case FieldWrite(owner, field, rhs) => ()
    case Return(retVal) =>
      typeHintsStore.addHint(retVal, expRetType)
    case Panic(msg) => ()
    case Cast(inValue, target) => ()
    case Drop(droppedValue) => ()
    case LocalDecl(localId, tpe) => ()
    case scope: Scope =>
      traverseScope(scope, expRetType)
    case Smartcast(formula, tpe) =>
      throw AssertionError(s"unexpected smartcast in ${classOf[TypeHintsInserter].getSimpleName}")
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
          (hintTypeArg, shapeTypeArg) <- hintTypeArgs.zipCommons(upcastShapeType.typeArgs)
        } {
          unifyTypes(hintTypeArg, shapeTypeArg)
        }
      case (ClosureType(hintParams, hintResult), ClosureType(shapeParams, shapeResult)) =>
        for ((ht, st) <- hintParams.zipCommons(shapeParams)){
          unifyTypes(ht, st)
        }
        unifyTypes(hintResult, shapeResult)
      case _ => ()
      // TODO also handle IntersectionTypes and UnionTypes?
    }
  }

}
