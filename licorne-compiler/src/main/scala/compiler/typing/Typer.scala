package compiler.typing

import compiler.identifiers.*
import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.SSA.*
import compiler.irs.ssa.SSA.HybridCastMode.{AssertNonNull, AssertPredicate}
import compiler.irs.ssa.{ClosureTypingTarget, FieldResolutionTarget, InvocationTarget, SSA}
import compiler.lang
import compiler.lang.*
import compiler.lang.Field.*
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.*
import compiler.lang.Variance.*
import compiler.pipeline.CompilationStep
import compiler.reasoning.Recurrence.Monotonicity.*
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.reasoning.*
import compiler.typing.contexts.*
import compiler.typing.contexts.ResolutionContext.{FieldResolResult, FuncResolResult}
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult
import compiler.typing.contexts.TypeParamsContext.processTypeParamsAccumulating
import compiler.util.{SeqSet, findUnique, mapVals}
import compiler.valproxies.{BoundMode, BranchingInfo, ProxyStore}
import compiler.valuesconversion.GlobalValuesContext
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized

import scala.collection.immutable.SeqMap
import scala.collection.mutable
import scala.reflect.ClassTag


final class Typer(
                   executionEnvirOpt: Option[ExecutionEnvironment],
                   dealiasingCtx: DealiasingContext,
                   resolutionCtx: ResolutionContext,
                   typeVarsCtx: TypeVariablesContext,
                   subtypingCtx: SubtypingContext,
                   meetJoin: MeetJoinComputer,
                   proxyStore: ProxyStore,
                   typeCandidatesStore: TypeCandidatesStore,
                   heapVarsTypeStore: HeapVarsTypeStore,
                   solver: Solver,
                   simplifier: Simplifier,
                   absInt: AbstractInterpreter,
                   globalValuesCtx: GlobalValuesContext,
                   er: ErrorReporter,
                   closuresCollectorFunc: ClosureInfo => Unit = _ => (),
                   allowWriteToIR: Boolean = true
                 )(using CompilationStep) {

  // @formatter:off
  private given DealiasingContext = dealiasingCtx
  private given ResolutionContext = resolutionCtx
  private given SubtypingContext = subtypingCtx
  private given MeetJoinComputer = meetJoin
  private given ProxyStore = proxyStore
  private given Solver = solver
  private given Simplifier = simplifier
  private given Typer = this
  private given GlobalValuesContext = globalValuesCtx
  // @formatter:on

  import globalValuesCtx.itValue

  private val nonZeroIntType = RefinedType(IntType, LogicalNot(Equality(itValue, IntConst(0))))

  private def isPurityRequired: Boolean = executionEnvirOpt.exists(_.requiresPurityInBody)

  def copyNotAllowedToWriteToIR: Typer = Typer(executionEnvirOpt, dealiasingCtx, resolutionCtx, typeVarsCtx, subtypingCtx,
    meetJoin, proxyStore, typeCandidatesStore, heapVarsTypeStore, solver, simplifier, absInt, globalValuesCtx, er,
    closuresCollectorFunc, allowWriteToIR = false)

  def typeScopeInstructions(scope: Scope, branchInfo: BranchingInfo)(using TypeParamsContext): Unit = {
    solver.onNewFrame {
      scope.resetHasExited()
      scope.forTraversal { instrIter =>
        applyBranchInfo(scope, branchInfo)
        var stop = false
        while (instrIter.hasNext && !stop) {
          val instr = instrIter.next()
          if (!instr.isInstanceOf[Drop]) {
            scope.reportHasExitedIfNeeded(er, instr.getPosition)
          }
          if (scope.hasExited){
            stop = true
          } else {
            typeInstr(instr, scope, branchInfo)
          }
        }
      }
    }
    for ((f1, f2) <- scope.persistingEqualities) {
      solver.assertEq(f1, f2, SimplifiedType.from(scope.detectCurrentType(f1)))
    }
  }

  def typeInstr(instr: RealInstr, currScope: Scope, branchInfo: BranchingInfo)
               (using typeParamsCtx: TypeParamsContext): Unit = {

    def saveEquality(f1: Formula, f2: Formula, persist: Boolean = false): Unit = {
      if (f1.isPure && f2.isPure) {
        currScope.eMerge(f1, f2, persist)
        solver.assertEq(f1, f2, SimplifiedType.from(currScope.detectCurrentType(f1)))
      }
    }

    instr match {

      case loop@Loop(condScope, condVal, bodyScope, loopUpdatedVars) =>
        val (infoIfCondTrueFirstGuess, _) = proxyStore.extractRawBranchingInfos(condVal, branchInfo, currScope)
        for (varData@LoopVarData(varId, beforeLoopVal, inCondVal, bodyLastVal, varDefScope) <- loopUpdatedVars) {
          (for {
            recurrence <- varData.recurrenceOpt
            monotonicity <- Some(recurrence.computeMonotonicity(this.copyNotAllowedToWriteToIR, solver, currScope)).filter(_ != NonMonotonous)
          } yield {
            val boundMode = if monotonicity == NonDecreasing then BoundMode.Upper else BoundMode.Lower
            val inferredBound = infoIfCondTrueFirstGuess.boundFor(inCondVal, boundMode, solver)
            val preIterationBoundOpt = proxyStore.developDeep(beforeLoopVal)
            val inferredInBodyType = simplifier.simplify(
              monotonicity match {
                case Constant => preIterationBoundOpt.map(IntRangeType.singleton).getOrElse(IntType)
                case NonDecreasing => IntRangeType(preIterationBoundOpt, inferredBound)
                case NonIncreasing => IntRangeType(inferredBound, preIterationBoundOpt)
                case NonMonotonous => IntType
              }
            )
            val inBodyType = currScope.getLocalValuesContextUnsafe.valueOf(varId).declOpt match {
              case Some(LocalDecl(_, tpe)) => simplifier.simplify(IntersectionType(tpe, inferredInBodyType))
              case None => inferredInBodyType
            }
            val feedbackType =
              absInt.interpretUnderAssumptions(recurrence.induct, Map(recurrence.inductVal -> inBodyType), None)(using currScope.getLocalValuesContextUnsafe.globalCtx).getOrElse {
                preIterationBoundOpt match {
                  case Some(preIterationBound) =>
                    simplifier.simplify(
                      monotonicity match {
                        case Constant => IntRangeType.singleton(preIterationBound)
                        case NonDecreasing => IntRangeType.ofLowerBound(preIterationBound)
                        case NonIncreasing => IntRangeType.ofUpperBound(preIterationBound)
                        case NonMonotonous => IntType
                      }
                    )
                  case None => IntType
                }
              }
            val inCondType = meetJoin.computeJoin(inBodyType, feedbackType)
            varDefScope.saveType(inCondVal, inCondType) // after loop
            condScope.saveSmartcast(inCondVal, inCondType) // inside condition
            bodyScope.saveSmartcast(inCondVal, inBodyType) // inside body
          }) orElse {
            // TODO lookup proxy of bodyLastVal to see if we can infer its type (maybe this can be unified with the "next step" interpretation in the previous case)
            val tpe =
              currScope.getLocalValuesContextUnsafe
                .valueOf(varId)
                .asInstanceOf[KnownAndInitialized]
                .declarationTypeAnnotOpt
                .orElse(typeCandidatesStore.getCandidates(inCondVal).find { candidate =>
                  subtypingCtx.isSubtype(currScope.detectCurrentType(beforeLoopVal), candidate)
                })
                .getOrElse(currScope.detectCurrentType(beforeLoopVal).ignoreRangesShallow)
            varDefScope.saveType(inCondVal, tpe)
            Some(())
          }
        }
        typeScopeInstructions(condScope, BranchingInfo.empty)
        subtypingCtx.enforceIsSubtype(condScope.detectCurrentType(condVal), BoolType, s"loop condition must have type $BoolType", loop.getPosition)
        val (infoIfCondTrue, infoIfCondFalse) = proxyStore.extractRawBranchingInfos(condVal, branchInfo, currScope)
        typeScopeInstructions(bodyScope, infoIfCondTrue)
        for {
          varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal, varDefScope) <- loopUpdatedVars
        } {
          val typeAtEndOfBody = bodyScope.detectCurrentType(bodyLastVal)
          val typeInCond = condScope.detectCurrentType(condVal)
          lazy val msg = currScope.getLocalValuesContextUnsafe.valueOf(varId) match {
            case KnownAndInitialized(value, defScope, reassigStatus, Some(declTypeAnnot)) =>
              s"update of variable $varId in loop violate its type annotation $declTypeAnnot"
            case _ =>
              s"inferred incorrect type $typeInCond for variable $varId at loop body start, please provide a type annotation at variable declaration site"
          }
          subtypingCtx.enforceIsSubtype(typeAtEndOfBody, typeInCond, msg, loop.getPosition)
          val beforeLoopType = currScope.detectCurrentType(beforeLoopVal)
          val afterLoopType = meetJoin.computeJoin(beforeLoopType, typeAtEndOfBody)
          currScope.saveSmartcast(condVal, afterLoopType)
        }
        applyBranchInfo(currScope, infoIfCondFalse)

      case disjunction@Disjunction(condVal, thenBr, elseBr, variables) =>
        val condType = currScope.computeCurrentType(condVal, disjunction.getPosition)
        subtypingCtx.enforceIsSubtype(condType, BoolType, s"condition must have type $BoolType", disjunction.getPosition)
        val (infoIfCondTrue, infoIfCondFalse) = proxyStore.extractRawBranchingInfos(condVal, branchInfo, currScope)
        typeScopeInstructions(thenBr, infoIfCondTrue)
        typeScopeInstructions(elseBr, infoIfCondFalse)
        for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
          val afterThenValType = thenBr.detectCurrentType(afterThenVal)
          val afterElseValType = elseBr.detectCurrentType(afterElseVal)
          val joinType = {
            if elseBr.hasExited then afterThenValType
            else if thenBr.hasExited then afterElseValType
            else typeCandidatesStore.getCandidates(joinedVal)
              .find(candType => subtypingCtx.isSubtype(afterThenVal, afterThenValType, candType, thenBr) && subtypingCtx.isSubtype(afterElseVal, afterElseValType, candType, elseBr))
              .getOrElse(meetJoin.computeJoin(afterThenValType, afterElseValType))
          }
          currScope.saveType(joinedVal, joinType)
        }
        if (elseBr.hasExited) {
          // in that case, variables are remapped to their value in thenScope by the SSAGenerator
          applyBranchInfo(currScope, infoIfCondTrue)
          currScope.absorbSmartcastsEGraphFrom(thenBr)
        } else if (thenBr.hasExited) {
          // in that case, variables are remapped to their value in elseScope by the SSAGenerator
          applyBranchInfo(currScope, infoIfCondFalse)
          currScope.absorbSmartcastsEGraphFrom(elseBr)
        }
        if (thenBr.hasExited && elseBr.hasExited) {
          currScope.markHasExited()
        }

      case staticTypeAssert@StaticTypeAssert(value, rawType) =>
        val valueType = currScope.computeCurrentType(value, staticTypeAssert.getPosition)
        val instantiatedType = instantiateType(rawType, None, currScope, staticTypeAssert.getPosition)
        irModif {
          staticTypeAssert.tpe = instantiatedType
        }
        subtypingCtx.enforceIsSubtypeExpAct(value, valueType, instantiatedType, "type ascription", currScope, staticTypeAssert.getPosition)

      case assignVal@AssignVal(assigned, src) =>
        val srcType = tryToApplyCandidates(src, currScope.computeCurrentType(src, assignVal.getPosition), currScope, assignVal.getPosition)
        val assignedType = assigned match {
          case idVal: LocalIdValue =>
            currScope.getLocalValuesContextUnsafe.valueOf(idVal.id).declOpt match {
              case Some(decl) =>
                val isSubT = subtypingCtx.enforceIsSubtypeExpAct(src, srcType, decl.tpe, s"assignment to ${idVal.id}", currScope, assignVal.getPosition)
                if isSubT then srcType else decl.tpe
              case None => srcType
            }
          case _ => srcType
        }
        currScope.saveType(assigned, assignedType)
        saveEquality(assigned, src)

      case AssignIntConst(assigned, src) =>
        currScope.saveType(assigned, IntRangeType.singleton(src))
        saveEquality(assigned, IntConst(src))

      case AssignBoolConst(assigned, src) =>
        currScope.saveType(assigned, BoolType)
        saveEquality(assigned, BoolConst(src))

      case AssignStringConst(assigned, src) =>
        currScope.saveType(assigned, StringType)
        saveEquality(assigned, StringConst(src))

      case neg@NumNeg(assigned, operand) => assignTarget(assigned, currScope) {
        typeNumericNeg(operand, currScope, neg.getPosition)
      }

      case add@Add(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeNumericBinop(lhs, rhs, currScope, absInt.typePlusType, Operator.Plus, add.getPosition)
      }

      case sub@Sub(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeNumericBinop(lhs, rhs, currScope, absInt.typeMinusType, Operator.Minus, sub.getPosition)
      }

      case mul@Mul(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeNumericBinop(lhs, rhs, currScope, absInt.typeTimesType, Operator.Times, mul.getPosition)
      }

      case div@Div(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeNumericBinop(lhs, rhs, currScope, absInt.typeDivType, Operator.Div, div.getPosition)
      }

      case rem@Rem(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeNumericBinop(lhs, rhs, currScope, absInt.typeModuloType(proxyStore.developDeep(rhs)), Operator.Modulo, rem.getPosition)
      }

      case neg@LogicNeg(assigned, operand) => assignTarget(assigned, currScope) {
        typeLogicalNeg(operand, currScope, neg.getPosition)
      }

      case leq@Leq(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeComparisonBinop(lhs, rhs, currScope, Operator.LessThan, leq.getPosition)
      }

      case lt@Lt(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeComparisonBinop(lhs, rhs, currScope, Operator.LessThan, lt.getPosition)
      }

      case Equal(assigned, lhs, rhs) =>
        currScope.saveType(assigned, BoolType)

      case invk@InvokeFunc(assigned, receiver, func, typeArgsRaw, args) if func.isNotResolvedYet =>
        val instTypeArgs = typeArgsRaw.map(instantiateType(_, None, currScope, invk.getPosition))
        val (returnTypeRaw, instRecTypeArgs, instFunTypeArgs) = resolveFunSigAndCheckArgs(receiver, func, instTypeArgs, args, currScope, invk.getPosition)
        if (instRecTypeArgs.nonEmpty) {
          irModif {
            invk.typeArgs = instFunTypeArgs
          }
        }
        val returnType =
          if func.isResolvedAndPure
          then proxyStore.developDeep(assigned).flatMap(currScope.smartcastFor(_, saveSmartcasts = true)).getOrElse(returnTypeRaw)
          else returnTypeRaw
        currScope.saveType(assigned, returnType)
        tryToResolveTypeVarsUsingCandidates(assigned, returnType)
        if (func.isResolved) {
          currScope.markHasExitedIfNothing(returnType)
        }

      case invkClosure@InvokeClosure(assigned, callee, closureTypingTarget, args) if closureTypingTarget.isNotResolvedYet =>
        val calleeType = currScope.computeCurrentType(callee, invkClosure.getPosition)
        val argsValsAndTypes = args.map(arg => Some(arg) -> currScope.computeCurrentType(arg, invkClosure.getPosition))
        val tpe = typeClosureCall(calleeType, closureTypingTarget, argsValsAndTypes, currScope, invkClosure.getPosition)
        currScope.saveType(assigned, tpe)
        tryToResolveTypeVarsUsingCandidates(assigned, tpe)

      case fr@FieldRead(assigned, owner, field) if field.isNotResolvedYet =>
        val ownerType = currScope.computeCurrentType(owner, fr.getPosition)
        val tpe = resolveFieldAccess(owner, ownerType, field, currScope, needsWriteAccess = false, fr.getPosition)
        proxyStore.developDeep(assigned).flatMap(currScope.smartcastFor(_, saveSmartcasts = true)) match {
          case Some(smartcastType) =>
            currScope.saveType(assigned, smartcastType)
          case None =>
            currScope.saveType(assigned, tpe)
        }

      case fw@FieldWrite(owner, fieldResolTarget, rhs) if fieldResolTarget.isNotResolvedYet =>
        val ownerType = currScope.computeCurrentType(owner, fw.getPosition)
        val fieldTypeRaw = resolveFieldAccess(owner, ownerType, fieldResolTarget, currScope, needsWriteAccess = true, fw.getPosition)
        val fieldTypeSubst = fieldResolTarget.getReceiverSigOpt match {
          case Some(recSig) => fieldTypeRaw.substitute(Map.empty, Map(recSig.sigScope.getLocalValuesContextUnsafe.getThisValue.get -> owner))
          case None => fieldTypeRaw
        }
        val rhsType = currScope.computeCurrentType(rhs, fw.getPosition)
        tryToResolveTypeVars(fieldTypeSubst, rhsType)
        subtypingCtx.enforceIsSubtypeExpAct(rhs, rhsType, fieldTypeSubst, s"assignment to field ${fieldResolTarget.fieldId}", currScope, fw.getPosition)

      case instr: (InvokeFunc | InvokeClosure | FieldRead | FieldWrite) =>
        throw AssertionError("typing phase run more than once on the same piece of code: " + instr.getClass.getSimpleName)

      case heapVarRd@HeapVarRead(assigned, heapVar) =>
        val tpe = heapVarsTypeStore.getTypeUnsafe(heapVar)
        currScope.saveType(assigned, tpe)
        forbiddenIfImpure(s"illegal access to impure closure-captured variable $heapVar in a pure method or closure", heapVarRd.getPosition)

      case heapVarWr@HeapVarWrite(heapVar, newValue) =>
        val newValType = currScope.computeCurrentType(newValue, heapVarWr.getPosition)
        heapVarsTypeStore.getType(heapVar) match {
          case Some(expType) =>
            subtypingCtx.enforceIsSubtypeExpAct(newValue, newValType, expType, "heap-allocated variable assignment", currScope, heapVarWr.getPosition)
          case None =>
            // TODO maybe try to save refined types also here, instead of falling back to the range-erased type?
            heapVarsTypeStore.saveType(heapVar, newValType.ignoreRangesShallow)
        }
        forbiddenIfImpure(s"illegal access to impure closure-captured variable $heapVar in a pure method or closure", heapVarWr.getPosition)

      case mkHeapVar@MkHeapVar(assigned) =>
        // defer typing to first write
        ()

      case instantiate@Instantiate(assigned, classOrRecordName, typeArgsRaw, fieldsInit) =>
        assigned match {
          case intermIdVal: IntermediateIdValue =>
            intermIdVal.nameHint = s"new_${classOrRecordName.nonPrefixedId}"
          case _ => ()
        }
        resolutionCtx.resolveTypeSigAs[UserInstantiableTypeSig](classOrRecordName) match {
          case Some(typeSig) =>
            val (typesSubst, instantiatedTypeArgs) = instantiateTypes(typeSig.typeParams, typeArgsRaw, subtypingCtx, currScope, instantiate.getPosition, Some(s"instantiation of $classOrRecordName"))
            irModif {
              instantiate.typeArgs = instantiatedTypeArgs
            }
            val tpe = typeInstInitializers(instantiate, typeSig, currScope, typesSubst)
            currScope.saveType(assigned, tpe)
          case None =>
            er.reportError(s"type $classOrRecordName not found or not instantiable", instantiate.getPosition)
        }

      case mkClosure@MkClosure(assigned, params, body, knownPureBeforeTyping) =>
        val id = NormalFunOrVarId(assigned match {
          case assigned: NamedIdValue => assigned.irDescr
          case assigned: IntermediateIdValue => assigned.toString
        })
        val resultTypeVar = typeVarsCtx.newTypeVariable(id, None, None, typeParamsCtx, body.getPosition)
        val paramTypesB = List.newBuilder[Type]
        for ((paramVal, paramType) <- params) {
          body.saveType(paramVal, paramType)
          paramTypesB.addOne(paramType)
        }
        val isPure = knownPureBeforeTyping || typeCandidatesStore.hasPureClosureCandidateFor(assigned)
        irModif {
          mkClosure.isPure = isPure
        }
        currScope.saveType(assigned, ClosureType(paramTypesB.result(), resultTypeVar, isPure))
        executionEnvirOpt match {
          case Some(executionEnvir) =>
            val closureInfo = ClosureInfo(params, body, resultTypeVar, branchInfo, isPure, executionEnvir, typeParamsCtx)
            closuresCollectorFunc(closureInfo)
          case None =>
            er.reportError("closure creation is not allowed in this position", mkClosure.getPosition)
        }

      case tt@TypeTest(assigned, testedValue, testedTypeId) =>
        checkDowncast(testedValue, testedTypeId, currScope, tt.getPosition)
        currScope.saveType(assigned, BoolType)

      case cast@Cast(inValue, target) =>
        checkDowncast(inValue, target, currScope, cast.getPosition).foreach { assertedType =>
          currScope.saveSmartcast(inValue, assertedType)
          proxyStore.developDeep(inValue).foreach { proxy =>
            currScope.saveSmartcast(proxy, assertedType)
          }
        }

      case hybridCast@HybridCast(inValue) =>
        val preType = dealiasingCtx.dealiasType(currScope.computeCurrentType(inValue, hybridCast.getPosition)).withTypeVarsExpanded
        val targetTypeOpt = typeCandidatesStore.getCandidates(inValue).headOption.map(h => dealiasingCtx.dealiasType(h.withTypeVarsExpanded).withTypeVarsExpanded)
        (preType, targetTypeOpt) match {
          case (preType, Some(targetType)) if subtypingCtx.isSubtype(preType, targetType) =>
            er.warn(s"useless use of !! : I inferred target type $targetType, which is a supertype of the input type $preType", hybridCast.getPosition)
          case (NullableType(nullatedType), Some(targetType)) if subtypingCtx.isSubtype(nullatedType, targetType) =>
            irModif {
              hybridCast.setMode(AssertNonNull)
            }
            currScope.saveSmartcast(inValue, nullatedType)
          case (preType, Some(targetType)) =>
            val RefinedType(inBase, inPred) = preType.asRefinedType.flattenedRefinement
            val RefinedType(targetBase, targetPred) = targetType.asRefinedType.flattenedRefinement
            if (subtypingCtx.isSubtype(inBase, targetBase)) {
              irModif {
                hybridCast.setMode(AssertPredicate(targetPred))
              }
              currScope.saveSmartcast(inValue, targetType)
            } else {
              er.reportError(s"hybrid cast is not sufficient to cast $inBase to $targetBase", hybridCast.getPosition)
            }
          case (preType, None) =>
            er.reportError("hybrid cast target type could not be resolved, please provide a type annotation", hybridCast.getPosition)
        }

      case conv@Conversion(assigned, inValue, targetType) =>
        val inValType = requireNonNullable(currScope.computeCurrentType(inValue, conv.getPosition).ignoreRangesShallow, "converted value", conv.getPosition)
        if (inValType == targetType || TypeConversion.conversionFor(inValType, targetType).isDefined) {
          currScope.saveType(assigned, targetType)
        } else {
          er.reportError(s"impossible conversion: $inValType to $targetType", conv.getPosition)
        }

      case ret@Return(retVal) =>
        executionEnvirOpt match {
          case Some(executionEnvir) =>
            val unitVal = currScope.getLocalValuesContextUnsafe.globalCtx.unitVal
            if (executionEnvir.expectedResultType == UnitType && retVal != unitVal && !proxyStore.developDeep(retVal).contains(unitVal)) {
              er.warn(s"returned value has no effect, since return type is $UnitType", ret.getPosition)
            }
            val retValType = currScope.computeCurrentType(retVal, ret.getPosition)
            subtypingCtx.enforceIsSubtypeExpAct(retVal, retValType, executionEnvir.expectedResultType, "return value", currScope, ret.getPosition)
          case None =>
            er.reportError("unexpected return in this position", ret.getPosition)
        }
        currScope.markHasExited()

      case panic@Panic(msg) =>
        val msgType = currScope.computeCurrentType(msg, panic.getPosition)
        subtypingCtx.enforceIsSubtype(msgType, StringType, s"panic message should have type $StringType", panic.getPosition)
        currScope.markHasExited()

      case localDecl@LocalDecl(localId, tpe) =>
        irModif {
          localDecl.tpe = instantiateType(tpe, None, currScope, localDecl.getPosition)
        }

      case Drop(droppedValue) => ()

      case scope: Scope =>
        typeScopeInstructions(scope, BranchingInfo.empty)
    }
  }

  private def typeInstInitializers(instantiate: Instantiate, typeSig: UserInstantiableTypeSig, currScope: Scope, typesSubst: Map[TypeIdentifier, Type])
                                  (using TypeParamsContext): Type = {
    val assigned = instantiate.assigned
    val newInstanceTypeBase = typeSig.toType(typesSubst)
    tryToResolveTypeVarsUsingCandidates(assigned, newInstanceTypeBase)
    val fieldsInitArgsSubst = mutable.Map.empty[IdValue, Formula]
    val returnTypePredParts = mutable.ListBuffer.empty[Formula]
    val expFieldsIter = typeSig.fields.iterator
    val actFieldsIter = instantiate.fieldsInit.iterator
    var errorFlag = false
    while (!errorFlag && expFieldsIter.hasNext && actFieldsIter.hasNext) {
      val (_, fld) = expFieldsIter.next()
      val (initFldId, rhsVal) = actFieldsIter.next()
      if (initFldId == fld.id) {
        val rhsValType = currScope.getCurrentTypeOf(rhsVal, saveSmartcastsInIR = true)
        val expType = fld.tpe.substitute(typesSubst, fieldsInitArgsSubst)
        subtypingCtx.enforceIsSubtypeExpAct(rhsVal, rhsValType, expType, s"initialization of field $initFldId", currScope, instantiate.getPosition)
        fld match {
          case fld: StableField =>
            val fldResolTarget = FieldResolutionTarget(fld.id)
            fldResolTarget.resolve(typeSig, expType)
            val itSelect = Select(itValue, fldResolTarget)
            returnTypePredParts.addOne(Equality(itSelect, rhsVal))
            val assignedSelect = Select(assigned, fldResolTarget)
            solver.assertEq(assignedSelect, rhsVal, SimplifiedType.from(rhsValType))
            fieldsInitArgsSubst.put(fld.value, rhsVal)
          case _ => ()
        }
      } else {
        er.reportError(s"expected initializer of field ${fld.id}, found label $initFldId", instantiate.getPosition)
        errorFlag = true
      }
    }
    if (!errorFlag && expFieldsIter.hasNext) {
      er.reportError(s"missing initializer for field ${expFieldsIter.next()._1}", instantiate.getPosition)
      errorFlag = true
    }
    if (!errorFlag && actFieldsIter.hasNext) {
      er.reportError(s"unexpected initializer for field ${actFieldsIter.next()._1}", instantiate.getPosition)
      errorFlag = true
    }
    val newInstanceType =
      if returnTypePredParts.isEmpty then newInstanceTypeBase
      else {
        val rawPred = returnTypePredParts.reduce(LogicalAnd(_, _))
        val pred = proxyStore.developNearest(rawPred).getOrElse(rawPred)
        RefinedType(newInstanceTypeBase, pred)
      }
    newInstanceType
  }

  private def tryToApplyCandidates(srcVal: IdValue, regularType: Type, currScope: Scope, posOpt: Option[Position])(using TypeParamsContext): Type = {
    val validatedCandidates = typeCandidatesStore.getCandidates(srcVal).toList.filter(subtypingCtx.canProveHasType(srcVal, regularType, _, currScope))
    if validatedCandidates.isEmpty then regularType
    else IntersectionType(SeqSet(regularType +: validatedCandidates))
  }

  private def tryToResolveTypeVarsUsingCandidates(value: IdValue, tpe: Type)(using TypeParamsContext): Unit = {
    for (cand <- typeCandidatesStore.getCandidates(value)) {
      tryToResolveTypeVars(cand, tpe)(using tvResolMode = TypeVarsResolMode.ParamsAndArgs)
    }
  }

  def typeFormula(formula: Formula, scope: Scope, posOpt: Option[Position], suspendReporting: Boolean = false)
                 (using typeParamsCtx: TypeParamsContext): Type = er.withReportingSuspendedIf(suspendReporting) {
    val tpe = scope.smartcastFor(formula, saveSmartcasts = true).getOrElse {
      val rawType = formula match {
        case value: IdValue =>
          val tpe = scope.detectCurrentType(value)
          value match {
            case UninterpretedConstIdValue(name, definingScope, uid) if tpe == NothingType =>
              er.reportError(s"object not found: $name", posOpt)
            case _ => ()
          }
          tpe
        case IntConst(value) => IntType
        case BoolConst(value) => BoolType
        case StringConst(value) => StringType
        case sel@Select(owner, field) if field.isResolved =>
          field.getInstantiatedTypeUnsafe
        case sel@Select(owner, field) if field.isNotResolvedYet =>
          val ownerType = typeFormula(owner, scope, posOpt)
          val tpe = resolveFieldAccess(owner, ownerType, field, scope, needsWriteAccess = false, posOpt)
          scope.smartcastFor(sel, saveSmartcasts = false).getOrElse(tpe)
        case Select(owner, field) =>
          assert(field.isUnresolvable)
          NothingType
        case FunCall(receiver, func, typeArgs, args) if func.isResolved => func.getInstantiatedReturnTypeUnsafe
        case call@FunCall(receiver, func, typeArgs, args) if func.isNotResolvedYet =>
          val (tpe, receiverTypeArgsInst, funTypeArgsInst) = resolveFunSigAndCheckArgs(receiver, func, typeArgs, args, scope, posOpt)
          if (funTypeArgsInst.nonEmpty) {
            irModif {
              call.typeArgs = funTypeArgsInst
            }
          }
          tpe
        case FunCall(receiver, func, typeArgs, args) =>
          assert(func.isUnresolvable)
          NothingType
        case ClosureCall(callee, closureTypingTarget, args) if closureTypingTarget.isResolved => closureTypingTarget.getTypeUnsafe.result
        case ClosureCall(callee, closureTypingTarget, args) if closureTypingTarget.isNotResolvedYet =>
          val calleeType = typeFormula(callee, scope, posOpt)
          val argsWithTypes = args.map(arg => Some(arg) -> typeFormula(arg, scope, posOpt))
          typeClosureCall(calleeType, closureTypingTarget, argsWithTypes, scope, posOpt)
        case ClosureCall(callee, closureTypingTarget, args) =>
          assert(closureTypingTarget.isUnresolvable)
          NothingType
        case PureClosureValue(params, body, closureVal) =>
          // TODO check that this is safe
          scope.detectCurrentType(closureVal)
        case Plus(lhs, rhs) =>
          typeNumericBinop(lhs, rhs, scope, absInt.typePlusType, Operator.Plus, posOpt)
        case Neg(operand) =>
          typeNumericNeg(operand, scope, posOpt)
        case Times(lhs, rhs) =>
          typeNumericBinop(lhs, rhs, scope, absInt.typeTimesType, Operator.Times, posOpt)
        case DivBy(lhs, rhs) =>
          typeNumericBinop(lhs, rhs, scope, absInt.typeDivType, Operator.Div, posOpt)
        case Modulo(lhs, rhs) =>
          typeNumericBinop(lhs, rhs, scope, absInt.typeModuloType(Some(rhs)), Operator.Modulo, posOpt)
        case LogicalAnd(lhs, rhs) =>
          typeLogicalBinop(lhs, rhs, scope, Operator.And, posOpt)
        case LogicalOr(lhs, rhs) =>
          typeLogicalBinop(lhs, rhs, scope, Operator.Or, posOpt)
        case LogicalNot(operand) =>
          typeLogicalNeg(operand, scope, posOpt)
        case LessOrEq(lhs, rhs) =>
          typeComparisonBinop(lhs, rhs, scope, Operator.LessOrEq, posOpt)
        case LessThan(lhs, rhs) =>
          typeComparisonBinop(lhs, rhs, scope, Operator.LessThan, posOpt)
        case Equality(lhs, rhs) =>
          typeFormula(lhs, scope, posOpt)
          typeFormula(rhs, scope, posOpt)
          BoolType
        case TypePredicate(subject, tpe) =>
          checkDowncast(subject, tpe, scope, posOpt)
          BoolType
        case Phi(terms) =>
          meetJoin.computeJoin(terms.map(typeFormula(_, scope, posOpt, suspendReporting)))
      }
      rawType.withDependenciesTransformed(d => proxyStore.developNearest(d).getOrElse(d))
    }
    if (formula.isPure) {
      solver.takeType(formula, tpe)
    }
    tpe
  }

  private def detectTypeForSmartcast(formula: Formula, scope: Scope)(using TypeParamsContext): Option[Type] = formula match {
    case value: IdValue =>
      Some(scope.detectCurrentType(value))
    case Select(owner, field) =>
      if (field.isResolved) {
        Some(field.getInstantiatedTypeUnsafe)
      } else None
    case funCall@FunCall(receiver, func, typeArgsRaw, args) =>
      if (func.isResolved) {
        Some(func.getInstantiatedReturnTypeUnsafe)
      } else None
    case ClosureCall(callee, closureTypingTarget, args) =>
      detectTypeForSmartcast(callee, scope) match {
        case Some(ClosureType(params, result, enforcedPure)) => Some(result)
        case _ => None
      }
    case _ => None
  }

  private def assignTarget(assignmentTarget: IdValue, currScope: Scope)
                          (tpe: Type)
                          (using TypeParamsContext): Unit = {
    currScope.saveType(assignmentTarget, tpe)
  }

  private def typeNumericBinop(lhs: Formula, rhs: Formula, currScope: Scope,
                               absIntFunc: (Type, Type) => Option[Type],
                               op: Operator, posOpt: Option[Position])
                              (using TypeParamsContext): Type = {
    val lhsType = dealiasingCtx.dealiasType(typeFormula(lhs, currScope, posOpt)).withTypeVarsExpanded
    val rhsType = dealiasingCtx.dealiasType(typeFormula(rhs, currScope, posOpt)).withTypeVarsExpanded
    val isDivOperator = op == Operator.Div || op == Operator.Modulo
    val mayBeDivByZero =
      isDivOperator && subtypingCtx.isSubtype(lhsType, IntType) && subtypingCtx.isSubtype(rhsType, IntType)
        && !subtypingCtx.isSubtype(rhs, rhsType, nonZeroIntType, currScope)
    if (mayBeDivByZero) {
      val rhsDescr =
        proxyStore.developDeep(rhs).orElse(Some(rhs)) match {
          case Some(f) => s" $f"
          case None => ""
        }
      er.reportError(s"I cannot prove that right-hand side$rhsDescr of operator '$op' cannot be zero", posOpt)
    }
    absIntFunc(forceRange(lhsType.withTypeVarsExpanded), forceRange(rhsType.withTypeVarsExpanded)) match {
      case Some(tpe) => tpe
      case None =>
        er.reportError(s"no operator $op found for types $lhsType and $rhsType", posOpt)
        NothingType
    }
  }

  private def typeLogicalBinop(lhs: Formula, rhs: Formula, currScope: Scope, op: Operator, posOpt: Option[Position])
                              (using TypeParamsContext): Type = {
    val lhsType = dealiasingCtx.dealiasType(typeFormula(lhs, currScope, posOpt)).withTypeVarsExpanded
    subtypingCtx.enforceIsSubtypeExpAct(lhsType, BoolType, s"operand of $op", posOpt)
    val rhsType = dealiasingCtx.dealiasType(typeFormula(rhs, currScope, posOpt)).withTypeVarsExpanded
    subtypingCtx.enforceIsSubtypeExpAct(rhsType, BoolType, s"operand of $op", posOpt)
    BoolType
  }

  private def typeComparisonBinop(lhs: Formula, rhs: Formula, currScope: Scope, op: Operator, posOpt: Option[Position])
                                 (using TypeParamsContext): Type = {
    // TODO warning if result is known (true or false)?
    val lhsType = dealiasingCtx.dealiasType(typeFormula(lhs, currScope, posOpt)).withTypeVarsExpanded
    val expectedOperandType = lhsType.ignoreRangesShallow match {
      case tpe@(IntType | DoubleType) => tpe
      // TODO be careful when compiling this, maybe we need to enforce that both types are equal
      case _ => UnionType(IntType, DoubleType)
    }
    subtypingCtx.enforceIsSubtypeExpAct(lhsType, expectedOperandType, s"operand of $op", posOpt)
    val rhsType = dealiasingCtx.dealiasType(typeFormula(rhs, currScope, posOpt)).withTypeVarsExpanded
    subtypingCtx.enforceIsSubtypeExpAct(rhsType, expectedOperandType, s"operand of $op", posOpt)
    BoolType
  }

  private def typeNumericNeg(operand: Formula, currScope: Scope, posOpt: Option[Position])
                            (using TypeParamsContext): Type = {
    val operandType = dealiasingCtx.dealiasType(typeFormula(operand, currScope, posOpt)).withTypeVarsExpanded
    val negatedType = absInt.unaryNegType(forceRange(operandType.withTypeVarsExpanded)) match {
      case Some(negType) => negType
      case None =>
        er.reportError(s"no unary operator ${Operator.Modulo} found for operand type $operandType", posOpt)
        NothingType
    }
    negatedType
  }

  private def typeLogicalNeg(operand: Formula, currScope: Scope, posOpt: Option[Position])
                            (using TypeParamsContext): Type = {
    val operandType = dealiasingCtx.dealiasType(typeFormula(operand, currScope, posOpt)).withTypeVarsExpanded
    subtypingCtx.enforceIsSubtypeExpAct(operandType, BoolType, "negation operand", posOpt)
    BoolType
  }

  private def forceRange(tpe: Type)(using TypeParamsContext): Type = simplifier.simplify(tpe) match {
    case RefinedType(baseType, predicate) =>
      forceRange(baseType)
    case intersection@IntersectionType(types) =>
      types.find(_.isInstanceOf[IntRangeType]).getOrElse(intersection)
    case tpe => tpe
  }

  private def checkDowncast(subject: Formula, tid: TypeIdentifier, currScope: Scope, posOpt: Option[Position])
                           (using TypeParamsContext): Option[Type] = {
    val subjectType = typeFormula(subject, currScope, posOpt).withTypeVarsExpanded
    subtypingCtx.checkDowncastTarget(requireNonNullable(subjectType, "cast value", posOpt), tid) match {
      case DowncastTargetCheckResult.CanDowncast(tpe) => Some(tpe)
      case DowncastTargetCheckResult.CannotDowncast(reason) =>
        er.reportError(s"$tid is not a valid downcast target for type $subjectType", posOpt)
        None
    }
  }

  def instantiateType(tpe: Type, ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
                     (using tParamsCtx: TypeParamsContext): Type = {
    tpe match {
      case primitiveType: PrimitiveType => primitiveType
      case namedType: NamedType => instantiateNamedType(namedType, ambientVarianceOpt, currScope, posOpt, subTIfInSuperTPos = None)
      case ClosureType(paramTypesRaw, resultTypeRaw, enforcedPure) =>
        val paramTypesInst = for paramType <- paramTypesRaw yield {
          instantiateType(paramType, ambientVarianceOpt.map(_ * Contravariant), currScope, posOpt)
        }
        val resultTypeInst = instantiateType(resultTypeRaw, ambientVarianceOpt.map(_ * Covariant), currScope, posOpt)
        ClosureType(paramTypesInst, resultTypeInst, enforcedPure)
      case tv: TypeVariable => tv
      case UnionType(types) =>
        UnionType(for tpe <- types yield {
          instantiateType(tpe, ambientVarianceOpt, currScope, posOpt)
        })
      case IntersectionType(types) =>
        IntersectionType(for tpe <- types yield {
          instantiateType(tpe, ambientVarianceOpt, currScope, posOpt)
        })
      case tpe@RefinedType(baseTypeRaw, predicate) =>
        val baseTypeInst = instantiateType(baseTypeRaw, ambientVarianceOpt, currScope, posOpt)
        val tmpPredScope = Scope.nestedInsideNodeOpt(currScope, None)
        tmpPredScope.saveSmartcast(itValue, baseTypeRaw)
        val predicateType = typeFormula(predicate, tmpPredScope, posOpt)
        if (!subtypingCtx.isSubtype(predicateType, BoolType)) {
          er.reportError(s"predicate should have type $BoolType", posOpt)
        }
        if (!predicate.isPure) {
          er.reportError(s"I cannot prove that predicate $predicate is pure", posOpt)
        }
        RefinedType(baseTypeInst, predicate)
      case tpe@IntRangeType(lbOpt, ubOpt) =>
        lbOpt.foreach { lb =>
          val lbType = typeFormula(lb, currScope, posOpt)
          if (!subtypingCtx.isSubtype(lbType, IntType)) {
            er.reportError(s"lower bound of $tpe should be an integer", posOpt)
          }
          if (!lb.isPure) {
            er.reportError(s"I cannot prove that lower bound of $tpe is pure", posOpt)
          }
        }
        ubOpt.foreach { ub =>
          val rbType = typeFormula(ub, currScope, posOpt)
          if (!subtypingCtx.isSubtype(rbType, IntType)) {
            er.reportError(s"upper bound of $tpe should be an integer", posOpt)
          }
          if (!ub.isPure) {
            er.reportError(s"I cannot prove that upper bound of $tpe is pure", posOpt)
          }
        }
        tpe
      case tpe@NullableType(nullatedTypeRaw) =>
        val nullatedTypeInst = instantiateType(nullatedTypeRaw, ambientVarianceOpt, currScope, posOpt)
        nullatedTypeInst match {
          case nullatedType@(NothingType | NullType) =>
            er.warn(s"useless '${Operator.QuestionMark}': $tpe is equivalent to $nullatedType", posOpt)
          case _ => ()
        }
        NullableType(nullatedTypeInst)
    }
  }

  def instantiateNamedType(namedType: NamedType, ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position], subTIfInSuperTPos: Option[TypeIdentifier])
                          (using typeParamsCtx: TypeParamsContext): NamedType = {
    val NamedType(typeName, typeArgs, args) = namedType
    typeParamsCtx.resolve(typeName) match {
      case Some(tpInfo) =>
        subTIfInSuperTPos.foreach { subT =>
          // TODO is there a way of allowing that? Most likely not really, but that could be powerful...
          er.reportError(s"$subT cannot extend its own type parameter", posOpt)
        }
        if (typeArgs.nonEmpty) {
          er.reportError(s"$typeName is a type variable, hence it cannot take type arguments", posOpt)
        }
        if (args.nonEmpty) {
          er.reportError(s"$typeName is a type variable, hence it cannot take arguments", posOpt)
        }
        for {
          tpVariance <- tpInfo.varianceOpt
          ambientVariance <- ambientVarianceOpt
          if !tpVariance.isAssignableTo(ambientVariance)
        } {
          er.reportError(s"variance error: $tpVariance type parameter $typeName in $ambientVariance position", posOpt)
        }
        namedType
      case None => resolutionCtx.resolveTypeSig(typeName) match {
        case Some(sig) =>
          if (subTIfInSuperTPos.isDefined && sig.typeParams.nonEmpty && typeArgs.isEmpty) {
            er.reportError(s"missing type arguments for $typeName", posOpt)
          }
          val (typeArgsSubst, _) = instantiateTypes(sig.typeParams, typeArgs, subtypingCtx, currScope, posOpt, Some(s"application of type $typeName"))
          val argsWithTypes = args.map(arg => Some(arg) -> typeFormula(arg, currScope, posOpt))
          val paramsWithType = sig.params.map { case (paramId, (paramType, paramVal)) =>
            Some(paramVal) -> paramType.substitute(typeArgsSubst, Map.empty)
          }
          val paramsSubst = checkArgumentsList(paramsWithType, argsWithTypes, s"application of ${sig.id}", currScope, posOpt)
          sig.toType(typeArgsSubst, paramsSubst)
        case None =>
          er.reportError(s"type not found: $typeName", posOpt)
          namedType
      }
    }
  }

  def typeField(field: Field, owner: UserInstantiableTypeSig, typeParamsCtx: TypeParamsContext, posOpt: Option[Position]): Field = {
    val sigScope = owner.sigScope
    field match {
      case ReassignableField(id, typeRaw) =>
        val typeInst = instantiateType(typeRaw, Some(Invariant), sigScope, posOpt)(using typeParamsCtx)
        val thisVal = sigScope.getLocalValuesContextUnsafe.getThisValue.get
        ReassignableField(id, typeInst)
      case field: StableField => typeStableField(field, owner, typeParamsCtx, posOpt)
    }
  }

  def typeStableField(field: StableField, owner: UserInstantiableTypeSig, typeParamsCtx: TypeParamsContext, posOpt: Option[Position]): StableField = {
    val sigScope = owner.sigScope
    val StableField(id, typeRaw, value, isPublishedAsMethod) = field
    val typeInst = instantiateType(typeRaw, Some(Covariant), sigScope, posOpt)(using typeParamsCtx)
    sigScope.saveType(value, typeInst)(using typeParamsCtx)
    val thisVal = sigScope.getLocalValuesContextUnsafe.getThisValue.get
    StableField(id, typeInst, value, isPublishedAsMethod)
  }
  
  def typeTypeTypeParam(typeTypeParamInfo: TypeTypeParamInfo, currScope: Scope, posOpt: Option[Position])
                       (using typeParamsCtx: TypeParamsContext): TypeTypeParamInfo = {
    val TypeTypeParamInfo(tid, variance, upperBoundOpt, lowerBoundOpt) = typeTypeParamInfo
    TypeTypeParamInfo(tid, variance,
      upperBoundOpt.map {
        instantiateType(_, None, currScope, posOpt)
      },
      lowerBoundOpt.map {
        instantiateType(_, None, currScope, posOpt)
      })
  }

  def typeFunTypeParam(functionTypeParamInfo: FunctionTypeParamInfo, currScope: Scope, posOpt: Option[Position])
                      (using typeParamsCtx: TypeParamsContext): FunctionTypeParamInfo = {
    val FunctionTypeParamInfo(tid, upperBoundOpt, lowerBoundOpt) = functionTypeParamInfo
    FunctionTypeParamInfo(tid,
      upperBoundOpt.map {
        instantiateType(_, None, currScope, posOpt)
      },
      lowerBoundOpt.map {
        instantiateType(_, None, currScope, posOpt)
      }
    )
  }

  def typeFunSig(functionSignature: FunctionSignature, ownerTypeParamsCtx: TypeParamsContext): FunctionSignature = solver.onNewFrame {
    val FunctionSignature(ownerName, functionName, typeParamsRaw, paramsInclThisRaw, precondOpt, retTypeRaw, sigScope, visibility, purity, isMain, declPosOpt, isAbstract, isSynthetic) = functionSignature

    val (typeParamsInst, fullTypeParamsCtx) = processTypeParamsAccumulating(ownerTypeParamsCtx, typeParamsRaw) {
      typeFunTypeParam(_, functionSignature.sigScope, functionSignature.declPosOpt)
    }
    val paramsInclThisInst = mutable.LinkedHashMap.empty[NamedIdValue, Type]
    var isReceiver = true
    for (paramId, paramTypeRaw) <- paramsInclThisRaw do {
      val paramTypeInst = instantiateType(paramTypeRaw, if isReceiver then None else Some(Contravariant), functionSignature.sigScope, functionSignature.declPosOpt)(using fullTypeParamsCtx)
      if (sigScope.valuesCtx.globalCtx.getNameOfObject(paramId).isEmpty) {
        sigScope.saveType(paramId, paramTypeInst)(using fullTypeParamsCtx)
      }
      paramsInclThisInst.addOne(paramId -> paramTypeInst)
      isReceiver = false
    }
    precondOpt.foreach { precond =>
      val precondType = typeFormula(precond, sigScope, declPosOpt)(using fullTypeParamsCtx)
      if (!subtypingCtx.isSubtype(precondType, BoolType)(using fullTypeParamsCtx)) {
        er.reportError(s"precondition must have type $BoolType", declPosOpt)
      }
      if (!precond.isPure) {
        er.reportError("I cannot prove that precondition is pure", declPosOpt)
      }
      solver.assert(precond)
    }
    val retTypeInst = instantiateType(retTypeRaw, Some(Covariant), functionSignature.sigScope, functionSignature.declPosOpt)(using fullTypeParamsCtx)
    checkingAllTypeVarsResolved {
      FunctionSignature(ownerName, functionName, typeParamsInst, SeqMap.from(paramsInclThisInst), precondOpt,
        retTypeInst, sigScope, visibility, purity, isMain, declPosOpt, isAbstract, isSynthetic)
    }
  }

  def typeTypeAliasSig(typealiasSig: TypeAliasSignature): TypeAliasSignature = {
    val TypeAliasSignature(id, typeParamsRaw, paramsRaw, rhsRaw, sigScope, declPosOpt) = typealiasSig

    checkTypeParamsAreDistinct(typeParamsRaw, declPosOpt)
    val (typeParamsInst, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamsRaw) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    val paramsInst = for ((paramId, (paramTypeRaw, paramVal)) <- paramsRaw) yield {
      val paramTypeInst = instantiateType(paramTypeRaw, None, sigScope, declPosOpt)(using fullTypeParamsCtx)
      sigScope.saveType(paramVal, paramTypeInst)(using fullTypeParamsCtx, dealiasingCtx, simplifier, resolutionCtx, proxyStore)
      (paramId, (paramTypeInst, paramVal))
    }
    val rhsInst = instantiateType(rhsRaw, None, sigScope, declPosOpt)(using fullTypeParamsCtx)
    checkingAllTypeVarsResolved {
      TypeAliasSignature(id, typeParamsInst, paramsInst, rhsInst, sigScope, declPosOpt)
    }
  }

  def typeInterfaceSig(interfaceSig: InterfaceSignature): InterfaceSignature = {
    val InterfaceSignature(id, typeParamsRaw, functionsRaw, directSupertypesRaw, sigScope, declPosOpt) = interfaceSig

    checkTypeParamsAreDistinct(typeParamsRaw, declPosOpt)
    val (typeParamsInst, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamsRaw) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    saveReceiverType(interfaceSig, fullTypeParamsCtx)
    val functionsInst = for (funId, funSig) <- functionsRaw yield {
      funId -> typeFunSig(funSig, fullTypeParamsCtx)
    }
    val directSuperTypesInst = typeSupertypesAsInterfaces(interfaceSig, resolutionCtx, fullTypeParamsCtx)
    checkingAllTypeVarsResolved {
      InterfaceSignature(id, typeParamsInst, functionsInst, directSuperTypesInst, sigScope, declPosOpt)
    }
  }

  def typeClassSig(classSig: ClassSignature): ClassSignature = {
    val ClassSignature(id, typeParamsRaw, fieldsRaw, functionsRaw, directSupertypesRaw, sigScope, declPosOpt) = classSig

    checkTypeParamsAreDistinct(typeParamsRaw, declPosOpt)
    val (typeParamsInst, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamsRaw) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    saveReceiverType(classSig, fullTypeParamsCtx)
    val fieldsInst = typeFieldsUsing(typeField(_, classSig, fullTypeParamsCtx, declPosOpt))(fieldsRaw)
    val functionsInst = for (funId, funSig) <- functionsRaw yield {
      funId -> typeFunSig(funSig, fullTypeParamsCtx)
    }
    val directSuperTypesInst = typeSupertypesAsInterfaces(classSig, resolutionCtx, fullTypeParamsCtx)
    checkingAllTypeVarsResolved {
      ClassSignature(id, typeParamsInst, fieldsInst, functionsInst, directSuperTypesInst, sigScope, declPosOpt)
    }
  }

  def typeObjectSig(objSig: ObjectSignature): ObjectSignature = {
    val ObjectSignature(id, functionsRaw, directSupertypesRaw, sigScope, declPosOpt) = objSig

    val functionsInst = for (funId, funSig) <- functionsRaw yield {
      funId -> typeFunSig(funSig, TypeParamsContext.empty)
    }
    val directSuperTypesInst = typeSupertypes(objSig, "interface", resolutionCtx, TypeParamsContext.empty)
    checkingAllTypeVarsResolved {
      ObjectSignature(id, functionsInst, directSuperTypesInst, sigScope, declPosOpt)
    }
  }

  def typeDatatypeSig(datatypeSig: DatatypeSignature): DatatypeSignature = {
    val DatatypeSignature(id, typeParamsRaw, functionsRaw, directSupertypesRaw, directSubtypes, sigScope, declPosOpt) = datatypeSig

    checkTypeParamsAreDistinct(typeParamsRaw, declPosOpt)
    val (typeParamsInst, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamsRaw) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    saveReceiverType(datatypeSig, fullTypeParamsCtx)
    val functionsInst = for (funId, funSig) <- functionsRaw yield {
      funId -> typeFunSig(funSig, fullTypeParamsCtx)
    }
    val directSupertypesInst = typeSuperTypesAsDatatypesOrInterfaces(datatypeSig, resolutionCtx, fullTypeParamsCtx)
    checkingAllTypeVarsResolved {
      DatatypeSignature(id, typeParamsInst, functionsInst, directSupertypesInst, directSubtypes, sigScope, declPosOpt)
    }
  }

  def typeRecordSig(recordSig: RecordSignature): RecordSignature = {
    val RecordSignature(id, typeParamsRaw, fieldsRaw, functionsRaw, directSupertypesRaw, sigScope, declPosOpt) = recordSig

    checkTypeParamsAreDistinct(typeParamsRaw, declPosOpt)
    val (typeParamsInst, fullTypeParamsCtx) = processTypeParamsAccumulating(TypeParamsContext.empty, typeParamsRaw) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    saveReceiverType(recordSig, fullTypeParamsCtx)
    val fieldsInst = typeFieldsUsing(typeStableField(_, recordSig, fullTypeParamsCtx, declPosOpt))(fieldsRaw)
    val functionsInst = for (funId, funSig) <- functionsRaw yield {
      funId -> typeFunSig(funSig, fullTypeParamsCtx)
    }
    val directSupertypesInst = typeSuperTypesAsDatatypesOrInterfaces(recordSig, resolutionCtx, fullTypeParamsCtx)
    checkingAllTypeVarsResolved {
      RecordSignature(id, typeParamsInst, fieldsInst, functionsInst, directSupertypesInst, sigScope, declPosOpt)
    }
  }

  private def saveReceiverType(sig: TypeSignature, typeParamsCtx: TypeParamsContext): Unit = {
    val thisVal = sig.sigScope.getLocalValuesContextUnsafe.getThisValue.get
    val tpe = sig.toType(Map.empty, Map.empty)
    sig.sigScope.saveType(thisVal, tpe)(using typeParamsCtx)
  }

  private def typeFieldsUsing[F <: Field](indivTypingFunc: F => F)
                                         (fieldsRaw: SeqMap[FunOrVarId, F]) = {
    val fieldsInstB = SeqMap.newBuilder[FunOrVarId, F]
    for ((id, rawField) <- fieldsRaw) {
      val typedField = indivTypingFunc(rawField)
      fieldsInstB.addOne(id -> typedField)
    }
    val fieldsInst = fieldsInstB.result()
    fieldsInst
  }

  private def checkingAllTypeVarsResolved[S <: DeclSignature](sig: S): S = {
    for ((tv, descr) <- sig.typeVarsWithDescr) {
      if (!tv.isResolved) {
        er.reportError(s"type variable $tv in $descr could not be resolved in a way that preserves encapsulation", sig.declPosOpt)
        tv.resolve(NullableType(AnyType))
      }
      tv.lock()
    }
    sig
  }

  private def applyBranchInfo(scope: Scope, branchInfo: BranchingInfo)(using TypeParamsContext): Unit = {
    for ((subject, smartcastData) <- branchInfo.smartcasts) {
      for {
        originalType <- detectTypeForSmartcast(subject, scope)
        smartcastType <- smartcastData.tryToSmartcast(dealiasingCtx.dealiasType(originalType).withTypeVarsExpanded, resolutionCtx.typesReasoningCache, subtypingCtx)
      } {
        if (smartcastType == NothingType) {
          scope.markHasExited()
          scope.insertInstrDuringTraversal(Unreachable())
        } else {
          val oldType = scope.detectCurrentType(subject)
          val newType = meetJoin.computeMeet(oldType, smartcastType)
          scope.saveSmartcast(subject, smartcastType)
        }
      }
    }
    for {
      assumption <- branchInfo.assumptions
      if assumption.isPure
    } {
      assumption match {
        case Equality(lhs, rhs) =>
          scope.eMerge(lhs, rhs)
        case _ => ()
      }
      solver.assert(assumption)
      val smartcasts =
        smartcastsFromAssumption(assumption, scope)
          ++ proxyStore.developNearest(assumption).toList.flatMap(smartcastsFromAssumption(_, scope))
          ++ proxyStore.developDeep(assumption).toList.flatMap(smartcastsFromAssumption(_, scope))
      smartcasts.foreach { (subject, smartcastType) =>
        scope.saveSmartcast(subject, smartcastType)
      }
    }
    if (solver.checkUnsat()) {
      scope.markHasExited()
      scope.insertInstrDuringTraversal(Unreachable())
    }
  }

  private def smartcastsFromAssumption(assumption: Formula, scope: Scope)(using TypeParamsContext): List[(Formula, Type)] = {
    solver.assert(assumption)
    val smartcasts = assumption match {
      case LessOrEq(lhs, rhs) =>
        solver.takeType(lhs, scope.detectCurrentType(lhs))
        solver.takeType(rhs, scope.detectCurrentType(rhs))
        leqToSmartcasts(lhs, rhs)
      case LessThan(lhs, rhs) =>
        solver.takeType(lhs, scope.detectCurrentType(lhs))
        solver.takeType(rhs, scope.detectCurrentType(rhs))
        ltToSmartcasts(lhs, rhs)
      case developedAssumption =>
        extractPredicateIntoSmartcastType(developedAssumption, scope).mapVals(simplifier.simplify)
    }
    val nullVal = scope.valuesCtx.globalCtx.nullVal
    assumption match {
      case LogicalNot(Equality(lhs, rhs)) =>
        if (lhs == nullVal) {
          scope.saveNonNull(rhs)
        } else if (rhs == nullVal) {
          scope.saveNonNull(lhs)
        }
      case _ => ()
    }
    smartcasts
  }

  private def leqToSmartcasts(lhs: Formula, rhs: Formula)(using TypeParamsContext): List[(Formula, Type)] = {
    val directlyInferredSmartcastOpt =
      if (lhs.typeCanMention(rhs)) {
        Some(lhs -> IntRangeType.ofUpperBound(rhs))
      } else if (rhs.typeCanMention(lhs)) {
        Some(rhs -> IntRangeType.ofLowerBound(lhs))
      } else None
    val linear = simplifier.linearize(Plus(lhs, Neg(rhs)))
    var smartcastSubjectOpt = Option.empty[(Formula, Int)]
    val otherTerms = mutable.ListBuffer.empty[(Formula, Int)]
    for (term@(f, idx) <- linear) {
      if (smartcastSubjectOpt.isEmpty && linear.forall((lf, _) => lf == f || f.typeCanMention(lf))) {
        smartcastSubjectOpt = Some(term)
      } else {
        otherTerms.addOne(term)
      }
    }
    val linSmartcastOpt = smartcastSubjectOpt match {
      case Some((smartcastSubject, smartcastSubjectCoef)) if otherTerms.forall((f, coef) => coef % Math.abs(smartcastSubjectCoef) == 0) =>
        val bound = otherTerms.foldLeft[Formula](IntConst(0)) {
          case (acc, (f, coef)) =>
            Plus(acc, Times(IntConst(-coef / smartcastSubjectCoef), f))
        }
        val range = simplifier.simplify(
          if smartcastSubjectCoef < 0
          then IntRangeType.ofLowerBound(bound)
          else IntRangeType.ofUpperBound(bound)
        )
        Some(smartcastSubject -> range)
      case _ => None
    }
    directlyInferredSmartcastOpt.toList ++ linSmartcastOpt
  }

  private def ltToSmartcasts(lhs: Formula, rhs: Formula)(using TypeParamsContext): List[(Formula, Type)] = {
    import compiler.irs.ssa.FormulasDsl.*
    leqToSmartcasts(lhs + 1, rhs)
  }

  private def extractPredicateIntoSmartcastType(condition: Formula, scope: Scope)(using TypeParamsContext): List[(Formula, RefinedType)] = {

    def performSubst(holes: List[Formula]): List[(Formula, RefinedType)] = {
      for {
        itSubstTarget <- findFormulaWhoseTypeCanMentionAllOthers(holes).toList
        baseType <- detectTypeForSmartcast(itSubstTarget, scope)
      } yield {
        val predicate = condition.substitute(itSubstTarget, itValue)
        itSubstTarget -> RefinedType(baseType, predicate)
      }
    }

    condition match {
      case LogicalAnd(lhs, rhs) =>
        extractPredicateIntoSmartcastType(lhs, scope) ++ extractPredicateIntoSmartcastType(rhs, scope)
      // TODO this is useful to prevent divisions by zero, but maybe we can generalize and support equalities as well
      //  Additionally, leqToSmartcasts and ltToSmartcasts can probably be turned into special cases of this (using the simplifier)
      case LogicalNot(Equality(lhs, rhs)) =>
        performSubst(List(lhs, rhs))
      case LogicalNot(operand) =>
        extractPredicateIntoSmartcastType(operand, scope).mapVals {
          case RefinedType(baseType, predicate) => RefinedType(baseType, simplifier.simplifyBool(LogicalNot(predicate)))
        }
      case FunCall(receiver, func, typeArgs, args) =>
        performSubst(receiver :: args)
      case ClosureCall(callee, closureTypingTarget, args) =>
        performSubst(callee :: args)
      case _ => List.empty
    }
  }

  private def findFormulaWhoseTypeCanMentionAllOthers(formulas: Iterable[Formula]): Option[Formula] =
    formulas.findUnique(candidate => formulas.forall(otherFormula => otherFormula == candidate || candidate.typeCanMention(otherFormula)))

  private def forbiddenIfImpure(msg: String, posOpt: Option[Position]): Unit = {
    if (isPurityRequired) {
      er.reportError(msg, posOpt)
    }
  }

  private def resolveFunSigAndCheckArgs(receiver: Formula, invkTarget: InvocationTarget, callTypeArgs: List[Type],
                                        callArgs: List[Formula], scope: Scope, posOpt: Option[Position])
                                       (using tParamsCtx: TypeParamsContext): (Type, List[Type], List[Type]) = {
    val receiverType = typeFormula(receiver, scope, posOpt)

    def errorCase() = {
      er.reportError(s"method ${invkTarget.funId} not found in type $receiverType", posOpt)
      irModif {
        invkTarget.markUnresolvable()
      }
      (NothingType, callTypeArgs, List.empty)
    }

    val typedCallArgs = callArgs.map(arg => Some(arg) -> typeFormula(arg, scope, posOpt))
    dealiasingCtx.dealiasType(receiverType.withTypeVarsExpanded).withTypeVarsExpanded.ignoreNullabilityShallow.asRefinedType.baseType match {
      case NamedType(typeName, receiverTypeArgs, receiverArgs) =>
        resolutionCtx.resolveFunSig(typeName, invkTarget.funId) match {
          case FuncResolResult.Success(ownerSig, funSig) =>
            if (funSig.visibility == Visibility.Private && !receiverIsThisPtr(scope, receiver)) {
              er.reportError(s"illegal access to ${Visibility.Private} method ${funSig.functionName}", posOpt)
            }
            val (receiverTypeSubst, instRecTypeArgs) = instantiateTypes(ownerSig.typeParams, receiverTypeArgs, subtypingCtx, scope, posOpt, None)
            val (callTypeSubst, instFunTypeArgs) = instantiateTypes(funSig.typeParams, callTypeArgs, subtypingCtx, scope, posOpt, Some(s"type $typeName"))
            val composedTypeSubst = receiverTypeSubst ++ callTypeSubst
            val paramTypesInclThis = funSig.paramsInclThis.map { (paramVal, tpe) =>
              Some(paramVal) -> tpe.substitute(composedTypeSubst, Map.empty)
            }
            val argsSubst = checkArgumentsList(paramTypesInclThis, (Some(receiver), receiverType) :: typedCallArgs,
              s"call to ${invkTarget.funId}", scope, posOpt, argsIncludeReceiver = true)
            funSig.precondOpt.foreach { precondRaw =>
              val precondSubst = precondRaw.substitute(argsSubst)
              if (!solver.canProve(precondSubst)) {
                er.reportError(s"illegal call to ${funSig.functionName}: I cannot prove that its precondition $precondSubst holds", posOpt)
              }
              solver.assert(precondSubst)
            }
            val instantiatedRetType =
              simplifier.simplify(funSig.retType.withTypeVarsExpanded.substitute(composedTypeSubst, argsSubst))
                .withDependenciesTransformed(d => proxyStore.developNearest(d).getOrElse(d))
            irModif {
              invkTarget.resolve(ownerSig, funSig, instantiatedRetType)
            }
            if (isPurityRequired && !funSig.isPure) {
              er.reportError(s"illegal call to impure method ${funSig.functionName}", posOpt)
            }
            (instantiatedRetType, instRecTypeArgs, instFunTypeArgs)
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  extension (scope: Scope) private def computeCurrentType(formula: Formula, posOpt: Option[Position])
                                                         (using Simplifier, TypeParamsContext): Type =
    doComputeCurrentType(scope, formula, Some(posOpt), saveSmartcastsInIR = true)

  extension (scope: Scope) private def detectCurrentType(formula: Formula)
                                                        (using Simplifier, TypeParamsContext): Type =
    doComputeCurrentType(scope, formula, None, saveSmartcastsInIR = false)

  private def doComputeCurrentType(scope: Scope, formula: Formula, posOptIfShouldReport: Option[Option[Position]], saveSmartcastsInIR: Boolean)
                                  (using Simplifier, TypeParamsContext): Type = {
    val tpe = scope.getCurrentTypeOf(formula, saveSmartcastsInIR)
    posOptIfShouldReport.foreach { posOpt =>
      (formula, tpe) match {
        case (UninterpretedConstIdValue(name, definingScope, uid), NothingType) =>
          er.reportError(s"object not found: $name", posOpt)
        case _ => ()
      }
    }
    tpe.withTypeVarsExpanded
  }

  private def typeClosureCall(calleeType: Type, closureTypingTarget: ClosureTypingTarget, argsAndTypes: List[(Some[Formula], Type)], currScope: Scope, posOpt: Option[Position])
                             (using TypeParamsContext): Type = {
    requireNonNullable(calleeType.withTypeVarsExpanded, "closure", posOpt) match {
      case calleeType@ClosureType(paramTypes, resultType, enforcedPure) =>
        irModif {
          closureTypingTarget.resolve(calleeType)
        }
        checkArgumentsList(paramTypes.map(None -> _), argsAndTypes, "closure invocation", currScope, posOpt)
        if (!enforcedPure) {
          forbiddenIfImpure("illegal invocation of an impure closure in a pure method or closure", posOpt)
        }
        resultType
      case calleeType =>
        er.reportError(s"$calleeType is not callable", posOpt)
        NothingType
    }
  }

  private def resolveFieldAccess(owner: Formula, ownerType: Type, fieldResolTarget: FieldResolutionTarget, currScope: Scope,
                                 needsWriteAccess: Boolean, posOpt: Option[Position])
                                (using TypeParamsContext): Type = {
    def errorCase() = {
      er.reportError(s"field ${fieldResolTarget.fieldId} not found in type $ownerType", posOpt)
      irModif {
        fieldResolTarget.markUnresolvable()
      }
      NothingType
    }

    val owt = requireNonNullable(ownerType.withTypeVarsExpanded, s"owner of field ${fieldResolTarget.fieldId}", posOpt)
    dealiasingCtx.dealiasType(owt.withTypeVarsExpanded).withTypeVarsExpanded.asRefinedType.baseType match {
      case NamedType(typeName, typeArgs, args) =>
        resolutionCtx.resolveFieldAccess(typeName, fieldResolTarget.fieldId) match {
          case FieldResolResult.Success(ownerSig, field) if receiverIsThisPtr(currScope, owner) =>
            val (typeSubst, _) = instantiateTypes(ownerSig.typeParams, typeArgs, subtypingCtx, currScope, posOpt, None)
            val instantiatedFieldType =
              field.tpe.substitute(typeSubst, Map.empty)
                .withDependenciesTransformed(_.transformParamValsIntoSelectOn(owner)(using ownerSig))
                .withDependenciesTransformed(d => proxyStore.developNearest(d).getOrElse(d))
            irModif {
              fieldResolTarget.resolve(ownerSig, instantiatedFieldType)
            }
            if (needsWriteAccess && field.isStable) {
              er.reportError(s"illegal update of ${Keyword.Val}-field ${field.id}", posOpt)
            }
            if (isPurityRequired && !field.isStable) {
              er.reportError(s"illegal access to impure field ${field.id}", posOpt)
            }
            instantiatedFieldType
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  private def requireNonNullable(possiblyNullable: Type, descr: String, posOpt: Option[Position]) = {
    possiblyNullable match {
      case NullableType(nullatedType) =>
        er.reportError(s"$descr should not be nullable", posOpt)
        nullatedType
      case nonNullable => nonNullable
    }
  }

  private def receiverIsThisPtr(currScope: Scope, receiver: Formula): Boolean = {
    currScope.getLocalValuesContextUnsafe.getThisValue.exists { thisVal =>
      receiver == thisVal || proxyStore.developDeep(receiver).contains(thisVal)
    }
  }

  private def instantiateTypes(typeParams: List[TypeParamInfo], typeArgs: List[Type], subtypingCtx: SubtypingContext, scope: Scope,
                               posOpt: Option[Position], ctxDescrForReportingOpt: Option[String])
                              (using typeParamsCtx: TypeParamsContext): (Map[TypeIdentifier, Type], List[Type]) = {
    val substBuilder = Map.newBuilder[TypeIdentifier, Type]
    val instTypesB = List.newBuilder[Type]
    for ((tParam, tArgRaw) <- typeParams.zip(typeArgs)) {
      val tArgInst = instantiateType(tArgRaw, tParam.varianceOpt, scope, posOpt)
      ctxDescrForReportingOpt.foreach { ctxDescr =>
        checkTypeIsInBounds(tArgInst, tParam.upperBoundOpt, tParam.lowerBoundOpt, posOpt, tParam.tid)
      }
      substBuilder.addOne(tParam.tid -> tArgInst)
      instTypesB.addOne(tArgInst)
    }
    for (tp <- typeParams.drop(typeArgs.size)) {
      substBuilder.addOne(tp.tid -> typeVarsCtx.newTypeVariable(tp.tid, tp.upperBoundOpt, tp.lowerBoundOpt, typeParamsCtx, posOpt))
    }
    if (typeArgs.size > typeParams.size) {
      ctxDescrForReportingOpt.foreach { ctxDescr =>
        if (typeArgs.nonEmpty) {
          er.reportError(s"too many type parameters for $ctxDescr", posOpt)
        }
      }
    }
    (substBuilder.result(), instTypesB.result())
  }

  def checkTypeIsInBounds(tpe: Type, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type], posOpt: Option[Position], typeVarId: Identifier)(using TypeParamsContext): Unit = {
    upperBoundOpt.foreach { upperBound =>
      subtypingCtx.enforceIsSubtype(tpe, upperBound, s"type variable $typeVarId has been resolved to type $tpe, which violates its upper bound $upperBound", posOpt)
    }
    lowerBoundOpt.foreach { lowerBound =>
      subtypingCtx.enforceIsSubtype(lowerBound, tpe, s"type variable $typeVarId has been resolved to type $tpe, which violates its lower bound $lowerBound", posOpt)
    }
  }

  private def checkTypeParamsAreDistinct(typeParams: Iterable[TypeParamInfo], posOpt: Option[Position]): Unit = {
    val prevNames = mutable.Set.empty[TypeIdentifier]
    for (tParam <- typeParams) {
      if (!prevNames.add(tParam.tid)) {
        er.reportError(s"duplicate type parameter: ${tParam.tid}", posOpt)
      }
    }
  }

  private def typeSupertypesAsInterfaces(sig: EncapsulatedTypeSig, resolutionCtx: ResolutionContext, typeParamsCtx: TypeParamsContext): List[NamedType] =
    typeSupertypes[InterfaceSignature](sig, "interface", resolutionCtx, typeParamsCtx)

  private def typeSuperTypesAsDatatypesOrInterfaces(sig: RuntimeTypeSignature, resolutionCtx: ResolutionContext, typeParamsCtx: TypeParamsContext): List[NamedType] =
    typeSupertypes[AbstractTypeSig](sig, "datatype or interface", resolutionCtx, typeParamsCtx)

  private def typeSupertypes[S <: AbstractTypeSig : ClassTag](sig: RuntimeTypeSignature, superTKindDescr: String, resolutionCtx: ResolutionContext, typeParamsCtx: TypeParamsContext): List[NamedType] = {
    for (superTRaw <- sig.directSupertypes) yield {
      val superTInst = instantiateNamedType(superTRaw, Some(Covariant), sig.sigScope, sig.declPosOpt, subTIfInSuperTPos = Some(sig.id))(using typeParamsCtx)
      dealiasingCtx.dealiasType(superTInst) match {
        case superTDealiased: NamedType =>
          if (resolutionCtx.resolveTypeSigAs[S](superTDealiased.typeName).isEmpty) {
            er.reportError(s"$superTKindDescr not found: ${superTDealiased.typeName}", sig.declPosOpt)
          }
        case superTDealiased =>
          er.reportError(s"$superTDealiased cannot be a supertype of ${sig.id}", sig.declPosOpt)
      }
      superTInst
    }
  }

  private def expVariance(ambientVarianceOpt: Option[Variance], tParam: TypeParamInfo): Option[Variance] = (tParam, ambientVarianceOpt) match {
    case (tParam: TypeTypeParamInfo, Some(ambientVariance)) =>
      Some(tParam.variance * ambientVariance)
    case _ => None
  }

  private def checkArgumentsList(params: Iterable[(Option[IdValue], Type)], args: Iterable[(Option[Formula], Type)], ctxDescr: String, currScope: Scope, posOpt: Option[Position], argsIncludeReceiver: Boolean = false)
                                (using TypeParamsContext): mutable.Map[IdValue, Formula] = {
    val nParams = params.size
    val nArgs = args.size
    if (nParams != nArgs) {
      er.reportError(s"$ctxDescr: wrong number of arguments (expected $nParams, was $nArgs)", posOpt)
    }

    // first pass: try to resolve type variables
    val subst = mutable.Map.empty[IdValue, Formula]
    for (((paramValOpt, paramTypeBeforeSubst), (argOpt, argType)) <- params.zip(args)) {
      val paramType = paramTypeBeforeSubst.substitute(Map.empty, subst)
      tryToResolveTypeVars(paramType, argType)
      paramValOpt.foreach { paramVal =>
        addToSubstIfValid(paramVal, argOpt, subst)
      }
    }

    // second pass: actually check types
    subst.clear()
    var argIdx = if argsIncludeReceiver then 0 else 1
    for (((paramValOpt, paramTypeBeforeSubst), (argOpt, argType)) <- params.zip(args)) {
      val paramType = paramTypeBeforeSubst.substitute(Map.empty, subst)
      subtypingCtx.enforceIsSubtypeExpAct(argOpt, argType, paramType, s"${nthArgument(argIdx)} of $ctxDescr", currScope, posOpt)
      paramValOpt.foreach { paramVal =>
        addToSubstIfValid(paramVal, argOpt, subst)
      }
      argIdx += 1
    }
    subst
  }

  private def addToSubstIfValid(paramVal: IdValue, argOpt: Option[Formula], subst: mutable.Map[IdValue, Formula]): Unit = {
    argOpt.foreach { rawArg =>
      val repl = proxyStore.developNearest(rawArg).getOrElse(rawArg)
      subst.put(paramVal, repl)
    }
  }

  private enum TypeVarsResolMode {
    case ParamsOnly, ParamsAndArgs
  }

  private def tryToResolveTypeVars(paramType: Type, argType: Type)(using tvResolMode: TypeVarsResolMode = TypeVarsResolMode.ParamsOnly, typeParamsCtx: TypeParamsContext): Unit = (dealiasingCtx.dealiasType(paramType).withTypeVarsExpanded, dealiasingCtx.dealiasType(argType).withTypeVarsExpanded) match {
    case (paramType@NamedType(paramTypeName, paramTypeArgs, _), argType@NamedType(argTypeName, argTypeArgs, _)) =>
      for {
        paramTSig <- resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](paramTypeName)
        argTSig <- resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](argTypeName)
        argToParamSubst <- subtypingCtx.subToSuperSubst(argTypeName, paramTypeName)
      } do {
        val paramSubst = paramTSig.typeParams.map(_.tid).zip(paramTypeArgs).toMap
        val argsSubst = argTSig.typeParams.map(_.tid).zip(argTypeArgs).toMap
        val upcastArgsSubst = argToParamSubst.map {
          case (tParamName, tArg@NamedType(tArgName, Nil, Nil)) =>
            tParamName -> argsSubst.getOrElse(tParamName, tArg)
          case (tParamName, tArg) => tParamName -> tArg
        }
        for {
          tParam <- paramSubst.keys ++ upcastArgsSubst.keys
          paramInstantiation <- paramSubst.get(tParam)
          argInstantiation <- argsSubst.get(tParam)
        } do {
          tryToResolveTypeVars(paramInstantiation, argInstantiation)
        }
      }
    case (ClosureType(paramParams, paramRes, _), ClosureType(argParams, argRes, _)) =>
      for ((tParam, tArg) <- paramParams.zip(argParams)) {
        tryToResolveTypeVars(tParam, tArg)
      }
      tryToResolveTypeVars(paramRes, argRes)
    case (tv: TypeVariable, argType) if !tv.isResolved =>
      tv.resolve(argType)
    case (tv: TypeVariable, argType) if tv.isResolved && subtypingCtx.isSubtype(tv.substitutedIfResolved, argType) =>
      tv.remapIfNotLocked(argType)
    case (paramType, tv: TypeVariable) if tvResolMode == TypeVarsResolMode.ParamsAndArgs && !tv.isResolved =>
      tv.resolve(paramType)
    case _ => ()
  }

  private def nthArgument(i: Int): String = i match {
    case 0 => "receiver"
    case 1 => "first argument"
    case 2 => "second argument"
    case 3 => "third argument"
    case i => s"${i}th argument"
  }

  private def irModif(action: => Unit): Unit = {
    if (allowWriteToIR) {
      val _ = action
    }
  }

}
