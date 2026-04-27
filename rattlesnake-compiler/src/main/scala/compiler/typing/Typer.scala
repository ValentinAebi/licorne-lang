package compiler.typing

import compiler.identifiers.{Identifier, NormalFunOrVarId, TypeIdentifier}
import compiler.irs.ssa.SSA.*
import compiler.irs.ssa.{FieldResolutionTarget, InvocationTarget, SSA}
import compiler.lang
import compiler.lang.*
import compiler.lang.Field.*
import compiler.irs.ssa.Formulas.*
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.*
import compiler.lang.Variance.*
import compiler.pipeline.CompilationStep
import compiler.recurrences.Recurrence.Monotonicity.*
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.smt.*
import compiler.typing.contexts.*
import compiler.typing.contexts.ResolutionContext.{FieldResolResult, FuncResolResult}
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult
import compiler.util.{SeqSet, whenInstanceOf}
import compiler.valproxies.{BoundMode, BranchingInfo, ProxyStore}
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized

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
                   typeHintsStore: TypeHintsStore,
                   heapVarsTypeStore: HeapVarsTypeStore,
                   solver: Solver,
                   simplifier: Simplifier,
                   absInt: AbstractInterpreter,
                   er: ErrorReporter,
                   closuresCollectorFunc: ClosureInfo => Unit = _ => ()
                 )(using CompilationStep) {
  private val instantiatedClosures = mutable.Map.empty[IdValue, ClosureInfo]

  // @formatter:off
  private given DealiasingContext = dealiasingCtx
  private given ResolutionContext = resolutionCtx
  private given SubtypingContext = subtypingCtx
  private given MeetJoinComputer = meetJoin
  private given ProxyStore = proxyStore
  private given Simplifier = simplifier
  private given Typer = this
  // @formatter:on

  private def isPurityRequired: Boolean = executionEnvirOpt.exists(_.requiresPurityInBody)

  def typeScopeInstructions(scope: Scope, branchInfo: BranchingInfo)(using TypeParamsContext): Unit = {
    solver.onNewFrame {
      scope.resetHasExited()
      scope.forTraversal { instrIter =>
        applyBranchInfo(scope, branchInfo)
        while (instrIter.hasNext) {
          val instr = instrIter.next()
          if (!instr.isInstanceOf[Drop]) {
            scope.reportHasExitedIfNeeded(er, instr.getPosition)
          }
          typeInstr(instr, scope, branchInfo)
        }
      }
    }
    for ((f1, f2) <- scope.persistingEqualities) {
      solver.assertEq(f1, f2, SimplifiedType.from(scope.currentTypeOf(f1, saveSmartcasts = false)))
    }
  }

  def typeInstr(instr: RealInstr, currScope: Scope, branchInfo: BranchingInfo)
               (using typeParamsCtx: TypeParamsContext): Unit = {

    def saveEquality(f1: Formula, f2: Formula, persist: Boolean = false): Unit = {
      if (f1.isPure && f2.isPure) {
        currScope.eMerge(f1, f2, persist)
        solver.assertEq(f1, f2, SimplifiedType.from(currScope.currentTypeOf(f1, saveSmartcasts = false)))
      }
    }

    instr match {

      case loop@Loop(condScope, condVal, bodyScope, loopUpdatedVars) =>
        val (infoIfCondTrueFirstGuess, _) = proxyStore.extractRawBranchingInfos(condVal, branchInfo, currScope)
        for (varData@LoopVarData(varId, beforeLoopVal, inCondVal, bodyLastVal) <- loopUpdatedVars) {
          (for {
            recurrence <- varData.recurrenceOpt
            monotonicity <- Some(recurrence.computeMonotonicity(solver)).filter(_ != NonMonotonous)
          } yield {
            val boundMode = if monotonicity == NonDecreasing then BoundMode.Upper else BoundMode.Lower
            val inferredBound = infoIfCondTrueFirstGuess.boundFor(inCondVal, boundMode, solver)
            val preIterationBoundOpt = proxyStore.getProxy(beforeLoopVal)
            val inBodyType = simplifier.simplify(
              monotonicity match {
                case Constant => preIterationBoundOpt.map(IntRangeType.singleton).getOrElse(IntType)
                case NonDecreasing => IntRangeType(preIterationBoundOpt, inferredBound)
                case NonIncreasing => IntRangeType(inferredBound, preIterationBoundOpt)
                case NonMonotonous => IntType
              }
            )
            val feedbackType =
              absInt.interpretUnderAssumptions(recurrence.induct, Map(recurrence.inductVal -> inBodyType), None).getOrElse {
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
            // TODO maybe detect more precise after-loop-type in the presence of a recurrence
            currScope.saveType(inCondVal, inCondType) // after loop
            condScope.saveSmartcast(inCondVal, inCondType) // inside condition
            bodyScope.saveSmartcast(inCondVal, inBodyType) // inside body
            varData.handledThroughRecurrenceFlag = true
          }) orElse {
            // TODO lookup proxy of bodyLastVal to see if we can infer its type (maybe this can be unified with the "next step" interpretation in the previous case)
            val tpe =
              currScope.getLocalValuesContextUnsafe
                .valueOf(varId)
                .asInstanceOf[KnownAndInitialized]
                .declarationTypeAnnotOpt
                .orElse(typeHintsStore.getHints(inCondVal).find { hint =>
                  subtypingCtx.isSubtype(currScope.currentTypeOf(beforeLoopVal, saveSmartcasts = false), hint)
                })
                .getOrElse(currScope.currentTypeOf(beforeLoopVal, saveSmartcasts = true).ignoreRangesShallow)
            currScope.saveType(inCondVal, tpe)
            Some(())
          }
        }
        typeScopeInstructions(condScope, BranchingInfo.empty)
        subtypingCtx.enforceIsSubtype(condScope.currentTypeOf(condVal, saveSmartcasts = true), BoolType, s"loop condition must have type $BoolType", loop.getPosition)
        val (infoIfCondTrue, infoIfCondFalse) = proxyStore.extractRawBranchingInfos(condVal, branchInfo, currScope)
        typeScopeInstructions(bodyScope, infoIfCondTrue)
        for {
          varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- loopUpdatedVars
          if !varData.handledThroughRecurrenceFlag
        } {
          val typeAtEndOfBody = bodyScope.currentTypeOf(bodyLastVal, saveSmartcasts = false)
          val typeInCond = condScope.currentTypeOf(condVal, saveSmartcasts = false)
          lazy val msg = currScope.getLocalValuesContextUnsafe.valueOf(varId) match {
            case KnownAndInitialized(value, reassigStatus, Some(declTypeAnnot)) =>
              s"update of variable $varId in loop violate its type annotation $declTypeAnnot"
            case _ =>
              s"inferred incorrect type $typeInCond for variable $varId at loop body start, please provide a type annotation at variable declaration site"
          }
          subtypingCtx.enforceIsSubtype(typeAtEndOfBody, typeInCond, msg, loop.getPosition)
        }
        applyBranchInfo(currScope, infoIfCondFalse)

      case disjunction@Disjunction(condVal, thenBr, elseBr, variables) =>
        val condType = currScope.currentTypeOf(condVal, saveSmartcasts = true)
        subtypingCtx.enforceIsSubtype(condType, BoolType, s"condition must have type $BoolType", disjunction.getPosition)
        val (infoIfCondTrue, infoIfCondFalse) = proxyStore.extractRawBranchingInfos(condVal, branchInfo, currScope)
        typeScopeInstructions(thenBr, infoIfCondTrue)
        typeScopeInstructions(elseBr, infoIfCondFalse)
        for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
          val thenType = thenBr.currentTypeOf(afterThenVal, saveSmartcasts = false)
          val elseType = elseBr.currentTypeOf(afterElseVal, saveSmartcasts = false)
          val joinType = {
            if elseBr.hasExited then thenType
            else if thenBr.hasExited then elseType
            else meetJoin.computeJoin(thenType, elseType)
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

      case staticTypeAssert@StaticTypeAssert(value, tpe) =>
        val valueType = currScope.currentTypeOf(value, saveSmartcasts = true)
        subtypingCtx.enforceIsSubtypeExpAct(value, valueType, tpe, "type ascription", staticTypeAssert.getPosition)

      case StaticAssert(value) => ???

      case AssignVal(assigned, src) =>
        val assignedType = tryToApplyHint(src, currScope.currentTypeOf(src, saveSmartcasts = true))
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
        typeNumericBinop(lhs, rhs, currScope, absInt.typeModuloType, Operator.Modulo, rem.getPosition)
      }

      case and@And(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeLogicalBinop(lhs, rhs, currScope, Operator.And, and.getPosition)
      }

      case or@Or(assigned, lhs, rhs) => assignTarget(assigned, currScope) {
        typeLogicalBinop(lhs, rhs, currScope, Operator.Or, or.getPosition)
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

      case invk@InvokeFunc(assigned, receiver, func, typeArgs, args) if func.isNotResolvedYet =>
        val returnType = resolveFunSigAndCheckArgs(receiver, func, typeArgs, args, currScope, invk.getPosition)
        currScope.saveType(assigned, returnType)
        currScope.markHasExitedIfNothing(returnType)

      case fr@FieldRead(assigned, owner, field) if field.isNotResolvedYet =>
        val ownerType = currScope.currentTypeOf(owner, saveSmartcasts = true)
        val tpe = resolveFieldAccess(owner, ownerType, field, currScope, needsWriteAccess = false, fr.getPosition)
        proxyStore.getProxy(assigned).flatMap(currScope.smartcastFor(_, saveSmartcasts = false)) match {
          case Some(smartcastType) =>
            currScope.saveType(assigned, smartcastType)
          case None =>
            currScope.saveType(assigned, tpe)
        }

      case fw@FieldWrite(owner, fieldResolTarget, rhs) if fieldResolTarget.isNotResolvedYet =>
        val ownerType = currScope.currentTypeOf(owner, saveSmartcasts = true)
        val fieldType = resolveFieldAccess(owner, ownerType, fieldResolTarget, currScope, needsWriteAccess = true, fw.getPosition, isInInitializer = currScope.isInitScopeOf(owner))
        val rhsType = currScope.currentTypeOf(rhs, saveSmartcasts = true)
        tryToResolveTypeVars(fieldType, rhsType)
        subtypingCtx.enforceIsSubtypeExpAct(rhs, rhsType, fieldType, s"assignment to field ${fieldResolTarget.fieldId}", fw.getPosition)
        val isInitializationOfStableField = fieldResolTarget.isResolvedAndStable
        if (isInitializationOfStableField) {
          val ow = proxyStore.getProxy(owner).getOrElse(owner)
          val select = Select(ow, fieldResolTarget)
          saveEquality(select, rhs, persist = true)
          fieldResolTarget.getReceiverSigUnsafe match {
            case receiverSig: ClassSignature =>
              val fld = receiverSig.fields.apply(fieldResolTarget.fieldId)
              if (fld.hasPublicSyntheticAccessor) {
                val invkTarget = InvocationTarget(fld.id)
                val funSig = resolutionCtx.resolveFunSig(receiverSig.id, fld.id).asInstanceOf[FuncResolResult.Success].funSig
                invkTarget.resolve(receiverSig, funSig, fld.tpe)
                val accessorCall = Call(ow, invkTarget, List.empty, List.empty)
                saveEquality(select, accessorCall, persist = true)
              }
            case _ => ()
          }
        }

      case _: (InvokeFunc | FieldRead | FieldWrite) =>
        throw AssertionError("typing phase run more than once on the same piece of code")

      case heapVarRd@HeapVarRead(assigned, heapVar) =>
        val tpe = heapVarsTypeStore.getTypeUnsafe(heapVar)
        currScope.saveType(assigned, tpe)
        forbiddenIfImpure(s"illegal access to impure closure-captured variable $heapVar", heapVarRd.getPosition)

      case heapVarWr@HeapVarWrite(heapVar, newValue) =>
        val newValType = currScope.currentTypeOf(newValue, saveSmartcasts = true)
        heapVarsTypeStore.getType(heapVar) match {
          case Some(expType) =>
            subtypingCtx.enforceIsSubtypeExpAct(newValue, newValType, expType, "heap-allocated variable assignment", heapVarWr.getPosition)
          case None =>
            // TODO maybe try to save refined types also here, instead of falling back to the principal type?
            heapVarsTypeStore.saveType(heapVar, newValType.ignoreRangesShallow)
        }
        forbiddenIfImpure(s"illegal access to impure closure-captured variable $heapVar", heapVarWr.getPosition)

      case invkClosure@InvokeClosure(assigned, callee, args) =>
        currScope.currentTypeOf(callee, saveSmartcasts = true) match {
          case ClosureType(paramTypes, resultType) =>
            val argsWithVals = args.map(arg => Some(arg) -> currScope.currentTypeOf(arg, saveSmartcasts = true))
            checkArgumentsList(paramTypes.map(None -> _), argsWithVals, "closure invocation", invkClosure.getPosition)
            currScope.saveType(assigned, resultType)
          case calleeType =>
            er.reportError(s"$calleeType is not callable", invkClosure.getPosition)
        }
        if (isPurityRequired) {
          instantiatedClosures.get(callee) match {
            case Some(closureInfo) =>
              closureInfo.raisePurityFlag()
            case None =>
              er.reportError("purity error: I cannot prove that closure invocation may not result in side-effects", invkClosure.getPosition)
          }
        }

      case mkHeapVar@MkHeapVar(assigned) =>
        // defer typing to first write
        ()

      case instantiate@Instantiate(assigned, classOrRecordName, typeArgs) =>
        resolutionCtx.resolveTypeSigAs[UserInstantiableTypeSig](classOrRecordName) match {
          case Some(typeSig) =>
            val typesSubst = instantiateTypes(typeSig.typeParams, typeArgs, subtypingCtx, instantiate.getPosition, Some(s"instantiation of $classOrRecordName"))
            currScope.saveType(assigned, typeSig.toType(typesSubst))
          case None =>
            er.reportError(s"type $classOrRecordName not found or not instantiable", instantiate.getPosition)
        }

      case mkClosure@MkClosure(assigned, params, body) =>
        val id = NormalFunOrVarId(assigned match {
          case assigned: NamedIdValue => assigned.irDescr
          case assigned: IntermediateIdValue => assigned.toString
        })
        val resultTypeVar = typeVarsCtx.newTypeVariable(id, None, None, body.getPosition)
        val paramTypesB = List.newBuilder[Type]
        for ((paramVal, paramType) <- params) {
          body.saveType(paramVal, paramType)
          paramTypesB.addOne(paramType)
        }
        currScope.saveType(assigned, ClosureType(paramTypesB.result(), resultTypeVar))
        executionEnvirOpt match {
          case Some(executionEnvir) =>
            val closureInfo = ClosureInfo(params, body, resultTypeVar, branchInfo, executionEnvir, typeParamsCtx)
            instantiatedClosures.put(assigned, closureInfo)
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
          proxyStore.getProxy(inValue).foreach { proxy =>
            currScope.saveSmartcast(proxy, assertedType)
          }
        }

      case conv@Conversion(assigned, inValue, targetType) =>
        val inValType = requireNonNullable(currScope.currentTypeOf(inValue, saveSmartcasts = true).ignoreRangesShallow, "converted value", conv.getPosition)
        if (inValType == targetType || TypeConversion.conversionFor(inValType, targetType).isDefined) {
          currScope.saveType(assigned, targetType)
        } else {
          er.reportError(s"impossible conversion: $inValType to $targetType", conv.getPosition)
        }

      case ret@Return(retVal) =>
        executionEnvirOpt match {
          case Some(executionEnvir) =>
            val unitVal = currScope.getLocalValuesContextUnsafe.globalCtx.unitVal
            if (executionEnvir.expectedResultType == UnitType && retVal != unitVal && !proxyStore.getProxy(retVal).contains(unitVal)) {
              er.warn(s"returned value has no effect, since return type is $UnitType", ret.getPosition)
            }
            val retValType = currScope.currentTypeOf(retVal, saveSmartcasts = true)
            subtypingCtx.enforceIsSubtypeExpAct(retVal, retValType, executionEnvir.expectedResultType, "return value", ret.getPosition)
          case None =>
            er.reportError("unexpected return in this position", ret.getPosition)
        }
        currScope.markHasExited()

      case panic@Panic(msg) =>
        val msgType = currScope.currentTypeOf(msg, saveSmartcasts = true)
        subtypingCtx.enforceIsSubtype(msgType, StringType, s"panic message should have type $StringType", panic.getPosition)
        currScope.markHasExited()

      case Drop(droppedValue) => ()

      case scope: Scope =>
        typeScopeInstructions(scope, BranchingInfo.empty)
    }
  }

  private def tryToApplyHint(srcVal: IdValue, regularType: Type): Type = {
    val appliedHints = mutable.ListBuffer.empty[Type]
    val hintsIter = typeHintsStore.getHints(srcVal).iterator
    while (hintsIter.hasNext) {
      val hint = hintsIter.next()
      if (subtypingCtx.canProveHasType(srcVal, hint)) {
        appliedHints.addOne(hint)
      }
    }
    if appliedHints.isEmpty then regularType
    else simplifier.simplify(IntersectionType(SeqSet(regularType +: appliedHints)))
  }

  def typeFormula(formula: Formula, scope: Scope, posOpt: Option[Position])
                 (using typeParamsCtx: TypeParamsContext): Type =
    scope.smartcastFor(formula, saveSmartcasts = true).getOrElse(formula match {
      case value: IdValue => scope.currentTypeOf(value, saveSmartcasts = false)
      case IntConst(value) => IntType
      case BoolConst(value) => BoolType
      case StringConst(value) => StringType
      case sel@Select(owner, field) if field.isResolved =>
        field.getInstantiatedFieldTypeUnsafe
      case sel@Select(owner, field) if field.isNotResolvedYet =>
        val ownerType = typeFormula(owner, scope, posOpt)
        val tpe = resolveFieldAccess(owner, ownerType, field, scope, needsWriteAccess = false, posOpt)
        scope.smartcastFor(sel, saveSmartcasts = false).getOrElse(tpe)
      case Select(owner, field) =>
        assert(field.isUnresolvable)
        NothingType
      case Call(receiver, func, typeArgs, args) if func.isResolved => func.getInstantiatedReturnTypeUnsafe
      case call@Call(receiver, func, typeArgs, args) if func.isNotResolvedYet =>
        resolveFunSigAndCheckArgs(receiver, func, typeArgs, args, scope, posOpt)
      case Call(receiver, func, typeArgs, args) =>
        assert(func.isUnresolvable)
        NothingType
      case Plus(lhs, rhs) =>
        typeNumericBinop(lhs, rhs, scope, absInt.typePlusType, Operator.Plus, posOpt)
      case Neg(operand) =>
        typeNumericNeg(operand, scope, posOpt)
      case Times(lhs, rhs) =>
        typeNumericBinop(lhs, rhs, scope, absInt.typeTimesType, Operator.Times, posOpt)
      case DivBy(lhs, rhs) =>
        typeNumericBinop(lhs, rhs, scope, absInt.typeDivType, Operator.Div, posOpt)
      case Modulo(lhs, rhs) =>
        typeNumericBinop(lhs, rhs, scope, absInt.typeModuloType, Operator.Modulo, posOpt)
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
    })

  private def detectNominalTypeForSmartcast(formula: Formula, scope: Scope)(using TypeParamsContext): Option[NamedType] = {

    def namedOrNone(tpe: Type): Option[NamedType] = tpe match {
      case namedType: NamedType => Some(namedType)
      case _ => None
    }

    formula match {
      case value: IdValue =>
        namedOrNone(scope.currentTypeOf(value, saveSmartcasts = false))
      case Select(owner, field) =>
        if (field.isNotResolvedYet) {
          detectNominalTypeForSmartcast(owner, scope) match {
            case Some(ownerType) =>
              val selectType = resolveFieldAccess(owner, ownerType, field, scope, needsWriteAccess = false, None)
              namedOrNone(selectType)
            case None => None
          }
        } else if (field.isResolved) {
          field.getInstantiatedFieldTypeUnsafe match {
            case instType: NamedType => Some(instType)
            case _ => None
          }
        } else None
      case Call(receiver, func, typeArgs, args) =>
        if (func.isNotResolvedYet) {
          detectNominalTypeForSmartcast(receiver, scope) match {
            case Some(receiverType) =>
              val retType = resolveFunSigAndCheckArgs(receiver, func, typeArgs, args, scope, None)
              namedOrNone(retType)
            case None => None
          }
        } else if (func.isResolved) {
          func.getInstantiatedReturnTypeUnsafe match {
            case instType: NamedType => Some(instType)
            case _ => None
          }
        } else None
      case _ => None
    }
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
    val lhsType = dealiasingCtx.dealiasType(typeFormula(lhs, currScope, posOpt))
    val rhsType = dealiasingCtx.dealiasType(typeFormula(rhs, currScope, posOpt))
    // TODO if set types get implemented, this should be updated to make use of them (op / : (Int, Int\{0}) -> Int)
    val isDivOperator = op == Operator.Div || op == Operator.Modulo
    val mayBeDivByZero = isDivOperator && !(
      rhsType.whenInstanceOf[IntRangeType](solver.canProveIsOutsideRange(IntConst(0), _)).getOrElse(false)
        || solver.canProveNotZero(rhs))
    if (mayBeDivByZero) {
      val rhsDescr =
        proxyStore.getProxyIfIdValue(rhs).orElse(Some(rhs)) match {
          case Some(f) => s" $f"
          case None => ""
        }
      er.reportError(s"I cannot prove that right-hand side$rhsDescr of operator '$op' cannot be zero", posOpt)
    }
    absIntFunc(lhsType.withTypeVarsExpanded, rhsType.withTypeVarsExpanded) match {
      case Some(tpe) => tpe
      case None =>
        er.reportError(s"no operator $op found for types $lhsType and $rhsType", posOpt)
        NothingType
    }
  }

  private def typeLogicalBinop(lhs: Formula, rhs: Formula, currScope: Scope, op: Operator, posOpt: Option[Position])
                              (using TypeParamsContext): Type = {
    val lhsType = dealiasingCtx.dealiasType(typeFormula(lhs, currScope, posOpt))
    subtypingCtx.enforceIsSubtypeExpAct(lhsType, BoolType, s"operand of $op", posOpt)
    val rhsType = dealiasingCtx.dealiasType(typeFormula(rhs, currScope, posOpt))
    subtypingCtx.enforceIsSubtypeExpAct(rhsType, BoolType, s"operand of $op", posOpt)
    BoolType
  }

  private def typeComparisonBinop(lhs: Formula, rhs: Formula, currScope: Scope, op: Operator, posOpt: Option[Position])
                                 (using TypeParamsContext): Type = {
    // TODO warning if result is known (true or false)?
    val lhsType = dealiasingCtx.dealiasType(typeFormula(lhs, currScope, posOpt))
    val expectedOperandType = lhsType.ignoreRangesShallow match {
      case tpe@(IntType | DoubleType) => tpe
      case _ => UnionType(IntType, DoubleType)
    }
    subtypingCtx.enforceIsSubtypeExpAct(lhsType, expectedOperandType, s"operand of $op", posOpt)
    val rhsType = dealiasingCtx.dealiasType(typeFormula(rhs, currScope, posOpt))
    subtypingCtx.enforceIsSubtypeExpAct(rhsType, expectedOperandType, s"operand of $op", posOpt)
    BoolType
  }

  private def typeNumericNeg(operand: Formula, currScope: Scope, posOpt: Option[Position])
                            (using TypeParamsContext): Type = {
    val operandType = dealiasingCtx.dealiasType(typeFormula(operand, currScope, posOpt))
    val negatedType = absInt.unaryNegType(operandType.withTypeVarsExpanded) match {
      case Some(negType) => negType
      case None =>
        er.reportError(s"no unary operator ${Operator.Modulo} found for operand type $operandType", posOpt)
        NothingType
    }
    negatedType
  }

  private def typeLogicalNeg(operand: Formula, currScope: Scope, posOpt: Option[Position])
                            (using TypeParamsContext): Type = {
    val operandType = dealiasingCtx.dealiasType(typeFormula(operand, currScope, posOpt))
    subtypingCtx.enforceIsSubtypeExpAct(operandType, BoolType, "negation operand", posOpt)
    BoolType
  }

  private def checkDowncast(subject: Formula, tid: TypeIdentifier, currScope: Scope, posOpt: Option[Position])
                           (using TypeParamsContext): Option[Type] = {
    val subjectType = typeFormula(subject, currScope, posOpt)
    subtypingCtx.checkDowncastTarget(requireNonNullable(subjectType, "cast value", posOpt), tid) match {
      case DowncastTargetCheckResult.CanDowncast(tpe) => Some(tpe)
      case DowncastTargetCheckResult.CannotDowncast(reason) =>
        er.reportError(s"$tid is not a valid downcast target for type $subjectType", posOpt)
        None
    }
  }

  def typeTypeApp(tpe: Type, ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
                 (using tParamsCtx: TypeParamsContext): Unit = {
    tpe match {
      case primitiveType: PrimitiveType => ()
      case namedType: NamedType => typeNamedTypeApp(namedType, ambientVarianceOpt, currScope, posOpt, subTIfInSuperTPos = None)
      case ClosureType(paramTypes, resultType) =>
        for paramType <- paramTypes do {
          typeTypeApp(paramType, ambientVarianceOpt.map(_ * Contravariant), currScope, posOpt)
        }
        typeTypeApp(resultType, ambientVarianceOpt.map(_ * Covariant), currScope, posOpt)
      case tv: TypeVariable => ()
      case UnionType(types) =>
        for tpe <- types do {
          typeTypeApp(tpe, ambientVarianceOpt, currScope, posOpt)
        }
      case IntersectionType(types) =>
        for tpe <- types do {
          typeTypeApp(tpe, ambientVarianceOpt, currScope, posOpt)
        }
      case tpe@IntRangeType(lbOpt, ubOpt) =>
        lbOpt.foreach { lb =>
          typeFormula(lb, currScope, posOpt)
          if (!lb.isPure) {
            er.reportError(s"I cannot prove that lower bound of $tpe is pure", posOpt)
          }
        }
        ubOpt.foreach { ub =>
          typeFormula(ub, currScope, posOpt)
          if (!ub.isPure) {
            er.reportError(s"I cannot prove that upper bound of $tpe is pure", posOpt)
          }
        }
      case tpe@NullableType(nullatedType) =>
        nullatedType match {
          case nullatedType@(NothingType | NullType) =>
            er.warn(s"useless '${Operator.QuestionMark}': $tpe is equivalent to $nullatedType", posOpt)
          case _ => ()
        }
        typeTypeApp(nullatedType, ambientVarianceOpt, currScope, posOpt)
    }
  }

  def typeNamedTypeApp(namedType: NamedType, ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position], subTIfInSuperTPos: Option[TypeIdentifier])
                      (using typeParamsCtx: TypeParamsContext): Unit = {
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
      case None => resolutionCtx.resolveTypeSig(typeName) match {
        case Some(sig) =>
          if (subTIfInSuperTPos.isDefined && sig.typeParams.nonEmpty && typeArgs.isEmpty) {
            er.reportError(s"missing type arguments for $typeName", posOpt)
          }
          typeTypeArgsList(sig.typeParams, typeArgs, ambientVarianceOpt, currScope, posOpt)
          val typeArgsSubst = instantiateTypes(sig.typeParams, typeArgs, subtypingCtx, posOpt, Some(s"application of type $typeName"))
          val argsWithTypes = args.map(arg => Some(arg) -> typeFormula(arg, currScope, posOpt))
          val paramsWithType = sig.params.map { case (paramId, (paramType, paramVal)) =>
            Some(paramVal) -> paramType.substitute(typeArgsSubst, Map.empty)
          }
          checkArgumentsList(paramsWithType, argsWithTypes, s"application of ${sig.id}", posOpt)
        case None =>
          er.reportError(s"type not found: $typeName", posOpt)
      }
    }
  }

  def typeField(field: Field, currScope: Scope, typeParamsCtx: TypeParamsContext, posOpt: Option[Position]): Unit = field match {
    case ReassignableField(id, tpe) => typeTypeApp(tpe, Some(Invariant), currScope, posOpt)(using typeParamsCtx)
    case field: StableField => typeStableField(field, currScope, posOpt)(using typeParamsCtx)
  }

  def typeStableField(field: StableField, currScope: Scope, posOpt: Option[Position])
                     (using typeParamsCtx: TypeParamsContext): Unit = {
    val StableField(id, tpe, value, isPublishedAsMethod) = field
    typeTypeApp(tpe, Some(Covariant), currScope, posOpt)
  }

  // TODO merge with typeFunTypeParam?
  def typeTypeTypeParam(typeTypeParamInfo: TypeTypeParamInfo, currScope: Scope, posOpt: Option[Position])
                       (using typeParamsCtx: TypeParamsContext): Unit = {
    val TypeTypeParamInfo(tid, variance, upperBoundOpt, lowerBoundOpt) = typeTypeParamInfo
    upperBoundOpt.foreach {
      typeTypeApp(_, None, currScope, posOpt)
    }
    lowerBoundOpt.foreach {
      typeTypeApp(_, None, currScope, posOpt)
    }
  }

  def typeFunTypeParam(functionTypeParamInfo: FunctionTypeParamInfo, currScope: Scope, posOpt: Option[Position])
                      (using typeParamsCtx: TypeParamsContext): Unit = {
    val FunctionTypeParamInfo(tid, upperBoundOpt, lowerBoundOpt) = functionTypeParamInfo
    upperBoundOpt.foreach {
      typeTypeApp(_, None, currScope, posOpt)
    }
    lowerBoundOpt.foreach {
      typeTypeApp(_, None, currScope, posOpt)
    }
  }

  def typeFunSig(functionSignature: FunctionSignature, ownerTypeParamsCtx: TypeParamsContext): Unit = {
    val FunctionSignature(ownerName, functionName, typeParams, paramsInclThis, precondOpt, retType, sigScope, visibility, purity, isMain, declPosOpt, isSynthetic) = functionSignature

    val fullTypeParamsCtx = processTypeParamsAccumulating(ownerTypeParamsCtx, typeParams) {
      typeFunTypeParam(_, functionSignature.sigScope, functionSignature.declPosOpt)
    }
    var isReceiver = true
    for (paramId, paramType) <- paramsInclThis do {
      typeTypeApp(paramType, if isReceiver then None else Some(Contravariant), functionSignature.sigScope, functionSignature.declPosOpt)(using fullTypeParamsCtx)
      if (sigScope.valuesCtx.globalCtx.getNameOfObject(paramId).isEmpty) {
        sigScope.saveType(paramId, paramType)(using fullTypeParamsCtx)
      }
      isReceiver = false
    }
    typeTypeApp(retType, Some(Covariant), functionSignature.sigScope, functionSignature.declPosOpt)(using fullTypeParamsCtx)
    precondOpt.foreach { precond =>
      val precondType = typeFormula(precond, sigScope, declPosOpt)(using fullTypeParamsCtx)
      if (!subtypingCtx.isSubtype(precondType, BoolType)) {
        er.reportError(s"precondition must have type $BoolType", declPosOpt)
      }
      if (!precond.isPure) {
        er.reportError("I cannot prove that precondition is pure", declPosOpt)
      }
    }
  }

  def typeInterfaceSig(interfaceSig: InterfaceSignature): Unit = {
    val InterfaceSignature(id, typeParams, functions, directSupertypes, sigScope, declPosOpt) = interfaceSig

    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    val fullTypeParamsCtx = processTypeParamsAccumulating(TypeParamsContext.empty, typeParams) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    for (_, funSig) <- functions do {
      typeFunSig(funSig, fullTypeParamsCtx)
    }
    typeSupertypesAsInterfaces(interfaceSig, resolutionCtx, fullTypeParamsCtx)
  }

  def typeClassSig(classSig: ClassSignature): Unit = {
    val ClassSignature(id, typeParams, fields, functions, directSupertypes, sigScope, declPosOpt) = classSig

    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    val fullTypeParamsCtx = processTypeParamsAccumulating(TypeParamsContext.empty, typeParams) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    for (_, fld) <- fields do {
      typeField(fld, sigScope, fullTypeParamsCtx, declPosOpt)
    }
    for (_, funSig) <- functions do {
      typeFunSig(funSig, fullTypeParamsCtx)
    }
    typeSupertypesAsInterfaces(classSig, resolutionCtx, fullTypeParamsCtx)
  }

  def typeObjectSig(objSig: ObjectSignature): Unit = {
    val ObjectSignature(id, functions, directSupertypes, sigScope, declPosOpt) = objSig

    for (_, funSig) <- functions do {
      typeFunSig(funSig, TypeParamsContext.empty)
    }
    typeSupertypes(objSig, "interface", resolutionCtx, TypeParamsContext.empty)
  }

  def typeDatatypeSig(datatypeSig: DatatypeSignature): Unit = {
    val DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, sigScope, declPosOpt) = datatypeSig

    val fullTypeParamsCtx = processTypeParamsAccumulating(TypeParamsContext.empty, typeParams) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    typeSupertypesAsDatatypes(datatypeSig, resolutionCtx, fullTypeParamsCtx)
  }

  def typeRecordSig(recordSig: RecordSignature): Unit = {
    val RecordSignature(id, typeParams, fields, directSupertypes, sigScope, declPosOpt) = recordSig

    val fullTypeParamsCtx = processTypeParamsAccumulating(TypeParamsContext.empty, typeParams) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for (_, fld) <- fields do {
      typeStableField(fld, sigScope, declPosOpt)(using fullTypeParamsCtx)
    }
    typeSupertypesAsDatatypes(recordSig, resolutionCtx, fullTypeParamsCtx)
  }

  private def applyBranchInfo(scope: Scope, branchInfo: BranchingInfo)(using TypeParamsContext): Unit = {
    for ((subject, smartcastData) <- branchInfo.smartcasts) {
      for {
        originalType <- detectNominalTypeForSmartcast(subject, scope)
        smartcastType <- smartcastData.tryToSmartcast(originalType, resolutionCtx.typesReasoningCache, subtypingCtx)
      } {
        if (smartcastType == NothingType) {
          scope.markHasExited()
          scope.insertInstrDuringTraversal(Unreachable())
        } else {
          val oldType = scope.currentTypeOf(subject, saveSmartcasts = false)
          val newType = meetJoin.computeMeet(oldType, smartcastType)
          scope.saveSmartcast(subject, smartcastType)
        }
      }
    }
    for (assumption <- branchInfo.assumptions) {
      assumption match {
        case Equality(lhs, rhs) =>
          scope.eMerge(lhs, rhs)
        case _ => ()
      }
      solver.assert(assumption)
      val developedAssumption = proxyStore.develop(assumption)
      if (developedAssumption.isPure) {
        solver.assert(developedAssumption)
      }
      val smartcasts = developedAssumption match {
        case LessOrEq(lhs, rhs) =>
          leqToSmartcasts(lhs, rhs)
        case LessThan(lhs, rhs) =>
          ltToSmartcasts(lhs, rhs)
        case _ => List.empty
      }
      smartcasts.foreach { (subject, smartcastType) =>
        scope.saveSmartcast(subject, smartcastType)
      }
      val nullVal = scope.valuesCtx.globalCtx.nullVal
      developedAssumption match {
        case LogicalNot(Equality(lhs, rhs)) =>
          if (lhs == nullVal) {
            scope.saveNonNull(rhs)
          } else if (rhs == nullVal) {
            scope.saveNonNull(lhs)
          }
        case _ => ()
      }
    }
    if (solver.checkUnsat()) {
      scope.markHasExited()
      scope.insertInstrDuringTraversal(Unreachable())
    }
  }

  private def leqToSmartcasts(lhs: Formula, rhs: Formula): List[(Formula, Type)] = {
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

  private def ltToSmartcasts(lhs: Formula, rhs: Formula): List[(Formula, Type)] = {
    import compiler.irs.ssa.FormulasDsl.*
    leqToSmartcasts(lhs + 1, rhs)
  }

  private def forbiddenIfImpure(msg: String, posOpt: Option[Position]): Unit = {
    if (isPurityRequired) {
      er.reportError(msg, posOpt)
    }
  }

  private def resolveFunSigAndCheckArgs(receiver: Formula, invkTarget: InvocationTarget, callTypeArgs: List[Type],
                                        callArgs: List[Formula], scope: Scope, posOpt: Option[Position])
                                       (using tParamsCtx: TypeParamsContext): Type = {
    val receiverType = typeFormula(receiver, scope, posOpt)

    def errorCase() = {
      er.reportError(s"method ${invkTarget.funId} not found in type $receiverType", posOpt)
      invkTarget.markUnresolvable()
      NothingType
    }

    val typedCallArgs = callArgs.map(arg => Some(arg) -> typeFormula(arg, scope, posOpt))
    receiverType.withTypeVarsExpanded.ignoreNullabilityShallow match {
      case NamedType(typeName, receiverTypeArgs, receiverArgs) =>
        resolutionCtx.resolveFunSig(typeName, invkTarget.funId) match {
          case FuncResolResult.Success(ownerSig, funSig) =>
            if (funSig.visibility == Visibility.Private && !receiverIsThisPtr(scope, receiver)) {
              er.reportError(s"illegal access to ${Visibility.Private} method ${funSig.functionName}", posOpt)
            }
            val receiverTypeSubst = instantiateTypes(ownerSig.typeParams, receiverTypeArgs, subtypingCtx, posOpt, None)
            val callTypeSubst = instantiateTypes(funSig.typeParams, callTypeArgs, subtypingCtx, posOpt, Some(s"type $typeName"))
            val composedTypeSubst = receiverTypeSubst ++ callTypeSubst
            val paramTypesInclThis = funSig.paramsInclThis.map { (paramVal, tpe) =>
              Some(paramVal) -> tpe.substitute(composedTypeSubst, Map.empty)
            }
            val argsSubst = checkArgumentsList(paramTypesInclThis, (Some(receiver), receiverType) :: typedCallArgs,
              s"call to ${invkTarget.funId}", posOpt, argsIncludeReceiver = true)
            addToSubstIfValid(funSig.receiverVal, Some(receiver), argsSubst)
            funSig.precondOpt.foreach { precondRaw =>
              val precondSubst = precondRaw.substitute(argsSubst)
              if (!solver.canProve(precondSubst)) {
                er.reportError(s"illegal call to ${funSig.functionName}: I cannot prove that its precondition $precondSubst holds", posOpt)
              }
            }
            val instantiatedRetType = funSig.retType.substitute(composedTypeSubst, argsSubst)
            invkTarget.resolve(ownerSig, funSig, instantiatedRetType)
            if (isPurityRequired && !funSig.isPure) {
              er.reportError(s"illegal call to impure method ${funSig.functionName}", posOpt)
            }
            instantiatedRetType
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  private def resolveFieldAccess(owner: Formula, ownerType: Type, fieldResolTarget: FieldResolutionTarget, currScope: Scope,
                                 needsWriteAccess: Boolean, posOpt: Option[Position], isInInitializer: Boolean = false): Type = {

    def isInitScopeOfOwner: Boolean = owner match {
      case owner: IdValue => currScope.isInitScopeOf(owner)
      case _ => false
    }

    def errorCase() = {
      er.reportError(s"field ${fieldResolTarget.fieldId} not found in type $ownerType", posOpt)
      fieldResolTarget.markUnresolvable()
      NothingType
    }

    requireNonNullable(ownerType, s"owner of field ${fieldResolTarget.fieldId}", posOpt) match {
      case NamedType(typeName, typeArgs, args) =>
        resolutionCtx.resolveFieldAccess(typeName, fieldResolTarget.fieldId) match {
          case FieldResolResult.Success(ownerSig, field) =>
            if (!isInInitializer && ownerSig.isInstanceOf[EncapsulatedTypeSig] && !receiverIsThisPtr(currScope, owner)) {
              er.reportError(s"illegal access to encapsulated field ${field.id}", posOpt)
            }
            // TODO check that we can indeed ignore errors here (reportErrors = false)
            val typeSubst = instantiateTypes(ownerSig.typeParams, typeArgs, subtypingCtx, posOpt, None)
            val instantiatedFieldType = field.tpe.substitute(typeSubst, Map.empty)
            fieldResolTarget.resolve(ownerSig, instantiatedFieldType)
            if (needsWriteAccess && field.isStable && !isInitScopeOfOwner) {
              er.reportError(s"illegal update of ${Keyword.Val}-field ${field.id}", posOpt)
            }
            if (isPurityRequired && !field.isStable && !isInitScopeOfOwner) {
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
      receiver == thisVal || proxyStore.getProxyIfIdValue(receiver).contains(thisVal)
    }
  }

  private def instantiateTypes(typeParams: List[TypeParamInfo], typeArgs: List[Type], subtypingCtx: SubtypingContext, posOpt: Option[Position], ctxDescrForReportingOpt: Option[String]): Map[TypeIdentifier, Type] = {
    if (typeParams.size == typeArgs.size) {
      val substBuilder = Map.newBuilder[TypeIdentifier, Type]
      for ((tParam, tArg) <- typeParams.zip(typeArgs)) {
        ctxDescrForReportingOpt.foreach { ctxDescr =>
          checkTypeIsInBounds(tArg, tParam.upperBoundOpt, tParam.lowerBoundOpt, posOpt, tParam.tid)
        }
        substBuilder.addOne(tParam.tid -> tArg)
      }
      substBuilder.result()
    } else {
      ctxDescrForReportingOpt.foreach { ctxDescr =>
        if (typeArgs.nonEmpty) {
          er.reportError(s"wrong number of type parameters for $ctxDescr", posOpt)
        }
      }
      Map.from(for tp <- typeParams yield {
        tp.tid -> typeVarsCtx.newTypeVariable(tp.tid, tp.upperBoundOpt, tp.lowerBoundOpt, posOpt)
      })
    }
  }

  def checkTypeIsInBounds(tpe: Type, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type], posOpt: Option[Position], typeVarId: Identifier): Unit = {
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

  private def typeSupertypesAsInterfaces(sig: EncapsulatedTypeSig, resolutionCtx: ResolutionContext, typeParamsCtx: TypeParamsContext): Unit =
    typeSupertypes[InterfaceSignature](sig, "interface", resolutionCtx, typeParamsCtx)

  private def typeSupertypesAsDatatypes(sig: UnencapsulatedTypeSig, resolutionCtx: ResolutionContext, typeParamsCtx: TypeParamsContext): Unit =
    typeSupertypes[DatatypeSignature](sig, "datatype", resolutionCtx, typeParamsCtx)

  private def typeSupertypes[S <: AbstractTypeSig : ClassTag](sig: RuntimeTypeSignature, superTKindDescr: String, resolutionCtx: ResolutionContext, typeParamsCtx: TypeParamsContext): Unit = {
    for (superTBeforeDealiasing <- sig.directSupertypes) {
      typeNamedTypeApp(superTBeforeDealiasing, Some(Covariant), sig.sigScope, sig.declPosOpt, subTIfInSuperTPos = Some(sig.id))(using typeParamsCtx)
      dealiasingCtx.dealiasType(superTBeforeDealiasing) match {
        case superTDealiased: NamedType =>
          if (resolutionCtx.resolveTypeSigAs[S](superTDealiased.typeName).isEmpty) {
            er.reportError(s"$superTKindDescr not found: ${superTDealiased.typeName}", sig.declPosOpt)
          }
        case superTDealiased =>
          er.reportError(s"$superTDealiased cannot be a supertype of ${sig.id}", sig.declPosOpt)
      }
    }
  }

  private def processTypeParamsAccumulating[T <: TypeParamInfo](initialTypeParamsCtx: TypeParamsContext, typeParams: Iterable[T])
                                                               (action: T => TypeParamsContext ?=> Unit): TypeParamsContext = {
    var typeParamsCtx = initialTypeParamsCtx
    for (tParam <- typeParams) {
      action(tParam)(using typeParamsCtx)
      typeParamsCtx = typeParamsCtx.extendedWith(tParam)
    }
    typeParamsCtx
  }

  private def typeTypeArgsList(tParams: List[TypeParamInfo], tArgs: List[Type], ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
                              (using TypeParamsContext): Unit = {
    tParams.zip(tArgs).foreach { (tParam, tArg) =>
      val expVar = expVariance(ambientVarianceOpt, tParam)
      typeTypeApp(tArg, expVar, currScope, posOpt)
    }
  }

  private def expVariance(ambientVarianceOpt: Option[Variance], tParam: TypeParamInfo): Option[Variance] = (tParam, ambientVarianceOpt) match {
    case (tParam: TypeTypeParamInfo, Some(ambientVariance)) =>
      Some(tParam.variance * ambientVariance)
    case _ => None
  }

  private def checkArgumentsList(params: Iterable[(Option[IdValue], Type)], args: Iterable[(Option[Formula], Type)], ctxDescr: String, posOpt: Option[Position], argsIncludeReceiver: Boolean = false): mutable.Map[IdValue, Formula] = {
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
      subtypingCtx.enforceIsSubtypeExpAct(argOpt, argType, paramType, s"${nthArgument(argIdx)} of $ctxDescr", posOpt)
      paramValOpt.foreach { paramVal =>
        addToSubstIfValid(paramVal, argOpt, subst)
      }
      argIdx += 1
    }
    subst
  }

  private def addToSubstIfValid(paramVal: IdValue, argOpt: Option[Formula], subst: mutable.Map[IdValue, Formula]): Unit = {
    argOpt.foreach { rawArg =>
      proxyStore.getProxyIfIdValue(rawArg)
        .orElse(Some(rawArg).filter(_.idValsDependencies.forall(_.isInstanceOf[NamedIdValue])))
        .filter(_.isPure)
        .foreach { repl =>
          subst.put(paramVal, repl)
        }
    }
  }

  private def tryToResolveTypeVars(paramType: Type, argType: Type): Unit = (paramType, argType) match {
    case (NamedType(_, paramTypeArgs, _), NamedType(_, argsTypeArgs, _)) =>
      // FIXME account for variance?
      for ((tParam, tArg) <- paramTypeArgs.zip(argsTypeArgs)) {
        tryToResolveTypeVars(tParam, tArg)
      }
    case (ClosureType(paramParams, paramRes), ClosureType(argParams, argRes)) =>
      for ((tParam, tArg) <- paramParams.zip(argParams)) {
        tryToResolveTypeVars(tParam, tArg)
      }
      tryToResolveTypeVars(paramRes, argRes)
    case (tv: TypeVariable, argType) if !tv.isResolved =>
      tv.resolve(argType)
    case (tv: TypeVariable, argType) if tv.isResolved && subtypingCtx.isSubtype(tv.substitutedIfResolved, argType) =>
      tv.remapIfNotLocked(argType)
    case _ => ()
  }

  private def nthArgument(i: Int): String = i match {
    case 0 => "receiver"
    case 1 => "first argument"
    case 2 => "second argument"
    case 3 => "third argument"
    case i => s"${i}th argument"
  }

}
