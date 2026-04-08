package compiler.typing

import compiler.identifiers.{Identifier, NormalFunOrVarId, TypeIdentifier}
import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.lang
import compiler.lang.*
import compiler.lang.Field.*
import compiler.lang.Formulas.*
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.*
import compiler.lang.Variance.*
import compiler.pipeline.CompilationStep
import compiler.recurrences.Recurrence.Monotonicity.*
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.smt.{AbstractInterpreter, Simplifier, Solver}
import compiler.typing.contexts.*
import compiler.typing.contexts.ResolutionContext.{FieldResolResult, FuncResolResult}
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult
import compiler.util.{SeqSet, zipCommons}
import compiler.valproxies.{BoundMode, BranchingInfo, ProxyStore}
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized

import scala.collection.mutable
import scala.reflect.ClassTag


final class Typer(
                   funRetTypeOpt: Option[Type],
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

  // @formatter:off
  private given ResolutionContext = resolutionCtx
  private given SubtypingContext = subtypingCtx
  private given MeetJoinComputer = meetJoin
  private given ProxyStore = proxyStore
  private given Simplifier = simplifier
  private given Typer = this
  // @formatter:on

  def typeScopeInstructions(scope: Scope, branchInfo: BranchingInfo)(using TypeParamsContext): Unit = {
    solver.onNewFrame {
      scope.resetHasExited()
      applyBranchInfo(scope, branchInfo, 0)
      if (solver.checkUnsat()) {
        scope.markHasExited()
      }
      for ((instr, idxInScope) <- scope.instructions.zipWithIndex) {
        if (!instr.isInstanceOf[Drop]) {
          scope.reportHasExitedIfNeeded(er, instr.getPosition)
        }
        typeInstr(instr, scope, branchInfo, idxInScope)
      }
      scope.applyPendingSmartcasts()
    }
  }

  def typeInstr(instr: Instr, currScope: Scope, branchInfo: BranchingInfo, idxInScope: Int)
               (using typeParamsCtx: TypeParamsContext): Unit = instr match {

    case loop@Loop(condScope, condVal, bodyScope, loopUpdatedVars) =>
      val (infoIfCondTrue, infoIfCondFalse) = proxyStore.extractRawBranchingInfos(condVal, branchInfo)
      for (varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- loopUpdatedVars) {
        (for {
          recurrence <- varData.recurrenceOpt
          monotonicity <- Some(recurrence.computeMonotonicity(solver)).filter(_ != NonMonotonous)
        } yield {
          val boundMode = if monotonicity == NonDecreasing then BoundMode.Upper else BoundMode.Lower
          val inferredBound = infoIfCondTrue.boundFor(condVal, boundMode, solver)
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
          currScope.saveType(condVal, inCondType) // after loop
          condScope.saveSmartcast(condVal, inCondType, 0) // inside condition
          bodyScope.saveSmartcast(condVal, inBodyType, 0) // inside body
          varData.handledThroughRecurrenceFlag = true
        }) orElse {
          // TODO lookup proxy of bodyLastVal to see if we can infer its type (maybe this can be unified with the "next step" interpretation in the previous case)
          val tpe =
            currScope.getLocalValuesContextUnsafe
              .valueOf(varId)
              .asInstanceOf[KnownAndInitialized]
              .declarationTypeAnnotOpt
              .orElse(typeHintsStore.getHints(condVal).find { hint =>
                subtypingCtx.isSubtype(currScope.currentTypeOf(beforeLoopVal), hint)
              })
              .getOrElse(currScope.currentTypeOf(beforeLoopVal).principalType)
          currScope.saveType(condVal, tpe)
          Some(())
        }
      }
      typeScopeInstructions(condScope, BranchingInfo.empty)
      subtypingCtx.enforceIsSubtype(condScope.currentTypeOf(condVal), BoolType, s"loop condition must have type $BoolType", loop.getPosition)
      typeScopeInstructions(bodyScope, infoIfCondTrue)
      for {
        varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- loopUpdatedVars
        if !varData.handledThroughRecurrenceFlag
      } {
        val typeAtEndOfBody = bodyScope.currentTypeOf(bodyLastVal)
        val typeInCond = condScope.currentTypeOf(condVal)
        lazy val msg = currScope.getLocalValuesContextUnsafe.valueOf(varId) match {
          case KnownAndInitialized(value, reassigStatus, Some(declTypeAnnot)) =>
            s"update of variable $varId in loop violate its type annotation $declTypeAnnot"
          case _ =>
            s"inferred incorrect type $typeInCond for variable $varId at loop body start, please provide a type annotation at variable declaration site"
        }
        subtypingCtx.enforceIsSubtype(typeAtEndOfBody, typeInCond, msg, loop.getPosition)
      }
      applyBranchInfo(currScope, infoIfCondFalse, idxInScope + 1)

    case disjunction@Disjunction(condVal, thenBr, elseBr, variables) =>
      val condType = currScope.currentTypeOf(condVal)
      subtypingCtx.enforceIsSubtype(condType, BoolType, s"condition must have type $BoolType", disjunction.getPosition)
      val (infoIfCondTrue, infoIfCondFalse) = proxyStore.extractRawBranchingInfos(condVal, branchInfo)
      typeScopeInstructions(thenBr, infoIfCondTrue)
      typeScopeInstructions(elseBr, infoIfCondFalse)
      for (varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) <- variables) {
        val thenType = thenBr.currentTypeOf(afterThenVal)
        val elseType = elseBr.currentTypeOf(afterElseVal)
        val joinType = {
          if elseBr.hasExited then thenType
          else if thenBr.hasExited then elseType
          else meetJoin.computeJoin(thenType, elseType)
        }
        currScope.saveType(joinedVal, joinType)
      }
      if (thenBr.hasExited && elseBr.hasExited) {
        currScope.markHasExited()
      }

    case staticTypeAssert@StaticTypeAssert(value, tpe) =>
      val valueType = currScope.currentTypeOf(value)
      subtypingCtx.enforceIsSubtypeExpAct(value, valueType, tpe, "type ascription", staticTypeAssert.getPosition)

    case StaticAssert(value) => ???

    case AssignVal(assigned, src) =>
      val assignedType = tryToApplyHint(src, currScope.currentTypeOf(src))
      currScope.saveType(assigned, assignedType)

    case AssignIntConst(assigned, src) =>
      currScope.saveType(assigned, IntRangeType.singleton(src))

    case AssignBoolConst(assigned, src) =>
      currScope.saveType(assigned, BoolType)

    case AssignStringConst(assigned, src) =>
      currScope.saveType(assigned, StringType)

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
      val ownerType = currScope.currentTypeOf(owner)
      val tpe = resolveFieldAccess(ownerType, field, fr.getPosition)
      proxyStore.getProxy(assigned).flatMap(currScope.smartcastFor) match {
        case Some(smartcastType) =>
          currScope.saveType(assigned, smartcastType)
        case None =>
          currScope.saveType(assigned, tpe)
      }

    case fw@FieldWrite(owner, field, rhs) if field.isNotResolvedYet =>
      val ownerType = currScope.currentTypeOf(owner)
      val fieldType = resolveFieldAccess(ownerType, field, fw.getPosition)
      val rhsType = currScope.currentTypeOf(rhs)
      tryToResolveTypeVars(fieldType, rhsType)
      subtypingCtx.enforceIsSubtypeExpAct(rhs, rhsType, fieldType, s"assignment to field ${field.fieldId}", fw.getPosition)

    case _: (InvokeFunc | FieldRead | FieldWrite) =>
      throw AssertionError("typing phase run more than once on the same piece of code")

    case HeapVarRead(assigned, heapVar) =>
      val tpe = heapVarsTypeStore.getTypeUnsafe(heapVar)
      currScope.saveType(assigned, tpe)

    case heapVarWrite@HeapVarWrite(heapVar, newValue) =>
      val newValType = currScope.currentTypeOf(newValue)
      heapVarsTypeStore.getType(heapVar) match {
        case Some(expType) =>
          subtypingCtx.enforceIsSubtypeExpAct(newValue, newValType, expType, "heap-allocated variable assignment", heapVarWrite.getPosition)
        case None =>
          // TODO maybe try to save refined types also here, instead of falling back to the principal type?
          heapVarsTypeStore.saveType(heapVar, newValType.principalType)
      }

    case invkClosure@InvokeClosure(assigned, callee, args) =>
      currScope.currentTypeOf(callee) match {
        case ClosureType(paramTypes, resultType) =>
          val argsWithVals = args.map(arg => Some(arg) -> currScope.currentTypeOf(arg))
          checkArgumentsList(paramTypes.map(None -> _), argsWithVals, "closure invocation", invkClosure.getPosition)
          currScope.saveType(assigned, resultType)
        case calleeType =>
          er.reportError(s"$calleeType is not callable", invkClosure.getPosition)
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

    case MkClosure(assigned, params, body) =>
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
      closuresCollectorFunc(ClosureInfo(params, body, resultTypeVar, branchInfo, typeParamsCtx))

    case tt@TypeTest(assigned, testedValue, testedTypeId) =>
      checkDowncast(testedValue, testedTypeId, currScope, tt.getPosition)
      currScope.saveType(assigned, BoolType)

    case cast@Cast(inValue, target) =>
      checkDowncast(inValue, target, currScope, cast.getPosition).foreach { assertedType =>
        currScope.saveSmartcast(inValue, assertedType, idxInScope + 1)
        proxyStore.getProxy(inValue).foreach { proxy =>
          currScope.saveSmartcast(proxy, assertedType, idxInScope + 1)
        }
      }

    case conv@Conversion(assigned, inValue, targetType) =>
      val inValType = currScope.currentTypeOf(inValue).principalType
      if (inValType == targetType || TypeConversion.conversionFor(inValType, targetType).isDefined) {
        currScope.saveType(assigned, targetType)
      } else {
        er.reportError(s"impossible conversion: $inValType to $targetType", conv.getPosition)
      }

    case ret@Return(retVal) =>
      funRetTypeOpt match {
        case Some(funRetType) =>
          val retValType = currScope.currentTypeOf(retVal)
          subtypingCtx.enforceIsSubtypeExpAct(retVal, retValType, funRetType, "return value", ret.getPosition)
        case None =>
          er.reportError("unexpected return in this position", ret.getPosition)
      }
      currScope.markHasExited()

    case panic@Panic(msg) =>
      val msgType = currScope.currentTypeOf(msg)
      subtypingCtx.enforceIsSubtype(msgType, StringType, s"panic message should have type $StringType", panic.getPosition)
      currScope.markHasExited()

    case Drop(droppedValue) => ()

    case LocalDecl(localId, tpe) => ()

    case scope: Scope =>
      typeScopeInstructions(scope, BranchingInfo.empty)

    case Smartcast(formula, tpe) =>
      throw AssertionError(s"unexpected smartcast in ${classOf[Typer].getSimpleName}")
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
    scope.smartcastFor(formula).getOrElse(formula match {
      case value: IdValue => scope.currentTypeOf(value)
      case IntConst(value) => IntType
      case BoolConst(value) => BoolType
      case StringConst(value) => StringType
      case sel@Select(owner, field) if field.isResolved =>
        scope.smartcastFor(sel).getOrElse(field.getInstantiatedFieldTypeUnsafe)
      case sel@Select(owner, field) if field.isNotResolvedYet =>
        val ownerType = typeFormula(owner, scope, posOpt)
        val tpe = resolveFieldAccess(ownerType, field, posOpt)
        scope.smartcastFor(sel).getOrElse(tpe)
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
        namedOrNone(scope.currentTypeOf(value))
      case Select(owner, field) =>
        if (field.isNotResolvedYet) {
          detectNominalTypeForSmartcast(owner, scope) match {
            case Some(ownerType) =>
              val selectType = resolveFieldAccess(ownerType, field, None)
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
              val retType = resolveFunSigAndCheckArgs(receiver, func, typeArgs, args, scope, None, reportErrors = false)
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
    val expectedOperandType = lhsType.principalType match {
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
    subtypingCtx.checkDowncastTarget(subjectType, tid) match {
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
      case IntRangeType(untypedLowerBoundOpt, untypedUpperBoundOpt) =>
        untypedLowerBoundOpt.foreach {
          typeFormula(_, currScope, posOpt)
        }
        untypedUpperBoundOpt.foreach {
          typeFormula(_, currScope, posOpt)
        }
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
    val StableField(id, tpe, value) = field
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
    val FunctionSignature(ownerName, functionName, typeParams, paramsInclThis, retType, sigScope, visibility, declPosOpt) = functionSignature

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

  private def applyBranchInfo(scope: Scope, branchInfo: BranchingInfo, idxInScope: Int)(using TypeParamsContext): Unit = {
    for ((subject, smartcastData) <- branchInfo.smartcasts) {
      for {
        originalType <- detectNominalTypeForSmartcast(subject, scope)
        smartcastType <- smartcastData.tryToSmartcast(originalType, resolutionCtx.typesReasoningCache, subtypingCtx)
      } {
        if (smartcastType.principalType == NothingType) {
          scope.markHasExited()
        } else {
          val oldType = scope.currentTypeOf(subject)
          val newType = meetJoin.computeMeet(oldType, smartcastType)
          scope.saveSmartcast(subject, smartcastType, idxInScope)
        }
      }
    }
    for (assumption <- branchInfo.assumptions) {
      val developedAssumption = proxyStore.develop(assumption)
      solver.assert(developedAssumption)
      val smartcasts = developedAssumption match {
        case LessOrEq(lhs, rhs) =>
          leqToSmartcasts(lhs, rhs)
        case LessThan(lhs, rhs) =>
          ltToSmartcasts(lhs, rhs)
        case _ => List.empty
      }
      smartcasts.foreach { (subject, smartcastType) =>
        scope.saveSmartcast(subject, smartcastType, idxInScope)
      }
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
    import FormulasDsl.*
    leqToSmartcasts(lhs + 1, rhs)
  }

  private def resolveFunSigAndCheckArgs(receiver: Formula, invkTarget: InvocationTarget, callTypeArgs: List[Type], callArgs: List[Formula], scope: Scope, posOpt: Option[Position], reportErrors: Boolean = true)
                                       (using TypeParamsContext): Type = {
    val receiverType = typeFormula(receiver, scope, posOpt)

    def errorCase() = {
      if (reportErrors) {
        er.reportError(s"method ${invkTarget.funId} not found in type $receiverType", posOpt)
      }
      invkTarget.markUnresolvable()
      NothingType
    }

    val typedCallArgs = callArgs.map(arg => Some(arg) -> typeFormula(arg, scope, posOpt))
    receiverType.principalType.withTypeVarsExpanded match {
      case NamedType(typeName, receiverTypeArgs, receiverArgs) =>
        resolutionCtx.resolveFunSig(typeName, invkTarget.funId) match {
          case FuncResolResult.Success(ownerSig, funSig) =>
            val receiverTypeSubst = instantiateTypes(ownerSig.typeParams, receiverTypeArgs, subtypingCtx, posOpt, None)
            val callTypeSubst = instantiateTypes(funSig.typeParams, callTypeArgs, subtypingCtx, posOpt, Option.when(reportErrors)(s"type $typeName"))
            val composedTypeSubst = receiverTypeSubst ++ callTypeSubst
            val paramTypes = funSig.paramsWithoutThis.map { (paramVal, tpe) =>
              Some(paramVal) -> tpe.substitute(composedTypeSubst, Map.empty)
            }
            val argsSubst = checkArgumentsList(paramTypes, typedCallArgs, s"call to ${invkTarget.funId}", posOpt)
            addToSubstIfValid(funSig.receiverVal, Some(receiver), argsSubst)
            val instantiatedRetType = funSig.retType.substitute(composedTypeSubst, argsSubst)
            invkTarget.resolve(ownerSig, funSig, instantiatedRetType)
            instantiatedRetType
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  private def resolveFieldAccess(owner: Type, fieldResolTarget: FieldResolutionTarget, posOpt: Option[Position]): Type = {

    def errorCase() = {
      er.reportError(s"field ${fieldResolTarget.fieldId} not found in type ${owner.principalType}", posOpt)
      fieldResolTarget.markUnresolvable()
      NothingType
    }

    owner.principalType match {
      case NamedType(typeName, typeArgs, args) =>
        resolutionCtx.resolveFieldAccess(typeName, fieldResolTarget.fieldId) match {
          case FieldResolResult.Success(ownerSig, field) =>
            // TODO check that we can indeed ignore errors here (reportErrors = false)
            val typeSubst = instantiateTypes(ownerSig.typeParams, typeArgs, subtypingCtx, posOpt, None)
            val instantiatedFieldType = field.tpe.substitute(typeSubst, Map.empty)
            fieldResolTarget.resolve(ownerSig, instantiatedFieldType)
            instantiatedFieldType
          case _ => errorCase()
        }
      case _ => errorCase()
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

  private def checkArgumentsList(params: Iterable[(Option[IdValue], Type)], args: Iterable[(Option[Formula], Type)], ctxDescr: String, posOpt: Option[Position]): mutable.Map[IdValue, Formula] = {
    val nParams = params.size
    val nArgs = args.size
    if (nParams != nArgs) {
      er.reportError(s"$ctxDescr: wrong number of arguments (expected $nParams, was $nArgs)", posOpt)
    }

    // first pass: try to resolve type variables
    val subst = mutable.Map.empty[IdValue, Formula]
    for (((paramValOpt, paramTypeBeforeSubst), (argOpt, argType)) <- params.zipCommons(args)) {
      val paramType = paramTypeBeforeSubst.substitute(Map.empty, subst)
      tryToResolveTypeVars(paramType, argType)
      paramValOpt.foreach { paramVal =>
        addToSubstIfValid(paramVal, argOpt, subst)
      }
    }

    // second pass: actually check types
    subst.clear()
    var argIdx = 1
    for (((paramValOpt, paramTypeBeforeSubst), (argOpt, argType)) <- params.zipCommons(args)) {
      val paramType = paramTypeBeforeSubst.substitute(Map.empty, subst)
      subtypingCtx.enforceIsSubtypeExpAct(argOpt, argType, paramType, s"${nth(argIdx)} argument of $ctxDescr", posOpt)
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
        .filter(_.isStable)
        .foreach { repl =>
          subst.put(paramVal, repl)
        }
    }
  }

  private def tryToResolveTypeVars(paramType: Type, argType: Type): Unit = (paramType, argType) match {
    case (NamedType(_, paramTypeArgs, _), NamedType(_, argsTypeArgs, _)) =>
      // FIXME account for variance?
      for ((tParam, tArg) <- paramTypeArgs.zipCommons(argsTypeArgs)) {
        tryToResolveTypeVars(tParam, tArg)
      }
    case (ClosureType(paramParams, paramRes), ClosureType(argParams, argRes)) =>
      for ((tParam, tArg) <- paramParams.zipCommons(argParams)) {
        tryToResolveTypeVars(tParam, tArg)
      }
      tryToResolveTypeVars(paramRes, argRes)
    case (tv: TypeVariable, argType) if !tv.isResolved =>
      tv.resolve(argType)
    case (tv: TypeVariable, argType) if tv.isResolved && subtypingCtx.isSubtype(tv.substitutedIfResolved, argType) =>
      tv.remapIfNotLocked(argType)
    case _ => ()
  }

  private def nth(i: Int): String = i match {
    case 1 => "first"
    case 2 => "second"
    case 3 => "third"
    case i => s"${i}th"
  }

}
