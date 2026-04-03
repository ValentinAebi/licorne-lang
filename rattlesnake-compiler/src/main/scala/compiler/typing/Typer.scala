package compiler.typing

import compiler.identifiers.{FunOrVarId, Identifier, TypeIdentifier}
import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.irs.SSA.FieldResolutionTarget.*
import compiler.irs.SSA.InvocationTarget.*
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
import compiler.valuesconversion.LocalValuesContext
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
                   solver: Solver,
                   simplifier: Simplifier,
                   absInt: AbstractInterpreter,
                   er: ErrorReporter
                 )(using CompilationStep) {

  private given ResolutionContext = resolutionCtx

  private given MeetJoinComputer = meetJoin

  private given ProxyStore = proxyStore

  private given Simplifier = simplifier

  def typeScopeInstructions(scope: Scope, branchInfo: BranchingInfo)(using TypeParamsContext): Unit = {
    solver.onNewFrame {
      scope.resetHasExited()
      applyBranchInfo(scope, branchInfo)
      if (solver.checkUnsat()) {
        scope.markHasExited()
      }
      for (instr <- scope.instructions) {
        if (!instr.isInstanceOf[Drop]) {
          scope.reportHasExitedIfNeeded(er, instr.getPosition)
        }
        typeInstr(instr, scope, branchInfo)
      }
    }
  }

  def typeInstr(instr: Instr, currScope: Scope, branchInfo: BranchingInfo)
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
          condScope.saveSmartcast(condVal, inCondType) // inside condition
          bodyScope.saveSmartcast(condVal, inBodyType) // inside body
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
                  && subtypingCtx.isSubtype(bodyScope.currentTypeOf(bodyLastVal), hint)
              })
              .getOrElse(currScope.currentTypeOf(beforeLoopVal).principalType)
          currScope.saveType(condVal, tpe)
          condScope.saveSmartcast(condVal, tpe)
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
      applyBranchInfo(currScope, infoIfCondFalse)

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

    case invk@InvokeFunc(assigned, receiver, UnresolvedFun(funId), typeArgs, args) =>
      val (invkTarget, returnType) = resolveFunSigAndCheckArgs(receiver, funId, typeArgs, args, currScope, invk.getPosition)
      invk.func = invkTarget
      currScope.saveType(assigned, returnType)
      currScope.markHasExitedIfNothing(returnType)

    case fr@FieldRead(assigned, owner, UnresolvedField(fieldId)) =>
      val ownerType = currScope.currentTypeOf(owner)
      val (fieldResolTarget, tpe) = resolveFieldAccess(ownerType, fieldId, fr.getPosition)
      fr.field = fieldResolTarget
      currScope.saveType(assigned, tpe)

    case fw@FieldWrite(owner, UnresolvedField(fieldId), rhs) =>
      val ownerType = currScope.currentTypeOf(owner)
      val (fieldResolTarget, fieldType) = resolveFieldAccess(ownerType, fieldId, fw.getPosition)
      fw.field = fieldResolTarget
      val rhsType = currScope.currentTypeOf(rhs)
      subtypingCtx.enforceIsSubtypeExpAct(rhs, rhsType, fieldType, s"assignment to field $fieldId", fw.getPosition)

    case _: (InvokeFunc | FieldRead | FieldWrite) =>
      throw AssertionError("typing phase run more than once on the same piece of code")

    case InvokeClosure(assigned, callee, args) => ???

    case instantiate@Instantiate(assigned, classOrRecordName, typeArgs) =>
      resolutionCtx.resolveTypeSigAs[UserInstantiableTypeSig](classOrRecordName) match {
        case Some(typeSig) =>
          val typesSubst = instantiateTypes(typeSig.typeParams, typeArgs, subtypingCtx, instantiate.getPosition, Some(s"instantiation of $classOrRecordName"))
          currScope.saveType(assigned, typeSig.toType(typesSubst))
        case None =>
          er.reportError(s"type $classOrRecordName not found or not instantiable", instantiate.getPosition)
      }

    case MkClosure(assigned, params, body) => ???

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
      case sel@Select(owner, ResolvedField(_, _, instantiatedFieldType)) =>
        scope.smartcastFor(sel).getOrElse(instantiatedFieldType)
      case sel@Select(owner, UnresolvedField(fieldId)) =>
        val ownerType = typeFormula(owner, scope, posOpt)
        val (resolvedField, tpe) = resolveFieldAccess(ownerType, fieldId, posOpt)
        sel.field = resolvedField
        scope.smartcastFor(sel).getOrElse(tpe)
      case Select(owner, _: UnresolvableField) => NothingType
      case Call(receiver, ResolvedFun(ownerSig, funSig, instantiatedReturnType), typeArgs, args) => instantiatedReturnType
      case call@Call(receiver, UnresolvedFun(funId), typeArgs, args) =>
        val (invocationTarget, retType) = resolveFunSigAndCheckArgs(receiver, funId, typeArgs, args, scope, posOpt)
        call.func = invocationTarget
        retType
      case Call(receiver, _: UnresolvableFun, typeArgs, args) => NothingType
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
        field match {
          case UnresolvedField(fieldId) =>
            detectNominalTypeForSmartcast(owner, scope) match {
              case Some(ownerType) =>
                val (_, selectType) = resolveFieldAccess(ownerType, fieldId, None, reportErrors = false)
                namedOrNone(selectType)
              case None => None
            }
          case ResolvedField(receiverSig, fieldId, instantiatedFieldType: NamedType) => Some(instantiatedFieldType)
          case _ => None
        }
      case Call(receiver, func, typeArgs, args) =>
        func match {
          case UnresolvedFun(funId) =>
            detectNominalTypeForSmartcast(receiver, scope) match {
              case Some(receiverType) =>
                val (_, retType) = resolveFunSigAndCheckArgs(receiver, funId, typeArgs, args, scope, None, reportErrors = false)
                namedOrNone(retType)
              case None => None
            }
          case ResolvedFun(ownerSig, funSig, instantiatedReturnType: NamedType) => Some(instantiatedReturnType)
          case _ => None
        }
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
    absIntFunc(lhsType, rhsType) match {
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
    val negatedType = absInt.unaryNegType(operandType) match {
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

  def dealiasAndTypeType(tpe: Type, ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
                        (using tParamsCtx: TypeParamsContext): Unit = {
    dealiasingCtx.dealiasType(tpe) match {
      case primitiveType: PrimitiveType => ()
      case namedType: NamedType => typeNamedTypeDealiased(namedType, ambientVarianceOpt, currScope, posOpt)
      case ClosureType(paramTypes, resultType) =>
        for paramType <- paramTypes do {
          dealiasAndTypeType(paramType, ambientVarianceOpt.map(_ * Contravariant), currScope, posOpt)
        }
        dealiasAndTypeType(resultType, ambientVarianceOpt.map(_ * Covariant), currScope, posOpt)
      case tv: TypeVariable => ()
      case UnionType(types) =>
        for tpe <- types do {
          dealiasAndTypeType(tpe, ambientVarianceOpt, currScope, posOpt)
        }
      case IntersectionType(types) =>
        for tpe <- types do {
          dealiasAndTypeType(tpe, ambientVarianceOpt, currScope, posOpt)
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

  def typeNamedTypeDealiased(namedType: NamedType, ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
                            (using typeParamsCtx: TypeParamsContext): Unit = {
    val NamedType(typeName, typeArgs, args) = namedType
    if (args.nonEmpty) {
      er.reportError(s"unexpected value arguments for type $typeName", posOpt)
    }
    typeParamsCtx.resolve(typeName) match {
      case Some(tpInfo) =>
        if (typeArgs.nonEmpty) {
          er.reportError(s"$typeName is a type variable, hence it cannot take type arguments", posOpt)
        }
      case None => resolutionCtx.resolveTypeSig(typeName) match {
        case Some(sig) =>
          typeTypeArgsList(typeName, sig.typeParams, typeArgs, ambientVarianceOpt, currScope, posOpt)
          val argsWithTypes = args.map(arg => Some(arg) -> typeFormula(arg, currScope, posOpt))
          val paramsWithType = sig.params.map {
            case (paramId, (paramType, paramVal)) => paramVal -> paramType
          }
          checkArgumentsList(paramsWithType, argsWithTypes, sig.id, posOpt)
        case None =>
          er.reportError(s"type not found: $typeName", posOpt)
      }
    }
  }

  def typeField(field: Field, currScope: Scope, typeParamsCtx: TypeParamsContext, posOpt: Option[Position]): Unit = field match {
    case ReassignableField(id, tpe) => dealiasAndTypeType(tpe, Some(Invariant), currScope, posOpt)(using typeParamsCtx)
    case field: StableField => typeStableField(field, currScope, posOpt)(using typeParamsCtx)
  }

  def typeStableField(field: StableField, currScope: Scope, posOpt: Option[Position])
                     (using typeParamsCtx: TypeParamsContext): Unit = {
    val StableField(id, tpe, value) = field
    dealiasAndTypeType(tpe, Some(Covariant), currScope, posOpt)
  }

  // TODO merge with typeFunTypeParam?
  def typeTypeTypeParam(typeTypeParamInfo: TypeTypeParamInfo, currScope: Scope, posOpt: Option[Position])
                       (using typeParamsCtx: TypeParamsContext): Unit = {
    val TypeTypeParamInfo(tid, variance, upperBoundOpt, lowerBoundOpt) = typeTypeParamInfo
    upperBoundOpt.foreach {
      dealiasAndTypeType(_, None, currScope, posOpt)
    }
    lowerBoundOpt.foreach {
      dealiasAndTypeType(_, None, currScope, posOpt)
    }
  }

  def typeFunTypeParam(functionTypeParamInfo: FunctionTypeParamInfo, currScope: Scope, posOpt: Option[Position])
                      (using typeParamsCtx: TypeParamsContext): Unit = {
    val FunctionTypeParamInfo(tid, upperBoundOpt, lowerBoundOpt) = functionTypeParamInfo
    upperBoundOpt.foreach {
      dealiasAndTypeType(_, None, currScope, posOpt)
    }
    lowerBoundOpt.foreach {
      dealiasAndTypeType(_, None, currScope, posOpt)
    }
  }

  def typeFunSig(functionSignature: FunctionSignature, ownerTypeParamsCtx: TypeParamsContext): Unit = {
    val FunctionSignature(ownerName, functionName, typeParams, paramsInclThis, retType, sigScope, visibility, declPosOpt) = functionSignature

    val fullTypeParamsCtx = processTypeParamsAccumulating(ownerTypeParamsCtx, typeParams) {
      typeFunTypeParam(_, functionSignature.sigScope, functionSignature.declPosOpt)
    }
    for (paramId, paramType) <- paramsInclThis do {
      dealiasAndTypeType(paramType, Some(Contravariant), functionSignature.sigScope, functionSignature.declPosOpt)(using fullTypeParamsCtx)
      if (sigScope.valuesCtx.globalCtx.getNameOfObject(paramId).isEmpty) {
        sigScope.saveType(paramId, paramType)(using fullTypeParamsCtx)
      }
    }
    dealiasAndTypeType(retType, Some(Covariant), functionSignature.sigScope, functionSignature.declPosOpt)(using fullTypeParamsCtx)
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
    typeSupertypesAsInterfaces(interfaceSig, resolutionCtx)
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
    typeSupertypesAsInterfaces(classSig, resolutionCtx)
  }

  def typeObjectSig(objSig: ObjectSignature): Unit = {
    val ObjectSignature(id, functions, directSupertypes, sigScope, declPosOpt) = objSig

    for (_, funSig) <- functions do {
      typeFunSig(funSig, TypeParamsContext.empty)
    }
    typeSupertypes(objSig, "interface", resolutionCtx)
  }

  def typeDatatypeSig(datatypeSig: DatatypeSignature): Unit = {
    val DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, sigScope, declPosOpt) = datatypeSig

    processTypeParamsAccumulating(TypeParamsContext.empty, typeParams) {
      typeTypeTypeParam(_, sigScope, declPosOpt)
    }
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    typeSupertypesAsDatatypes(datatypeSig, resolutionCtx)
  }

  def typeRecordSig(recordSig: RecordSignature): Unit = {
    val RecordSignature(id, typeParams, fields, directSupertypes, sigScope, declPosOpt) = recordSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, sigScope, declPosOpt)
    }
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for (_, fld) <- fields do {
      typeStableField(fld, sigScope, declPosOpt)
    }
    typeSupertypesAsDatatypes(recordSig, resolutionCtx)
  }

  private def applyBranchInfo(scope: Scope, branchInfoRaw: BranchingInfo)(using TypeParamsContext): Unit = {
    val branchInfo = branchInfoRaw.filteredStable(this)
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
          scope.saveSmartcast(subject, smartcastType)
        }
      }
    }
    for (assumption <- branchInfo.assumptions) {
      solver.assert(proxyStore.develop(assumption))
      val smartcastOpt = assumption match {
        // TODO maybe we should rather isolate the term with the most narrow scope?
        //  (could be for instance x in x + y <= a + b + 1)
        case LessOrEq(lhs, rhs) =>
          leqToSmartcast(lhs, rhs)
        case LessThan(lhs, rhs) =>
          ltToSmartcast(lhs, rhs)
        case _ => None
      }
      smartcastOpt.foreach { (subject, smartcastType) =>
        scope.saveSmartcast(subject, smartcastType)
      }
    }
  }

  private def leqToSmartcast(lhs: Formula, rhs: Formula): Option[(Formula, Type)] = {
    if (lhs.typeCanMention(rhs)) {
      Some(lhs -> IntRangeType.ofUpperBound(rhs))
    } else if (rhs.typeCanMention(lhs)) {
      Some(rhs -> IntRangeType.ofLowerBound(lhs))
    } else None
  }

  private def ltToSmartcast(lhs: Formula, rhs: Formula): Option[(Formula, Type)] = {
    import FormulasDsl.*
    if (lhs.typeCanMention(rhs)) {
      Some(lhs -> IntRangeType.ofUpperBound(rhs - 1))
    } else if (rhs.typeCanMention(lhs)) {
      Some(rhs -> IntRangeType.ofLowerBound(lhs + 1))
    } else None
  }

  private def resolveFunSigAndCheckArgs(receiver: Formula, funId: FunOrVarId, callTypeArgs: List[Type], callArgs: List[Formula], scope: Scope, posOpt: Option[Position], reportErrors: Boolean = true)
                                       (using TypeParamsContext): (InvocationTarget, Type) = {
    val receiverType = typeFormula(receiver, scope, posOpt)

    def errorCase() = {
      if (reportErrors) {
        er.reportError(s"method $funId not found in type $receiverType", posOpt)
      }
      (UnresolvableFun(funId), NothingType)
    }

    val typedCallArgs = callArgs.map(arg => Some(arg) -> typeFormula(arg, scope, posOpt))
    receiverType.principalType match {
      case NamedType(typeName, receiverTypeArgs, receiverArgs) =>
        resolutionCtx.resolveFunSig(typeName, funId) match {
          case FuncResolResult.Success(ownerSig, funSig) =>
            val receiverTypeSubst = instantiateTypes(ownerSig.typeParams, receiverTypeArgs, subtypingCtx, posOpt, None)
            val callTypeSubst = instantiateTypes(funSig.typeParams, callTypeArgs, subtypingCtx, posOpt, Option.when(reportErrors)(s"type $typeName"))
            val composedTypeSubst = receiverTypeSubst ++ callTypeSubst
            val paramTypes = funSig.paramsWithoutThis
              .map((paramVal, tpe) => paramVal -> tpe.substitute(composedTypeSubst, Map.empty))
            val argsSubst = checkArgumentsList(paramTypes, typedCallArgs, funId, posOpt)
            addToSubstIfValid(funSig.receiverVal, Some(receiver), argsSubst)
            val instantiatedRetType = funSig.retType.substitute(composedTypeSubst, argsSubst)
            val invocationTarget = ResolvedFun(ownerSig, funSig, instantiatedRetType)
            (invocationTarget, instantiatedRetType)
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  private def resolveFieldAccess(owner: Type, fieldId: FunOrVarId, posOpt: Option[Position], reportErrors: Boolean = true): (FieldResolutionTarget, Type) = {

    def errorCase() = {
      if (reportErrors) {
        er.reportError(s"field $fieldId not found in type ${owner.principalType}", posOpt)
      }
      (UnresolvableField(fieldId), NothingType)
    }

    owner.principalType match {
      case NamedType(typeName, typeArgs, args) =>
        resolutionCtx.resolveFieldAccess(typeName, fieldId) match {
          case FieldResolResult.Success(ownerSig, field) =>
            // TODO check that we can indeed ignore errors here (reportErrors = false)
            val typeSubst = instantiateTypes(ownerSig.typeParams, typeArgs, subtypingCtx, posOpt, None)
            val instantiatedFieldType = field.tpe.substitute(typeSubst, Map.empty)
            (ResolvedField(ownerSig, fieldId, instantiatedFieldType), instantiatedFieldType)
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
          checkTypeIsInBounds(tArg, tParam.upperBoundOpt, tParam.lowerBoundOpt, posOpt)
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
        tp.tid -> typeVarsCtx.newTypeVariable(tp.tid.stringId, tp.upperBoundOpt, tp.lowerBoundOpt, posOpt)
      })
    }
  }

  def checkTypeIsInBounds(tpe: Type, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type], posOpt: Option[Position]): Unit = {
    upperBoundOpt.foreach { upperBound =>
      subtypingCtx.enforceIsSubtype(tpe, upperBound, s"type $tpe violates upper bound $upperBound", posOpt)
    }
    lowerBoundOpt.foreach { lowerBound =>
      subtypingCtx.enforceIsSubtype(lowerBound, tpe, s"type $tpe violates lower bound $lowerBound", posOpt)
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

  private def typeSupertypesAsInterfaces(sig: EncapsulatedTypeSig, resolutionCtx: ResolutionContext): Unit =
    typeSupertypes[InterfaceSignature](sig, "interface", resolutionCtx)

  private def typeSupertypesAsDatatypes(sig: UnencapsulatedTypeSig, resolutionCtx: ResolutionContext): Unit =
    typeSupertypes[DatatypeSignature](sig, "datatype", resolutionCtx)

  private def typeSupertypes[S <: AbstractTypeSig : ClassTag](sig: RuntimeTypeSignature, superTKindDescr: String, resolutionCtx: ResolutionContext): Unit = {
    for (superT <- sig.directSupertypes) {
      dealiasingCtx.dealiasType(superT) match {
        case namedType: NamedType =>
          if (resolutionCtx.resolveTypeSigAs[S](superT.typeName).isEmpty) {
            er.reportError(s"$superTKindDescr not found: ${superT.typeName}", sig.declPosOpt)
          }
        case dealiasedSuperT =>
          er.reportError(s"type $superT expands to $dealiasedSuperT, which cannot be a supertype of ${sig.id}", sig.declPosOpt)
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

  private def checkSupertypesOfUnencapsulated(sig: UnencapsulatedTypeSig, resolutionCtx: ResolutionContext): Unit = {
    for (superT <- sig.directSupertypes) {
      if (resolutionCtx.resolveTypeSigAs[DatatypeSignature](superT.typeName).isEmpty) {
        er.reportError(s"datatype not found: ${superT.typeName}", sig.declPosOpt)
      }
    }
  }

  private def typeTypeArgsList(tid: TypeIdentifier, tParams: List[TypeParamInfo], tArgs: List[Type], ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
                              (using TypeParamsContext): Unit = {
    if (tParams.size != tArgs.size) {
      er.reportError(s"wrong number of type parameters for $tid: expected ${tParams.size}, was ${tArgs.size}", posOpt)
    }
    val tInfosIter = tParams.iterator
    for (tArg <- tArgs) {
      val nestedAmbientVariance = tInfosIter.nextOption().flatMap(expVariance(ambientVarianceOpt, _))
      dealiasAndTypeType(tArg, nestedAmbientVariance, currScope, posOpt)
    }
  }

  private def expVariance(ambientVarianceOpt: Option[Variance], tParam: TypeParamInfo): Option[Variance] = (tParam, ambientVarianceOpt) match {
    case (tParam: TypeTypeParamInfo, Some(ambientVariance)) =>
      Some(tParam.variance * ambientVariance)
    case _ => None
  }

  private def checkArgumentsList(params: Iterable[(IdValue, Type)], args: Iterable[(Option[Formula], Type)], argsTaker: Identifier, posOpt: Option[Position]): mutable.Map[IdValue, Formula] = {
    val nParams = params.size
    val nArgs = args.size
    if (nParams != nArgs) {
      er.reportError(s"call to $argsTaker: wrong number of arguments (expected $nParams, was $nArgs)", posOpt)
    }
    val subst = mutable.Map.empty[IdValue, Formula]
    var argIdx = 1
    for (((paramVal, paramTypeBeforeSubst), (argOpt, argType)) <- params.zipCommons(args)) {
      val paramType = paramTypeBeforeSubst.substitute(Map.empty, subst)
      tryResolveTypeVars(paramType, argType)
      subtypingCtx.enforceIsSubtypeExpAct(argOpt, argType, paramType, s"${nth(argIdx)} argument of call to $argsTaker", posOpt)
      addToSubstIfValid(paramVal, argOpt, subst)
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

  private def tryResolveTypeVars(paramType: Type, argType: Type): Unit = (paramType, argType) match {
    case (NamedType(_, paramTypeArgs, _), NamedType(_, argsTypeArgs, _)) =>
      for ((tParam, tArg) <- paramTypeArgs.zipCommons(argsTypeArgs)) {
        tryResolveTypeVars(tParam, tArg)
      }
    case (ClosureType(paramParams, paramRes), ClosureType(argParams, argRes)) =>
      for ((tParam, tArg) <- paramParams.zipCommons(argParams)) {
        tryResolveTypeVars(tParam, tArg)
      }
      tryResolveTypeVars(paramRes, argRes)
    case (tv: TypeVariable, argType) if !tv.isResolved =>
      tv.resolve(argType)
    case _ => ()
  }

  private def nth(i: Int): String = i match {
    case 1 => "first"
    case 2 => "second"
    case 3 => "third"
    case i => s"${i}th"
  }

}
