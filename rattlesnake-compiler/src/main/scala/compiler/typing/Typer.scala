package compiler.typing

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.SSA.*
import compiler.lang
import compiler.lang.*
import compiler.lang.Field.*
import compiler.lang.Formulas.{substitute as _, *}
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.*
import compiler.lang.Variance.*
import compiler.pipeline.CompilationStep
import compiler.recurrences.Recurrence.Monotonicity.*
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.smt.Solver
import compiler.typing.contexts.*
import compiler.typing.contexts.ResolutionContext.{FieldResolResult, FuncResolResult}
import compiler.valproxies.{BoundMode, BranchingInfo, ProxyStore}
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized

import scala.collection.mutable
import scala.reflect.{ClassTag, classTag}


final class Typer(
                   dealiasingCtx: DealiasingContext,
                   resolutionCtx: ResolutionContext,
                   typeVarsCtx: TypeVariablesContext,
                   subtypingCtx: SubtypingContext,
                   meetJoin: MeetJoinComputer,
                   proxyStore: ProxyStore,
                   absInt: AbstractInterpreter,
                   solver: Solver,
                   er: ErrorReporter
                 )(using CompilationStep) {

  private given ResolutionContext = resolutionCtx

  def typeFunction(function: Function, ownerTypeParamsCtx: TypeParamsContext)
                  (using subtypingCtx: SubtypingContext): Unit = {
    val Function(ownerId, funId, bodyOpt) = function
    val funSig = resolutionCtx.resolveFunSig(ownerId, funId).forceGetFunSig
    bodyOpt.foreach { body =>
      val typeParamsCtx = ownerTypeParamsCtx.extendedWith(funSig.typeParams)
      typeScopeInstructions(body, BranchingInfo.empty)(using typeParamsCtx)
    }
  }

  def typeScopeInstructions(scope: Scope, branchInfo: BranchingInfo)(using TypeParamsContext): Unit = {
    solver.onNewFrame {
      applyBranchInfo(scope, branchInfo)
      if (solver.checkUnsat()) {
        scope.markHasExited()
      }
      for (untypedInstr <- scope.instructions) {
        scope.reportHasExitedIfNeeded(er, untypedInstr.getPosition)
        typeInstr(untypedInstr, scope)
      }
    }
  }

  def typeInstr(instr: Instr, currScope: Scope)
               (using typeParamsCtx: TypeParamsContext): Unit = instr match {
    case loop@Loop(condScope, condVal, bodyScope, loopUpdatedVars) =>
      val (infoIfCondTrue, infoIfCondFalse) = proxyStore.extractRawBranchingInfos(condVal)
      for (varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- loopUpdatedVars) {
        (for {
          recurrence <- varData.recurrenceOpt
          monotonicity <- Some(recurrence.computeMonotonicity(solver)).filter(_ != NonMonotonous)
          inBodyType <- Some {
            val boundMode = if monotonicity == NonDecreasing then BoundMode.Upper else BoundMode.Lower
            val inferredBound = infoIfCondTrue.boundFor(condVal, boundMode, solver)
            val preIterationBoundOpt = proxyStore.getProxy(beforeLoopVal)
            if monotonicity == NonDecreasing
            then IntRangeType(preIterationBoundOpt, inferredBound)
            else IntRangeType(inferredBound, preIterationBoundOpt)
          }
          feedbackType <- absInt.interpretUnderAssumptions(recurrence.induct, Map(recurrence.inductVal -> inBodyType), None)
        } yield {
          val inCondType = meetJoin.computeJoin(inBodyType, feedbackType)
          condScope.saveType(condVal, inCondType)
          bodyScope.saveSmartcast(condVal, inBodyType)
          varData.handledThroughRecurrenceFlag = true
        }) orElse {
          // TODO lookup proxy of bodyLastVal to see if we can infer its type (maybe this can be unified with the "next step" interpretation in the previous case)
          val tpe =
            currScope.getLocalValuesContextUnsafe
              .valueOf(varId)
              .asInstanceOf[KnownAndInitialized]
              .declarationTypeAnnotOpt
              .getOrElse(currScope.currentTypeOf(beforeLoopVal))
          condScope.saveType(condVal, tpe)
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
        subtypingCtx.enforceIsSubtype(typeAtEndOfBody, typeInCond, s"cannot infer type of variable $varId inside loop, please provide a type annotation", loop.getPosition)
      }
      applyBranchInfo(currScope, infoIfCondFalse)
    case disjunction@Disjunction(condVal, thenBr, elseBr, variables) =>
      val condType = currScope.currentTypeOf(condVal)
      subtypingCtx.enforceIsSubtype(condType, BoolType, s"condition must have type $BoolType", disjunction.getPosition)
      val (infoIfCondTrue, infoIfCondFalse) = proxyStore.extractRawBranchingInfos(condVal)
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
      }
    case staticTypeAssert@StaticTypeAssert(value, tpe) =>
      val valueType = currScope.currentTypeOf(value)
      subtypingCtx.enforceIsSubtypeExpAct(value, valueType, tpe, "type annotation", staticTypeAssert.getPosition)
    case StaticAssert(value) => ???
    case AssignVal(assigned, src) =>
      currScope.saveType(assigned, currScope.currentTypeOf(src))
    case AssignIntConst(assigned, src) =>
      currScope.saveType(assigned, IntRangeType.singleton(src))
    case AssignBoolConst(assigned, src) =>
      currScope.saveType(assigned, BoolType)
    case AssignStringConst(assigned, src) =>
      currScope.saveType(assigned, StringType)
    case neg@NumNeg(assigned, operand) =>
      val posOpt = neg.getPosition
      val negType = typeUnaryNeg(operand, currScope, posOpt).filtered(assigned, Invariant)
      currScope.saveType(assigned, negType)
    case add@Add(assigned, lhs, rhs) =>
      typeNumericBinopForTarget(assigned, lhs, rhs, currScope, absInt.typePlusType, Operator.Plus, add.getPosition)
    case sub@Sub(assigned, lhs, rhs) =>
      typeNumericBinopForTarget(assigned, lhs, rhs, currScope, absInt.typeMinusType, Operator.Minus, sub.getPosition)
    case mul@Mul(assigned, lhs, rhs) =>
      typeNumericBinopForTarget(assigned, lhs, rhs, currScope, absInt.typeTimesType, Operator.Times, mul.getPosition)
    case div@Div(assigned, lhs, rhs) =>
      typeNumericBinopForTarget(assigned, lhs, rhs, currScope, absInt.typeDivType, Operator.Div, div.getPosition)
    case rem@Rem(assigned, lhs, rhs) =>
      typeNumericBinopForTarget(assigned, lhs, rhs, currScope, absInt.typeModuloType, Operator.Modulo, rem.getPosition)
    case and@And(assigned, lhs, rhs) =>
      typeLogicalBinopForTarget(assigned, lhs, rhs, currScope, Operator.And, and.getPosition)
    case or@Or(assigned, lhs, rhs) =>
      typeLogicalBinopForTarget(assigned, lhs, rhs, currScope, Operator.Or, or.getPosition)
    case LogicNeg(assigned, operand) => ???
    case Equal(assigned, lhs, rhs) => ???
    case Leq(assigned, lhs, rhs) => ???
    case Lt(assigned, lhs, rhs) => ???
    case FieldRead(assigned, owner, field) => ???
    case InvokeFunc(assigned, receiver, func, typeArgs, args) => ???
    case InvokeClosure(assigned, callee, args) => ???
    case Instantiate(assigned, classOrRecordName, typeArgs) => ???
    case MkClosure(assigned, params, body) => ???
    case TypeTest(assigned, testedValue, testedTypeId) => ???
    case Conversion(assigned, inValue, targetType) => ???
    case FieldWrite(owner, field, rhs) => ???
    case Return(retVal) => ???
    case Panic(msg) => ???
    case Cast(inValue, target) => ???
    case Drop(droppedValue) => ???
    case LocalDecl(localId, tpe) => ???
    case scope: Scope =>
      typeScopeInstructions(scope, BranchingInfo.empty)
  }

  def typeFormula(formula: Formula, scope: Scope, posOpt: Option[Position])
                 (using typeParamsCtx: TypeParamsContext): Type =
    scope.smartcastFor(formula).getOrElse(formula match {
      case value: IdValue => scope.currentTypeOf(value)
      case IntConst(value) => IntType
      case BoolConst(value) => BoolType
      case StringConst(value) => StringType
      case sel@Select(owner, FieldResolutionTarget.Resolved(_, _, instantiatedFieldType)) =>
        scope.smartcastFor(sel).getOrElse(instantiatedFieldType)
      case sel@Select(owner, FieldResolutionTarget.Unresolved(fieldId)) =>
        val ownerType = typeFormula(owner, scope, posOpt)
        val (resolvedField, tpe) = resolveFieldAccess(ownerType, fieldId, posOpt)
        sel.field = resolvedField
        scope.smartcastFor(sel).getOrElse(tpe)
      case Select(owner, _: FieldResolutionTarget.Unresolvable) => NothingType
      case Call(receiver, InvocationTarget.Resolved(ownerSig, funSig, instantiatedReturnType), args) => instantiatedReturnType
      case call@Call(receiver, InvocationTarget.Unresolved(funId), args) =>
        val receiverType = typeFormula(receiver, scope, posOpt)
        val (invocationTarget, retType) = resolveFunSig(receiverType, funId, posOpt)
        call.func = invocationTarget
        retType
      case Call(receiver, _: InvocationTarget.Unresolvable, args) => NothingType
      case Plus(lhs, rhs) =>
        typeNumericBinop(lhs, rhs, scope, absInt.typePlusType, Operator.Plus, posOpt)
      case Neg(operand) =>
        typeUnaryNeg(operand, scope, posOpt)
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
      case LogicalNot(operand) => ???
      case Equality(lhs, rhs) => ???
      case LessOrEq(lhs, rhs) => ???
      case LessThan(lhs, rhs) => ???
      case TypePredicate(lhs, rhs) => ???
    })

  private def typeNumericBinopForTarget(assigTarget: IdValue, lhs: Formula, rhs: Formula, currScope: Scope,
                                        absIntFunc: (Type, Type) => Option[Type],
                                        op: Operator, posOpt: Option[Position])
                                       (using TypeParamsContext): Unit = {
    val tpe = typeNumericBinop(lhs, rhs, currScope, absIntFunc, op, posOpt).filtered(assigTarget, Invariant)
    currScope.saveType(assigTarget, tpe)
  }

  private def typeNumericBinop(lhs: Formula, rhs: Formula, currScope: Scope,
                               absIntFunc: (Type, Type) => Option[Type],
                               op: Operator, posOpt: Option[Position])
                              (using TypeParamsContext): Type = {
    val lhsType = typeFormula(lhs, currScope, posOpt)
    val rhsType = typeFormula(rhs, currScope, posOpt)
    absIntFunc(lhsType, rhsType) match {
      case Some(tpe) => tpe
      case None =>
        er.reportError(s"no operator $op found for types $lhsType and $rhsType", posOpt)
        NothingType
    }
  }

  private def typeLogicalBinopForTarget(assignmentTarget: IdValue, lhs: Formula, rhs: Formula, currScope: Scope, op: Operator, posOpt: Option[Position])
                                       (using TypeParamsContext): Unit = {
    val tpe = typeLogicalBinop(lhs, rhs, currScope, op, posOpt).filtered(assignmentTarget, Invariant)
    currScope.saveType(assignmentTarget, tpe)
  }

  private def typeLogicalBinop(lhs: Formula, rhs: Formula, currScope: Scope, op: Operator, posOpt: Option[Position])
                              (using TypeParamsContext): Type = {
    val lhsType = typeFormula(lhs, currScope, posOpt)
    subtypingCtx.enforceIsSubtypeExpAct(lhsType, BoolType, s"left operand of $op", posOpt)
    val rhsType = typeFormula(rhs, currScope, posOpt)
    subtypingCtx.enforceIsSubtypeExpAct(rhsType, BoolType, s"right operand of $op", posOpt)
    BoolType
  }

  private def typeUnaryNeg(operand: Formula, currScope: Scope, posOpt: Option[Position])
                          (using TypeParamsContext): Type = {
    val operandType = typeFormula(operand, currScope, posOpt)
    val negatedType = absInt.unaryNegType(operandType) match {
      case Some(negType) => negType
      case None =>
        er.reportError(s"no unary operator ${Operator.Modulo} found for operand type $operandType", posOpt)
        NothingType
    }
    negatedType
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
          typeArgsList(typeName, sig.params.size, args, currScope, posOpt)
        case None =>
          er.reportError(s"type not found: $typeName", posOpt)
      }
    }
  }

  def typeField(field: Field, currScope: Scope, posOpt: Option[Position])(using typeParamsCtx: TypeParamsContext): Unit = field match {
    case ReassignableField(id, tpe) => dealiasAndTypeType(tpe, Some(Invariant), currScope, posOpt)
    case field: StableField => typeStableField(field, currScope, posOpt)
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

  def typeFunSig(functionSignature: FunctionSignature)(using typeParamsCtx: TypeParamsContext): Unit = {
    val FunctionSignature(ownerName, functionName, typeParams,
      paramsInclThis, retType, sigScope, visibility, declPosOpt) = functionSignature
    for typeParam <- typeParams do {
      typeFunTypeParam(typeParam, functionSignature.sigScope, functionSignature.declPosOpt)
    }
    for (paramId, paramType) <- paramsInclThis do {
      dealiasAndTypeType(paramType, Some(Contravariant), functionSignature.sigScope, functionSignature.declPosOpt)
    }
    dealiasAndTypeType(retType, Some(Covariant), functionSignature.sigScope, functionSignature.declPosOpt)
  }

  def typeInterfaceSig(interfaceSig: InterfaceSignature): Unit = {
    val InterfaceSignature(id, typeParams, functions, directSupertypes, sigScope, declPosOpt) = interfaceSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, sigScope, declPosOpt)
    }
    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypesAsInterfaces(interfaceSig, resolutionCtx)
  }

  def typeClassSig(classSig: ClassSignature): Unit = {
    val ClassSignature(id, typeParams, fields, functions, directSupertypes, sigScope, declPosOpt) = classSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for tp <- typeParams do {
      typeTypeTypeParam(tp, sigScope, declPosOpt)
    }
    for (_, fld) <- fields do {
      typeField(fld, sigScope, declPosOpt)
    }
    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypesAsInterfaces(classSig, resolutionCtx)
  }

  def typeObjectSig(objSig: ObjectSignature): Unit = {
    val ObjectSignature(id, functions, directSupertypes, sigScope, declPosOpt) = objSig

    given TypeParamsContext = TypeParamsContext.empty

    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypes(objSig, "interface", resolutionCtx)
  }

  def typeDatatypeSig(datatypeSig: DatatypeSignature): Unit = {
    val DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, sigScope, declPosOpt) = datatypeSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, sigScope, declPosOpt)
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

  private def saveType(idValue: IdValue, tpe: Type): Unit = {
    idValue.definingScope.saveType(idValue, tpe)
  }

  private def saveSmartcast(idValue: IdValue, tpe: Type, scope: Scope): Unit = {
    scope.saveType(idValue, tpe)
  }

  private def applyBranchInfo(scope: Scope, branchInfo: BranchingInfo): Unit = {
    for {
      (subject, typeIds) <- branchInfo.smartcasts
      tid <- typeIds
      tpe <- subtypingCtx.checkDowncastTarget(scope.currentTypeOf(subject), tid).asOption
    } {
      scope.saveSmartcast(subject, tpe)
    }
    for (assumption <- branchInfo.assumptions) {
      solver.assert(assumption)
      // TODO turn assumptions into smartcasts if they are inequalities
    }
  }

  private def resolveFunSig(receiver: Type, funId: FunOrVarId, posOpt: Option[Position]): (InvocationTarget, Type) = {

    def errorCase() = {
      er.reportError(s"method $funId not found in type $receiver", posOpt)
      (InvocationTarget.Unresolvable(funId), NothingType)
    }

    receiver.principalType match {
      case NamedType(typeName, typeArgs, args) =>
        resolutionCtx.resolveFunSig(typeName, funId) match {
          case FuncResolResult.Success(ownerSig, funSig) =>
            val typesSubst = instantiateTypes(typeName, funSig.typeParams, typeArgs, posOpt)
            val instantiatedRetType = funSig.retType.substitute(typesSubst, Map.empty)
            val invocationTarget = InvocationTarget.Resolved(ownerSig, funSig, instantiatedRetType)
            (invocationTarget, instantiatedRetType)
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  private def resolveFieldAccess(owner: Type, fieldId: FunOrVarId, posOpt: Option[Position]): (FieldResolutionTarget, Type) = {

    def errorCase() = {
      er.reportError(s"field $fieldId not found in type ${owner.principalType}", posOpt)
      (FieldResolutionTarget.Unresolvable(fieldId), NothingType)
    }

    owner.principalType match {
      case NamedType(typeName, typeArgs, args) =>
        resolutionCtx.resolveFieldAccess(typeName, fieldId) match {
          case FieldResolResult.Success(ownerSig, field) =>
            val typeSubst = instantiateTypes(ownerSig.id, ownerSig.typeParams, typeArgs, posOpt)
            val instantiatedFieldType = field.tpe.substitute(typeSubst, Map.empty)
            (FieldResolutionTarget.Resolved(ownerSig, fieldId, instantiatedFieldType), instantiatedFieldType)
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  private def instantiateTypes(tid: TypeIdentifier, typeParams: List[TypeParamInfo], typeArgs: List[Type], posOpt: Option[Position]): Map[TypeIdentifier, Type] = {
    if typeParams.size == typeArgs.size then typeParams.map(_.tid).zip(typeArgs).toMap
    else {
      if (typeArgs.nonEmpty) {
        er.reportError(s"wrong number of type parameters for type $tid", posOpt)
      }
      Map.from(for tp <- typeParams yield tp.tid -> typeVarsCtx.newTypeVariable(tp.tid.stringId, posOpt))
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

  // TODO maybe collect params -> args mapping for dependent typing
  private def typeArgsList(tid: TypeIdentifier, expParamsCnt: Int, args: List[Formula], currScope: Scope, posOpt: Option[Position])
                          (using TypeParamsContext): Unit = {
    if (args.size == expParamsCnt) {
      er.reportError(s"wrong number of parameters for $tid: expected $expParamsCnt, was ${args.size}", posOpt)
    }
    for (arg <- args) {
      typeFormula(arg, currScope, posOpt)
    }
  }

  private def expVariance(ambientVarianceOpt: Option[Variance], tParam: TypeParamInfo): Option[Variance] = (tParam, ambientVarianceOpt) match {
    case (tParam: TypeTypeParamInfo, Some(ambientVariance)) =>
      Some(tParam.variance * ambientVariance)
    case _ => None
  }

}
