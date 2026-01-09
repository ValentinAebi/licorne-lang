package compiler.typechecking

import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.*
import compiler.typechecking.ControlFlowInfo.TypeInfo
import compiler.typechecking.FunctionContext.TypeInfo
import compiler.typechecking.Taint.Parameters
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.*
import lang.Operators.OperatorSignature
import lang.Types.*
import lang.Types.PrimitiveType.*
import lang.Values.*
import lang.Visibility.Private

import scala.collection.mutable
import scala.compiletime.uninitialized
import scala.util.boundary


final class Typer(
                   private val er: ErrorReporter,
                   private val maxLoopTypingRetryCnt: Int = 1, // TODO add to command-line arguments
                   private val continueIfErrors: Boolean = false
                 ) extends CompilerStep[Program, (Program, TypeStore)] {

  private given Typer = this

  private given CompilationStep = TypeChecking

  private given ErrorReporter = er

  // TODO substitution of terms in types appearing as results

  override def apply(program: Program): (Program, TypeStore) = {
    val ts = new TypeStore
    program.checkDefinitions()(using this, ts, er, program.typeDeclPositions)
    checkFunctions()(using program, ts)
    if (!continueIfErrors) {
      er.displayAndTerminateIfErrors()
    }
    (program, ts)
  }

  private def checkFunctions()(using program: Program, ts: TypeStore): Unit = {
    for ((funSig, func) <- program.functions) {
      val funOwnerSig = program.resolveSignature(funSig.ownerName).get
      val (thisVal, thisType) = funSig.paramsInclThis.head
      for ((paramVal, (argType, argMarking)) <- funSig.paramsInclThis) {
        ts(paramVal) = (argType, Taint.ofParam(paramVal))
      }
      func.bodyOpt.foreach { body =>
        given funcCtx: FunctionContext = FunctionContext(program, funOwnerSig.typeParams.toMap, funSig.typeParams.toSet,
          thisVal, funSig.ownerName, expectedReturnType = funSig.retType)

        given closuresCollector: mutable.Queue[ClosureInfo] = mutable.Queue.empty

        given ambientTaint: Taint = Taint.constant

        val funcEndCtx = traverseAll(body, ControlFlowInfo.empty)
        val retTypeBase = funSig.retType.baseType
        checkReturnsIfNonVoid(retTypeBase, funcEndCtx, "method", func.posOpt)
        while (closuresCollector.nonEmpty) {
          val ClosureInfo(closureBody, closureStartCtx, closureExpRetTVar, closurePosOpt) = closuresCollector.dequeue()
          val closureEndCtx = traverseAll(closureBody, closureStartCtx)
          closureExpRetTVar.actualTypeIfResolved.foreach { expectedRetType =>
            checkReturnsIfNonVoid(expectedRetType.baseType, closureEndCtx, "closure", closurePosOpt)
          }
          if (!closureExpRetTVar.isResolved) {
            closureExpRetTVar.resolve(VoidType)
          }
        }
      }
    }
  }

  private def checkReturnsIfNonVoid(retTypeBase: BaseType, endCf: ControlFlowInfo, functionKindDescr: String, posOpt: Option[Position]) = {
    if (retTypeBase != VoidType && !endCf.hasExited) {
      reportError(s"missing return in non-$VoidType $functionKindDescr", posOpt)
    }
  }

  private def traverseAll(instructions: List[Instr], cfInfo: ControlFlowInfo)
                         (using ambientTaint: Taint, ts: TypeStore, closuresCollector: mutable.Queue[ClosureInfo], er: ErrorReporter, program: Program): ControlFlowInfo =
    instructions.foldLeft(cfInfo) { (cfInfo, instr) =>
      traverse(instr, cfInfo)
    }

  private def traverse(instr: Instr, cfIn: ControlFlowInfo)
                      (using ambientTaint: Taint, functionContext: FunctionContext, ts: TypeStore, closuresCollector: mutable.Queue[ClosureInfo], er: ErrorReporter, program: Program): ControlFlowInfo = {
    given posOpt: Option[Position] = instr.getAstNodeOpt.flatMap(_.getPosition)

    instr match {
      case SSA.Loop(cond, body, variables) =>
        // first guess of types: same as before loop
        for (LoopVarInfo(varId, beforeLoopVal, bodyStartVal, bodyEndVal, afterLoopVal) <- variables) {
          val (tpe, taint, _) = analyze(beforeLoopVal, cfIn)
          ts(bodyStartVal) = (tpe, taint)
        }
        er.pushSpeculationLayer()
        var typingAttemptsCnt = 0
        var typingSucceeded = false
        var bodyStartCf: ControlFlowInfo = uninitialized
        var bodyEndCf: ControlFlowInfo = uninitialized
        while (!typingSucceeded && typingAttemptsCnt < maxLoopTypingRetryCnt) {
          val (condType, condTaint, cfAfterCond) = analyze(cond, cfIn)
          bodyStartCf = cfAfterCond
          enforceBaseSubtypingConstraint(condType, BoolType)(using "loop condition")
          val (bodyInfos, afterLoopInfos) = extractTypeInfos(cond)
          bodyEndCf = traverseAll(body, bodyStartCf)
          for (LoopVarInfo(varId, beforeLoopVal, bodyStartVal, bodyEndVal, afterLoopVal) <- variables) {
            // check if the guessed types work; if they do not, retry
            val (typeAtEndOfBody, taintAtEndOfBody, _) = analyze(bodyEndVal, bodyEndCf)
            val (typeAtBeginningOfBody, taintAtBeginningOfBody) = ts.query(bodyStartVal).get
            val typeIsValid = enforceBaseSubtypingConstraint(typeAtEndOfBody.baseType, typeAtBeginningOfBody.baseType)(using s"base type of $varId at the end of loop body")
            if (!typeIsValid) {
              ts.widenType(bodyStartVal, typeAtEndOfBody)
            }
            val taintIsValid = taintAtEndOfBody.isCoveredBy(taintAtBeginningOfBody)
            if (!taintIsValid) {
              ts.widenTaint(bodyStartVal, taintAtEndOfBody)
            }
            typingSucceeded = typeIsValid && taintIsValid
          }
          typingAttemptsCnt += 1
        }
        er.commitSpeculation()
        for (LoopVarInfo(varId, beforeLoopVal, bodyStartVal, bodyEndVal, afterLoopVal) <- variables) {
          val (bodyStartType, bodyStartTaint, _) = analyze(bodyStartVal, bodyStartCf)
          val (bodyEndType, bodyEndTaint, _) = analyze(bodyEndVal, bodyEndCf)
          ts(afterLoopVal) = (Types.join(bodyStartType, bodyEndType), bodyStartTaint + bodyEndTaint)
        }
        bodyStartCf.merged(bodyEndCf)
      case SSA.Disjunction(cond, thenBr, elseBr, postMerges) =>
        val condType = analyze(cond)(using tcCtx)
        enforceBaseSubtypingConstraint(condType, BoolType)(using "condition")
        val (thenInfos, elseInfos) = extractTypeInfos(cond)
        val thenStartCtx = tcCtx.withTypeInfoRefined(thenInfos)
        val thenEndCtx = traverseAll(thenBr, thenStartCtx)
        val elseStartCtx = tcCtx.withTypeInfoRefined(elseInfos)
        val elseEndCtx = traverseAll(elseBr, elseStartCtx)
        val ctxAfter =
          if thenEndCtx.alwaysExitsFlag then elseEndCtx
          else if elseEndCtx.alwaysExitsFlag then thenEndCtx
          else tcCtx
        traverseAll(postMerges, ctxAfter)
      case SSA.Phi(assignedValue, inValues) =>
        ts(assignedValue) = Types.join(inValues.map(analyze(_)(using tcCtx)))
        tcCtx
      case SSA.Assignment(assignedValue, rhs) =>
        val rhsType = analyze(rhs)(using tcCtx)
        ts(assignedValue) = rhsType
        tcCtx
      case SSA.Instantiate(assignedValue, classOrRecordName, typeArgs, initialization) =>
        typeArgs.foreach(tcCtx.checkType(_, None, posOpt))
        program.resolveSignatureAs[RuntimeTypeSignature & UserInstantiable](classOrRecordName) match {
          case None =>
            reportError(s"instantiable type not found: $classOrRecordName", posOpt)
          case Some(sig) =>
            val typeParams = sig.typeParams.map(_._1)
            generateTypeParamsMapping(typeParams, typeArgs, posOpt, "new", reportIfLengthMismatch = true) match {
              case Some(typeParamsMapping) =>
                ts(assignedValue) = NamedType(classOrRecordName, typeParams.map(typeParamsMapping.apply), List.empty)
                val initializedFields = initialization.flatMap {
                  case FieldWrite(owner, fieldName, rhs) => Some(fieldName)
                  case _ => None
                }.toSet
                val requiredFields = sig.fields.keySet
                val missingFields = requiredFields.diff(initializedFields)
                if (missingFields.nonEmpty) {
                  reportError(s"field(s) ${missingFields.mkString(", ")} have not been initialized", posOpt)
                }
                traverseAll(initialization, tcCtx)
              case None =>
                // still report the errors we can
                initialization.foreach {
                  case FieldWrite(owner, fieldName, rhs) =>
                    analyze(rhs)(using tcCtx)
                  case _ => ()
                }
            }
        }
        tcCtx
      case SSA.Cast(assignedValue, inValue, targetType) =>
        val inValueType = analyze(inValue)(using tcCtx)
        import DowncastTargetCheckResult.*
        checkDowncastTarget(inValueType, targetType) match {
          case CanDowncast(tpe) =>
            ts(assignedValue) = tpe
          case CannotDowncast(reason) =>
            reportError(s"illegal cast: $reason", instr.getAstNodeOpt.flatMap(_.getPosition))
        }
        tcCtx.withTypeInfoRefined(Set(TypeInfo(inValue, targetType, Set(targetType), Set.empty)))
      case SSA.Conversion(assignedValue, inValue, targetType) =>
        val inValueType = analyze(inValue)(using tcCtx)
        inValueType match {
          case inValueType: BaseType if inValueType != targetType && TypeConversion.conversionFor(inValueType, targetType).isEmpty =>
            reportError(s"impossible conversion: $inValueType to $targetType", posOpt)
          case _ => ()
        }
        tcCtx
      case SSA.StaticTypeAssert(value, tpe) =>
        tcCtx.checkType(tpe, None, posOpt)
        enforceBaseSubtypingConstraint(analyze(value)(using tcCtx), tpe)(using "type ascription")
        tcCtx
      case SSA.StaticAssert(formula) =>
        val formulaType = analyze(formula)(using tcCtx)
        enforceBaseSubtypingConstraint(formulaType, BoolType)(using "assertion")
        tcCtx
      case SSA.FieldWrite(owner, fieldName, rhs) =>
        val ownerType = analyze(owner)(using tcCtx)
        val rhsType = analyze(rhs)(using tcCtx)
        checkFieldAndReturnTypeAndTaint(ownerType.baseType, fieldName, posOpt,
          checkIsReassignable = false, ownerThatMustBeThis = None)(using tcCtx).foreach { fieldType =>
          enforceBaseSubtypingConstraint(rhsType, fieldType)(using "field assignment")
        }
        tcCtx
      case SSA.Return(None) =>
        if (tcCtx.expectedReturnType.baseType != VoidType) {
          reportError(s"non-$VoidType method should return a value", posOpt)
        }
        tcCtx.withAlwaysExitsFlagRaised
      case SSA.Return(Some(retVal)) =>
        // TODO also enforce marking constraints
        val retType = analyze(retVal)(using tcCtx)
        enforceBaseSubtypingConstraint(retType, tcCtx.expectedReturnType)(using "return value")
        if (tcCtx.expectedReturnType == VoidType) {
          reportError(s"$VoidType method cannot return a value", posOpt)
        }
        tcCtx.withAlwaysExitsFlagRaised
      case SSA.Panic(msg) =>
        val msgType = analyze(msg)(using tcCtx)
        enforceBaseSubtypingConstraint(msgType, StringType)(using "panic message")
        tcCtx.withAlwaysExitsFlagRaised
      case SSA.Evaluate(formula) =>
        val tpe = analyze(formula)(using tcCtx)
        if tpe.baseType == NothingType then tcCtx.withAlwaysExitsFlagRaised else tcCtx
      case SSA.DynamicAssert(formula) => ???
      case SSA.LocalDecl(localId, tpe) =>
        tcCtx.checkType(tpe, None, posOpt)
        tcCtx
      case SSA.ClosureCreation(assignedValue, params, body) =>
        for ((paramId, paramType) <- params) {
          ts(paramId) = paramType
        }
        val resultTypeVar = new TypeVariable(s"${assignedValue}_res")
        ts(assignedValue) = ClosureType(params.map(_._2), resultTypeVar)
        closuresCollector.enqueue(ClosureInfo(body, tcCtx.copyForClosureBody(resultTypeVar), resultTypeVar, posOpt))
        tcCtx
    }
  }

  private[typechecking] def analyze(formula: Formula, cfIn: ControlFlowInfo)
                                   (using ambientTaint: Taint, funCtx: FunctionContext, ts: TypeStore, er: ErrorReporter, program: Program): (Type, Taint, ControlFlowInfo) = {
    val posOpt =
      if program.formulaPositions.containsKey(formula)
      then Some(program.formulaPositions.get(formula))
      else None
    val (outTypeRaw: Type, outTaintRaw: Taint, outCtx: ControlFlowInfo) = formula match {
      case idValue: IdValue =>
        val (tpe, taint) = ts.query(idValue) match {
          case Some((regularType, taint)) =>
            smartCastsCtx.inferredTypeFor(idValue) match {
              case Some(typeId) =>
                import DowncastTargetCheckResult.*
                val morePreciseType = checkDowncastTarget(regularType, typeId) match {
                  case CanDowncast(tpe) => tpe
                  case CannotDowncast(reason) => regularType
                }
                (morePreciseType, taint)
              case _ => (regularType, taint)
            }
          // typically, the type of a missing value because of an illegal construct
          case _ => (NothingType, Taint.constant)
        }
        (tpe, taint, cfIn)
      case True | False => (BoolType, Taint.constant, cfIn)
      case NullPtr => (NullType, Taint.constant, cfIn)
      case IntConstant(value) => (IntType, Taint.constant, cfIn)
      case DoubleConstant(value) => (DoubleType, Taint.constant, cfIn)
      case StringConstant(value) => (StringType, Taint.constant, cfIn)
      case Equal(lhs, rhs) =>
        val (lhsType, lhsTaint, cfBetweenMembers) = analyze(lhs, cfIn)
        val (rhsType, rhsTaint, cfOut) = analyze(rhs, cfBetweenMembers)
        if (areProvablyDisjointUnlessNull(lhsType.baseType, rhsType.baseType)) {
          reportError(s"illegal equality test: ${lhsType.baseType} and ${rhsType.baseType} are incompatible types", posOpt)
        }
        (BoolType, lhsTaint + rhsTaint, cfOut)
      case op: BinOp =>
        val (lhsTypeRaw, lhsTaint, cfBetweenMembers) = analyze(op.lhs, cfIn)
        val lhsTypeDesBase = program.desugarType(lhsTypeRaw).baseType
        val (lhsTrueInfos, lhsFalseInfos) = extractTypeInfos(op.lhs)
        val rhsAmbientTaint = if isShortcutBinop(op) then ambientTaint + lhsTaint else ambientTaint
        val rhsSmartcastsCtx = op.operator match {
          case Operator.And => smartCastsCtx.refined(lhsTrueInfos)
          case Operator.Or => smartCastsCtx.refined(lhsFalseInfos)
          case _ => smartCastsCtx
        }
        val (rhsTypeRaw, rhsTaint, cfOut) = analyze(op.rhs, cfBetweenMembers)(using rhsAmbientTaint, rhsSmartcastsCtx)
        val rhsTypeDesBase = program.desugarType(rhsTypeRaw).baseType
        val tpe = if (lhsTypeDesBase == NothingType || rhsTypeDesBase == NothingType) {
          NothingType
        } else {
          val candidateOperators = Operators.binaryOperators.filter { opSig =>
            opSig.op == op.operator
              && lhsTypeDesBase.trivialBaseSubtypeOf(opSig.leftOperandType.baseType)
              && rhsTypeDesBase.baseType.trivialBaseSubtypeOf(opSig.rightOperandType.baseType)
          }
          resolveCandidatesOp(candidateOperators, op.operator, s"operand types $lhsTypeDesBase and $rhsTypeDesBase", posOpt) match {
            case Some(opSig) =>
              enforceBaseSubtypingConstraint(lhsTypeRaw, opSig.leftOperandType)(using "operand", posOpt)
              enforceBaseSubtypingConstraint(rhsTypeRaw, opSig.rightOperandType)(using "operand", posOpt)
              opSig.retType
            case None => NothingType
          }
        }
        (tpe, lhsTaint + rhsTaint, cfOut)
      case op: UnaryOp =>
        val (operandTypeRaw, operandTaint, cfOut) = analyze(op.operand, cfIn)
        val operandTypeDesBase = program.desugarType(operandTypeRaw).baseType
        val tpe = if (operandTypeDesBase == NothingType) {
          NothingType
        } else {
          val candidatesOperators = Operators.unaryOperators.filter { opSig =>
            opSig.op == op.operator && operandTypeDesBase.trivialBaseSubtypeOf(opSig.operandType.baseType)
          }
          resolveCandidatesOp(candidatesOperators, op.operator, s"operand type $operandTypeDesBase", posOpt) match {
            case Some(opSig) =>
              enforceBaseSubtypingConstraint(operandTypeRaw, opSig.operandType)(using "operand", posOpt)
              opSig.retType
            case None => NothingType
          }
        }
        (tpe, operandTaint, cfOut)
      case Call(receiverArg, funId, typeArgs, args) =>
        val (receiverArgType, receiverArgTaint, cfAfterReceiver) = analyze(receiverArg, cfIn)
        typeArgs.foreach(funCtx.checkType(_, None, posOpt))
        forceComputeJoins(program.desugarType(receiverArgType).baseType) match {
          case Some(Types.NamedType(receiverTypeName, receiverTypeArgs, receiverArgs)) =>
            assert(receiverArgs.isEmpty)
            program.resolveSignatureAs[RuntimeTypeSignature](receiverTypeName) match {
              case None =>
                reportError(s"type not found: $receiverTypeName", posOpt)
                (NothingType, Taint.constant, cfAfterReceiver)
              case Some(_: Unencapsulated) =>
                reportMethodNotFoundInType(receiverArgType.baseType, funId, posOpt)
                (NothingType, Taint.constant, cfAfterReceiver)
              case Some(receiverTypeSig: Encapsulated) =>
                findMethod(receiverTypeName, funId) match {
                  case None =>
                    reportMethodNotFoundInType(receiverArgType.baseType, funId, posOpt)
                    (NothingType, Taint.constant, cfAfterReceiver)
                  case Some(funSig) =>
                    if (funSig.visibility == Private && funSig.ownerName != funCtx.ownerId) {
                      reportError(s"$Private method $funId cannot be accessed from outside its defining class ${funSig.ownerName}", posOpt)
                    }
                    val argsSizeMatch = args.size == funSig.paramsInclThis.size - 1
                    if (!argsSizeMatch) {
                      reportError(s"wrong number of arguments for method $funId: expected ${funSig.paramsInclThis.size - 1}, was ${args.size}", posOpt)
                    }
                    val funcTParamsSubstOpt = generateTypeParamsMapping(funSig.typeParams, typeArgs, posOpt, s"$funId", reportIfLengthMismatch = true)
                    val upcastRecvTParamsSubstOpt = generateTypeParamsMapping(receiverTypeSig.typeParams.map(_._1), receiverTypeArgs, posOpt, "recverr", reportIfLengthMismatch = false)
                    val subToSuperSubstOpt = program.subToSuperSubst(receiverTypeName, funSig.ownerName)
                    val subst = substComposition(subToSuperSubstOpt, upcastRecvTParamsSubstOpt).getOrElse(Map.empty) ++ funcTParamsSubstOpt.getOrElse(Map.empty)
                    val argsSubst = mutable.Map.empty[IdValue, Value]
                    receiverArg match {
                      case receiver: Value =>
                        argsSubst(funSig.receiverVal) = receiver
                      case _ => ()
                    }
                    var aggregatedTaint = if funSig.retIsMarked then Taint.Unstable else Taint.constant
                    if (funSig.receiverMarking == ParamMarking.NotMarked) {
                      aggregatedTaint += receiverArgTaint
                    }
                    var currCf = cfAfterReceiver
                    if (argsSizeMatch) {
                      for (((paramVal, (paramTypeRaw, paramMarking)), arg) <- funSig.paramsInclThis.tail zip args) {
                        val (argType, argTaint, cfAfterParam) = analyze(arg, currCf)
                        val paramTypeSubst = paramTypeRaw.substitute(subst, argsSubst.toMap)
                        enforceBaseSubtypingConstraint(argType, paramTypeSubst)(using "method argument", posOpt)
                        arg match {
                          case arg: Value =>
                            argsSubst(paramVal) = arg
                          case _ => ()
                        }
                        if (paramMarking == ParamMarking.NotMarked) {
                          aggregatedTaint += argTaint
                        }
                        currCf = cfAfterParam
                      }
                    }
                    (funSig.retType.substitute(subst, argsSubst.toMap), aggregatedTaint, currCf)
                }
            }
          case None =>
            reportMethodNotFoundInType(receiverArgType.baseType, funId, posOpt)
            (NothingType, Taint.constant, cfAfterReceiver)
        }
      case ClosureInvocation(closure, args) =>
        val (closureType, closureValTaint, cfAfterClosureEval) = analyze(closure, cfIn)
        val argTypesB = List.newBuilder[Type]
        var aggregatedTaint = closureValTaint
        var currCf = cfAfterClosureEval
        for (arg <- args) {
          val (argType, argTaint, cfAfterArgEval) = analyze(arg, currCf)
          argTypesB.addOne(argType)
          aggregatedTaint += argTaint
          currCf = cfAfterArgEval
        }
        val tpe = closureType match {
          case ClosureType(paramTypes, resultType) =>
            for ((paramType, argType) <- paramTypes.zip(argTypesB.result())) {
              enforceBaseSubtypingConstraint(argType, paramType)(using "closure argument", posOpt)
            }
            resultType
          case _ =>
            reportError("illegal invocation: not a closure", posOpt)
        }
        // FIXME make sure the way taints are handled in closures is correct (we probably need to prevent closures from having a non-deterministic return value)
        (tpe, aggregatedTaint, currCf)
      case Select(owner, fieldName) =>
        val (ownerType, ownerTaint, cfAfterOwnerEval) = analyze(owner, cfIn)
        val (tpe, taint) = if ownerType.baseType == NothingType then (NothingType, Taint.constant)
        else checkFieldAndReturnTypeAndTaint(funCtx.thisVal, ownerType.baseType, ownerTaint, fieldName, posOpt, checkIsReassignable = false, Some(owner))
          .getOrElse((NothingType, Taint.constant))
        (tpe, taint, cfAfterOwnerEval)
      case HasType(formula, tpe) =>
        import DowncastTargetCheckResult.*
        val (formulaType, formulaTaint, cfAfterFormulaEval) = analyze(formula, cfIn)
        checkDowncastTarget(formulaType, tpe) match {
          case CanDowncast(tpe) => ()
          case CannotDowncast(reason) =>
            reportError(s"illegal type test: $reason", posOpt)
        }
        (BoolType, formulaTaint, cfAfterFormulaEval)
    }
    (outTypeRaw.withTypeVarsExpanded, outTaintRaw + ambientTaint, outCtx)
  }

  /**
   * @return (info when cond, info when !cond)
   */
  private def extractTypeInfos(cond: Formula)(using ts: TypeStore): (Set[TypeInfo], Set[TypeInfo]) = cond match {
    case And(lhs, rhs) =>
      val (infoWhenLhs, infoWhenNotLhs) = extractTypeInfos(lhs)
      val (infoWhenRhs, infoWhenNotRhs) = extractTypeInfos(rhs)
      (infoWhenLhs ++ infoWhenRhs, Set.empty)
    case Or(lhs, rhs) =>
      val (infoWhenLhs, infoWhenNotLhs) = extractTypeInfos(lhs)
      val (infoWhenRhs, infoWhenNotRhs) = extractTypeInfos(rhs)
      (Set.empty, infoWhenNotLhs ++ infoWhenNotRhs)
    case Not(operand) =>
      val (infoWhenOperand, infoWhenNotOperand) = extractTypeInfos(operand)
      (infoWhenNotOperand, infoWhenOperand)
    case HasType(idValue: IdValue, testedType) =>
      ts.typeQuery(idValue) match {
        case Some(NamedType(knownType, _, Nil)) =>
          (Set(TypeInfo(idValue, knownType, Set(testedType), Set.empty)),
            Set(TypeInfo(idValue, knownType, Set.empty, Set(testedType))))
        case _ => (Set.empty, Set.empty)
      }
    case _ => (Set.empty, Set.empty)
  }

  private def findMethod(receiverTypeId: TypeIdentifier, mthId: FunOrVarId)(using program: Program): Option[FunctionSignature] = {

    def searchFrom(receiverId: TypeIdentifier): Option[FunctionSignature] = {
      program.resolveSignatureAs[Encapsulated](receiverId) match {
        case None => None
        case Some(tSig) =>
          tSig.functions.get(mthId) match {
            case someFunc@Some(_) => someFunc
            case None =>
              tSig.directSupertypes.foldLeft[Option[FunctionSignature]](None) {
                case (result@Some(_), _) => result
                case (None, superT) => searchFrom(superT.typeName)
              }
          }
      }
    }

    searchFrom(receiverTypeId)
  }

  private def areProvablyDisjointUnlessNull(type1: BaseType, type2: BaseType): Boolean = (type1, type2) match {
    case (type1: Concrete, type2: Concrete) if type1 != type2 => true
    case _ => false
  }

  private[typechecking] def generateTypeParamsMapping(typeParams: List[TypeIdentifier], typeArgs: List[Type], posOpt: Option[Position], contextDescrForTypeVar: String, reportIfLengthMismatch: Boolean): Option[Map[TypeIdentifier, Type]] = {
    if (typeArgs.nonEmpty && typeArgs.size != typeParams.size) {
      if (reportIfLengthMismatch) {
        reportError(s"wrong number of type arguments: expected ${typeParams.size}, was ${typeArgs.size}", posOpt)
      }
      None
    } else if (typeArgs.isEmpty && typeParams.nonEmpty) Some {
      typeParams.map(tp => tp -> new TypeVariable(s"${contextDescrForTypeVar}_$tp")).toMap
    } else Some {
      typeParams.zip(typeArgs).toMap
    }
  }

  private def forceComputeJoins(tpe: BaseType)(using program: Program): Option[NamedType] = tpe match {
    case namedType: NamedType => Some(namedType)
    case _: BaseUnionType => boundary {

      def extractTypeIds(tpe: BaseType): Set[TypeIdentifier] = tpe match {
        case NamedType(tid, _, _) => Set(tid)
        case BaseUnionType(types) => types.flatMap(extractTypeIds)
        case _ => boundary.break(None)
      }

      val allTypeIds = extractTypeIds(tpe)
      val commonDirectSupertypes = allTypeIds.map { tid =>
        val sig = program.resolveSignatureAs[RuntimeTypeSignature](tid).getOrElse {
          boundary.break(None)
        }
        sig.directSupertypes.toSet
      }.reduce(_.intersect(_))

      val possibleSubstitutions = {
        for {
          NamedType(superTypeId, _, _) <- commonDirectSupertypes
          subst <- program.subToSuperSubst(allTypeIds.head, superTypeId)
          if allTypeIds.tail.forall {
            program.subToSuperSubst(_, superTypeId).contains(subst)
          }
        } yield (superTypeId, subst)
      }
      if (possibleSubstitutions.size == 1) {
        val (superTypeId, subst) = possibleSubstitutions.head
        program.resolveSignatureAs[RuntimeTypeSignature](superTypeId).flatMap { sig =>
          sig.toType(subst, Map.empty) match {
            case namedType: NamedType => Some(namedType)
            case _ => None
          }
        }
      } else None
    }
    case _ => None
  }

  private def substComposition(firstSubstOpt: Option[Map[TypeIdentifier, Type]], secondSubstOpt: Option[Map[TypeIdentifier, Type]]): Option[Map[TypeIdentifier, Type]] = (firstSubstOpt, secondSubstOpt) match {
    case (Some(firstSubst), Some(secondSubst)) => Some(substComposition(firstSubst, secondSubst))
    case (firstSubstOpt@Some(_), None) => firstSubstOpt
    case (None, secondSubstOpt@Some(_)) => secondSubstOpt
    case (None, None) => None
  }

  private def substComposition(firstSubst: Map[TypeIdentifier, Type], secondSubst: Map[TypeIdentifier, Type]): Map[TypeIdentifier, Type] = {
    for ((tParam, tArg) <- firstSubst) yield {
      tParam -> (tArg match {
        case NamedType(tid, Nil, Nil) =>
          secondSubst.getOrElse(tid, tArg)
        case _ => tArg
      })
    }
  }

  private def checkFieldAndReturnTypeAndTaint(
                                               ownerVal: IdValue,
                                               ownerType: BaseType,
                                               ownerTaint: Taint,
                                               fieldName: FunOrVarId,
                                               posOpt: Option[Position],
                                               checkIsReassignable: Boolean,
                                               ownerThatMustBeThis: Option[Formula]
                                             )(using er: ErrorReporter, program: Program): Option[(Type, Taint)] = {
    forceComputeJoins(program.desugarType(ownerType).baseType) match {
      case Some(Types.NamedType(typeName, typeArgs, args)) =>

        def subst(sig: RuntimeTypeSignature, tpe: Type): Type = {
          val subst = sig.typeParams.map(_._1).zip(typeArgs).toMap
          tpe.substitute(subst, Map.empty)
        }

        def computeTaint(fieldIsStable: Boolean): Taint =
          if fieldIsStable then ownerTaint else Taint.Unstable

        program.resolveSignatureAs[RuntimeTypeSignature](typeName).flatMap {
          case recordSig: RecordSignature =>
            recordSig.fields.get(fieldName) match {
              case Some(field) => Some((subst(recordSig, field.tpe), computeTaint(field.isStable)))
              case None =>
                reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
            }
          case classSig: ClassSignature if ownerThatMustBeThis.forall(_ == ownerVal) =>
            classSig.fields.get(fieldName) match {
              case None =>
                reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
              case Some(field) =>
                if (checkIsReassignable && field.isStable) {
                  reportError(s"field $fieldName is not reassignable", posOpt)
                }
                Some((subst(classSig, field.tpe), computeTaint(field.isStable)))
            }
          case _: ClassSignature =>
            reportError(s"field $fieldName not found or not accessible in $typeName; note that class fields are always private and should be accessed from the outside through getters only", posOpt)
            None
          case _ =>
            reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
        }
      case None =>
        val remarkAboutUnion = mkUnionReceiverRemark(ownerType)
        reportError(s"access to field $fieldName: cannot resolve receiver type$remarkAboutUnion", posOpt)
        None
    }
  }

  extension (targetId: TypeIdentifier) private def isValidDowncastTargetForType(tpe: Type)(using program: Program): Boolean =
    checkDowncastTarget(tpe, targetId).isInstanceOf[DowncastTargetCheckResult.CanDowncast]

  private enum DowncastTargetCheckResult {
    case CanDowncast(tpe: Type)
    case CannotDowncast(reason: String)
  }

  private def checkDowncastTarget(originalType: Type, targetId: TypeIdentifier)
                                 (using program: Program): DowncastTargetCheckResult = {
    import DowncastTargetCheckResult.*
    originalType.baseType match {
      case NamedType(originId, originTypeArgs, Nil) =>
        program.resolveSignatureAs[RuntimeTypeSignature](targetId) match {
          case None =>
            CannotDowncast(s"type $targetId not found")
          case Some(targetSig) =>
            program.subToSuperSubst(targetId, originId) match {
              case None => CannotDowncast(s"$targetId does not subtype $originId")
              case Some(targetToOrigSubst) =>
                val origSig = program.resolveSignatureAs[RuntimeTypeSignature](originId).get
                val siteSubst = origSig.typeParams.map(_._1).zip(originTypeArgs).toMap
                val newTargetSubstB = Map.newBuilder[TypeIdentifier, Type]
                for ((tInOrig, tInTarget) <- targetToOrigSubst) {
                  tInTarget match {
                    case NamedType(tInTarget, Nil, Nil) =>
                      for {
                        varianceInOrig <- origSig.varianceOf(tInOrig)
                        varianceInTarget <- targetSig.varianceOf(tInTarget)
                        if varianceInOrig == varianceInTarget
                      } do {
                        newTargetSubstB.addOne(tInTarget -> siteSubst.apply(tInOrig))
                      }
                    case _ => ()
                  }
                }
                val newTargetSubst = newTargetSubstB.result()
                val uncoveredTypeParams = targetSig.typeParams.map(_._1).toSet -- newTargetSubst.keySet
                if (uncoveredTypeParams.isEmpty) {
                  CanDowncast(targetSig.toType(newTargetSubst, Map.empty))
                } else {
                  CannotDowncast(s"cannot infer type argument(s) for type parameter(s) ${uncoveredTypeParams.mkString(", ")} of tested type $targetId")
                }
            }
        }
      case _ =>
        CannotDowncast(s"tested type ${originalType.baseType} is unresolved or primitive")
    }
  }

  private def reportMethodNotFoundInType(receiverType: BaseType, funId: FunOrVarId, posOpt: Option[Position])(using Program): Unit = {
    val receiverTypeDescr = mkReceiverTypeDescr(receiverType)
    val remarkAboutUnion = mkUnionReceiverRemark(receiverType)
    reportError(s"method $funId not found in $receiverTypeDescr$remarkAboutUnion", posOpt)
  }

  private def mkUnionReceiverRemark(receiverType: BaseType): String = {
    receiverType match {
      case BaseUnionType(types) => ", you may want to explicitize the type of the receiver using a type ascription"
      case _ => ""
    }
  }

  private def reportFieldNotFoundInType(receiverType: BaseType, fieldId: FunOrVarId, posOpt: Option[Position])
                                       (using Program): None.type = {
    val receiverTypeDescr = mkReceiverTypeDescr(receiverType)
    reportError(s"field $fieldId not found in $receiverTypeDescr", posOpt)
    None
  }

  private def mkReceiverTypeDescr(receiverType: BaseType)(using program: Program): String = {
    val desugaredReceiverType = program.desugarType(receiverType)
    desugaredReceiverType.toString + (if desugaredReceiverType == receiverType then "" else s"( = $desugaredReceiverType)")
  }

  private def resolveCandidatesOp[S <: OperatorSignature](candidateOperators: List[S], op: Operator, operandsDescr: String, posOpt: Option[Position]): Option[S] = {
    candidateOperators match {
      case Nil =>
        reportError(s"no operator $op found for $operandsDescr", posOpt)
        None
      case List(opSig) => Some(opSig)
      case candidates =>
        reportError(s"more than one operators $op found for $operandsDescr: " +
          "candidates are " + candidates.mkString(", "), posOpt)
        None
    }
  }

  private def isShortcutBinop(op: BinOp): Boolean = op match {
    case And(_, _) | Or(_, _) => true
    case _ => false
  }

  private def reportError(msg: String, posOpt: Option[Position]): NothingType.type = {
    er.report(Err(TypeChecking, msg, posOpt))
    NothingType
  }

  private case class ClosureInfo(body: List[Instr], cf: ControlFlowInfo, expectedRetTypeVar: TypeVariable, posOpt: Option[Position])

}
