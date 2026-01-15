package compiler.typechecking

import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.*
import compiler.typechecking.ControlFlowInfo.TypeInfo
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.*
import lang.Operators.OperatorSignature
import lang.Types.*
import lang.Types.PrimitiveType.*
import lang.Values.*
import lang.Visibility.Private

import scala.collection.mutable
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
      for ((paramVal, argType) <- funSig.paramsInclThis) {
        ts(paramVal) = argType
      }
      func.bodyOpt.foreach { body =>
        given funcCtx: FunctionContext = FunctionContext(program, funOwnerSig.typeParams.toMap, funSig.typeParams.toSet,
          thisVal, funSig.ownerName, expectedReturnType = funSig.retType)

        given closuresCollector: mutable.Queue[ClosureInfo] = mutable.Queue.empty

        val funcEndCtx = traverseAll(body, ControlFlowInfo.empty)
        val retTypeBase = funSig.retType.baseType
        checkReturnsIfNonUnit(retTypeBase, funcEndCtx, "method", func.posOpt)
        while (closuresCollector.nonEmpty) {
          val ClosureInfo(closureBody, closureCtx, cfStartInfo, closureExpRetTVar, closurePosOpt) = closuresCollector.dequeue()
          val closureEndCtx = traverseAll(closureBody, cfStartInfo)(using closureCtx)
          closureExpRetTVar.actualTypeIfResolved.foreach { expectedRetType =>
            checkReturnsIfNonUnit(expectedRetType.baseType, closureEndCtx, "closure", closurePosOpt)
          }
          if (!closureExpRetTVar.isResolved) {
            closureExpRetTVar.resolve(UnitType)
          }
        }
      }
    }
  }

  private def checkReturnsIfNonUnit(retTypeBase: BaseType, endCf: ControlFlowInfo, functionKindDescr: String, posOpt: Option[Position]): Unit = {
    if (retTypeBase != UnitType && !endCf.hasExited) {
      reportError(s"missing return in non-$UnitType $functionKindDescr", posOpt)
    }
  }

  private def traverseAll(instructions: List[Instr], cfInfo: ControlFlowInfo)
                         (using FunctionContext, TypeStore, mutable.Queue[ClosureInfo], ErrorReporter, Program): ControlFlowInfo =
    instructions.foldLeft(cfInfo) { (cfInfo, instr) =>
      traverse(instr, cfInfo)
    }

  private def traverse(instr: Instr, cfIn: ControlFlowInfo)
                      (using funCtx: FunctionContext, ts: TypeStore, closuresCollector: mutable.Queue[ClosureInfo], er: ErrorReporter, program: Program): ControlFlowInfo = {
    given posOpt: Option[Position] = instr.getAstNodeOpt.flatMap(_.getPosition)

    instr match {
      case SSA.Loop(cond, body, variables) => boundary {
        er.pushSpeculationLayer()
        var typingAttemptsCnt = 0
        var typingSucceeded = false
        var afterCondCf: ControlFlowInfo = ControlFlowInfo.empty
        var infoIfCondFalse = Set.empty[TypeInfo]
        while (!typingSucceeded && typingAttemptsCnt < maxLoopTypingRetryCnt) {
          for (LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- variables) {
            val beforeLoopType = analyzeIdVal(beforeLoopVal, cfIn)
            ts(condVal) = ts.typeOfOpt(bodyLastVal) match {
              case Some(bodyEndType) => Types.join(beforeLoopType, bodyEndType)
              case None => beforeLoopType
            }
          }
          val (condType, cfAfterCond) = analyze(cond, cfIn)
          val (infoIfCondTrue, _infoIfCondFalse) = extractTypeInfos(cond)
          infoIfCondFalse = _infoIfCondFalse
          if (cfAfterCond.hasExited) {
            reportError("condition never terminates", posOpt)
            boundary.break(cfIn)
          }
          afterCondCf = cfAfterCond
          enforceBaseSubtypingConstraint(condType, BoolType)(using "loop condition")
          val bodyEndCf = traverseAll(body, cfAfterCond.refined(infoIfCondTrue))
          for (LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- variables) {
            // check if the guessed types work; if they do not, retry
            val typeInCond = analyzeIdVal(condVal, cfIn)
            val bodyEndType = analyzeIdVal(condVal, bodyEndCf)
            val typeIsValid = enforceBaseSubtypingConstraint(bodyEndType.baseType, typeInCond.baseType)(using s"base type of $varId at the end of loop body")
            if (!typeIsValid) {
              ts.widenType(condVal, bodyEndType)
            }
            typingSucceeded = typeIsValid
          }
          typingAttemptsCnt += 1
        }
        er.commitSpeculation()
        afterCondCf.refined(infoIfCondFalse)
      }
      case SSA.Disjunction(cond, thenBr, elseBr, postMerges) =>
        val (condType, cfAfterCond) = analyze(cond, cfIn)
        enforceBaseSubtypingConstraint(condType, BoolType)(using "condition")
        val (thenInfos, elseInfos) = extractTypeInfos(cond)
        val thenStartCtx = cfAfterCond.refined(thenInfos)
        val thenEndCf = traverseAll(thenBr, thenStartCtx)
        val elseStartCf = cfAfterCond.refined(elseInfos)
        val elseEndCf = traverseAll(elseBr, elseStartCf)
        val cfAfterMerge = thenEndCf.merged(elseEndCf)
        traverseAll(postMerges, cfAfterMerge)
      case SSA.Phi(assignedValue, inValues) =>
        ts(assignedValue) = Types.join(inValues.map(analyzeIdVal(_, cfIn)))
        cfIn
      case SSA.Assignment(assignedValue, rhs) =>
        val (rhsType, cfAfterFormulaEval) = analyze(rhs, cfIn)
        ts(assignedValue) = rhsType
        cfAfterFormulaEval
      case SSA.Instantiate(assignedValue, classOrRecordName, typeArgs, initialization) =>
        typeArgs.foreach(funCtx.checkType(_, None, posOpt))
        program.resolveSignatureAs[RuntimeTypeSignature & UserInstantiable](classOrRecordName) match {
          case None =>
            reportError(s"instantiable type not found: $classOrRecordName", posOpt)
            cfIn
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
                traverseAll(initialization, cfIn)
              case None =>
                // still report the errors we can
                var cf = cfIn
                for (init <- initialization) {
                  init match {
                    case FieldWrite(owner, fieldName, rhs) =>
                      cf = analyze(rhs, cf)._2
                    case _ => ()
                  }
                }
                cf
            }
        }
      case SSA.Cast(castValue, targetType) =>
        val inValueType = analyzeIdVal(castValue, cfIn)
        import DowncastTargetCheckResult.*
        checkDowncastTarget(inValueType, targetType) match {
          case CanDowncast(tpe) =>
            ts(castValue) = tpe
          case CannotDowncast(reason) =>
            reportError(s"illegal cast: $reason", instr.getAstNodeOpt.flatMap(_.getPosition))
        }
        cfIn.refined(Set(TypeInfo(castValue, targetType, List(targetType), List.empty)))
      case SSA.Conversion(assignedValue, inValue, targetType) =>
        val inValueType = analyzeIdVal(inValue, cfIn)
        inValueType match {
          case inValueType: BaseType if inValueType != targetType && TypeConversion.conversionFor(inValueType, targetType).isEmpty =>
            reportError(s"impossible conversion: $inValueType to $targetType", posOpt)
          case _ => ()
        }
        cfIn
      case SSA.StaticTypeAssert(value, tpe) =>
        funCtx.checkType(tpe, None, posOpt)
        val (valueType, cfAfterValueEval) = analyze(value, cfIn)
        enforceBaseSubtypingConstraint(valueType, tpe)(using "type ascription")
        cfAfterValueEval
      case SSA.StaticAssert(formula) =>
        val (formulaType, cfAfterFormulaEval) = analyze(formula, cfIn)
        enforceBaseSubtypingConstraint(formulaType, BoolType)(using "assertion")
        cfAfterFormulaEval
      case SSA.FieldWrite(owner, fieldName, rhs) =>
        val (ownerType, cfAfterOwnerEval) = analyze(owner, cfIn)
        val (rhsType, cfAfterRhsEval) = analyze(rhs, cfAfterOwnerEval)
        checkFieldAndReturnType(owner, ownerType.baseType, fieldName, posOpt,
          checkIsReassignable = false, ownerThatMustBeThis = None).foreach { fieldType =>
          enforceBaseSubtypingConstraint(rhsType, fieldType)(using "field assignment")
        }
        cfAfterRhsEval
      case SSA.Return(retVal) =>
        val (retType, cfAfterRetValEval) = analyze(retVal, cfIn)
        enforceBaseSubtypingConstraint(retType, funCtx.expectedReturnType)(using "return value")
        if (funCtx.expectedReturnType == UnitType) {
          warn(s"returning $UnitType", posOpt)
        }
        ControlFlowInfo.exited
      case SSA.Panic(msg) =>
        val (msgType, cfAfterMsgEval) = analyze(msg, cfIn)
        enforceBaseSubtypingConstraint(msgType, StringType)(using "panic message")
        ControlFlowInfo.exited
      case SSA.Evaluate(formula) =>
        val (tpe, cfAfterFormulaEval) = analyze(formula, cfIn)
        cfAfterFormulaEval
      case SSA.DynamicAssert(formula) => ???
      case SSA.LocalDecl(localId, tpe) =>
        funCtx.checkType(tpe, None, posOpt)
        cfIn
      case SSA.ClosureCreation(assignedValue, params, body) =>
        for ((paramId, paramType) <- params) {
          ts(paramId) = paramType
        }
        val resultTypeVar = new TypeVariable(s"${assignedValue}_res")
        ts(assignedValue) = ClosureType(params.map(_._2), resultTypeVar)
        closuresCollector.enqueue(ClosureInfo(body, funCtx.copyForClosureBody(resultTypeVar), cfIn, resultTypeVar, posOpt))
        cfIn
    }
  }

  private def analyzeIdVal(idValue: IdValue, cfIn: ControlFlowInfo)
                          (using funCtx: FunctionContext, ts: TypeStore, er: ErrorReporter, program: Program): Type = {
    ts.typeOfOpt(idValue) match {
      case Some(regularType) =>
        cfIn.inferredTypeFor(idValue) match {
          case Some(typeId) =>
            import DowncastTargetCheckResult.*
            val morePreciseType = checkDowncastTarget(regularType, typeId) match {
              case CanDowncast(tpe) => tpe
              case CannotDowncast(reason) => regularType
            }
            morePreciseType
          case _ => regularType
        }
      // typically, the type of a missing value because of an illegal construct
      case _ => NothingType
    }
  }

  private[typechecking] def analyze(formula: Formula, cfIn: ControlFlowInfo)
                                   (using funCtx: FunctionContext, ts: TypeStore, er: ErrorReporter, program: Program): (Type, ControlFlowInfo) = {
    val posOpt =
      if program.formulaPositions.containsKey(formula)
      then Some(program.formulaPositions.get(formula))
      else None
    val (outTypeRaw: Type, cfAfterEval: ControlFlowInfo) = formula match {
      case idValue: IdValue =>
        val tpe = analyzeIdVal(idValue, cfIn)
        (tpe, cfIn)
      case True | False => (BoolType, cfIn)
      case NullPtr => (NullType, cfIn)
      case UnitVal => (UnitType, cfIn)
      case IntConstant(value) => (IntType, cfIn)
      case DoubleConstant(value) => (DoubleType, cfIn)
      case StringConstant(value) => (StringType, cfIn)
      case Equal(lhs, rhs) =>
        val (lhsType, cfBetweenMembers) = analyze(lhs, cfIn)
        val (rhsType, cfOut) = analyze(rhs, cfBetweenMembers)
        if (areProvablyDisjointUnlessNull(lhsType.baseType, rhsType.baseType)) {
          reportError(s"illegal equality test: ${lhsType.baseType} and ${rhsType.baseType} are incompatible types", posOpt)
        }
        (BoolType, cfOut)
      case op: BinOp =>
        val (lhsTypeRaw, lhsOutCf) = analyze(op.lhs, cfIn)
        val lhsTypeDesBase = program.desugarType(lhsTypeRaw).baseType
        // TODO make this a lazy val?
        val (lhsTrueInfos, lhsFalseInfos) = extractTypeInfos(op.lhs)
        val rhsStartCf = op.operator match {
          case Operator.And =>
            lhsOutCf.refined(lhsTrueInfos)
          case Operator.Or =>
            lhsOutCf.refined(lhsFalseInfos)
          case _ => lhsOutCf
        }
        val (rhsTypeRaw, rhsOutCf) = analyze(op.rhs, rhsStartCf)
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
        (tpe, lhsOutCf.merged(rhsOutCf))
      case op: UnaryOp =>
        val (operandTypeRaw, cfOut) = analyze(op.operand, cfIn)
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
        (tpe, cfOut)
      case Call(receiverArg, funId, typeArgs, args) =>
        val (receiverArgType, cfAfterReceiver) = analyze(receiverArg, cfIn)
        typeArgs.foreach(funCtx.checkType(_, None, posOpt))
        program.forceComputeJoins(program.desugarType(receiverArgType).baseType) match {
          case Some(Types.NamedType(receiverTypeName, receiverTypeArgs, receiverArgs)) =>
            assert(receiverArgs.isEmpty)
            program.resolveSignatureAs[RuntimeTypeSignature](receiverTypeName) match {
              case None =>
                reportError(s"type not found: $receiverTypeName", posOpt)
                (NothingType, cfAfterReceiver)
              case Some(_: Unencapsulated) =>
                reportMethodNotFoundInType(receiverArgType.baseType, funId, posOpt)
                (NothingType, cfAfterReceiver)
              case Some(receiverTypeSig: Encapsulated) =>
                findMethod(receiverTypeName, funId) match {
                  case None =>
                    reportMethodNotFoundInType(receiverArgType.baseType, funId, posOpt)
                    (NothingType, cfAfterReceiver)
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
                    var currCf = cfAfterReceiver
                    if (argsSizeMatch) {
                      for (((paramVal, paramTypeRaw), arg) <- funSig.paramsInclThis.tail zip args) {
                        val (argType, cfAfterParam) = analyze(arg, currCf)
                        val paramTypeSubst = paramTypeRaw.substitute(subst, argsSubst.toMap)
                        enforceBaseSubtypingConstraint(argType, paramTypeSubst)(using "method argument", posOpt)
                        arg match {
                          case arg: Value =>
                            argsSubst(paramVal) = arg
                          case _ => ()
                        }
                        currCf = cfAfterParam
                      }
                    }
                    (funSig.retType.substitute(subst, argsSubst.toMap), currCf)
                }
            }
          case None =>
            reportMethodNotFoundInType(receiverArgType.baseType, funId, posOpt)
            (NothingType, cfAfterReceiver)
        }
      case ClosureInvocation(closure, args) =>
        val (closureType, cfAfterClosureEval) = analyze(closure, cfIn)
        val argTypesB = List.newBuilder[Type]
        var currCf = cfAfterClosureEval
        for (arg <- args) {
          val (argType, cfAfterArgEval) = analyze(arg, currCf)
          argTypesB.addOne(argType)
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
            NothingType
        }
        // FIXME make sure the way taints are handled in closures is correct (we probably need to prevent closures from having a non-deterministic return value)
        (tpe, currCf)
      case Select(owner, fieldName) =>
        val (ownerType, cfAfterOwnerEval) = analyze(owner, cfIn)
        val tpe = if ownerType.baseType == NothingType then NothingType
        else checkFieldAndReturnType(funCtx.thisVal, ownerType.baseType, fieldName, posOpt, checkIsReassignable = false, Some(owner))
          .getOrElse(NothingType)
        (tpe, cfAfterOwnerEval)
      case HasType(formula, tpe) =>
        import DowncastTargetCheckResult.*
        val (formulaType, cfAfterFormulaEval) = analyze(formula, cfIn)
        checkDowncastTarget(formulaType, tpe) match {
          case CanDowncast(tpe) => ()
          case CannotDowncast(reason) =>
            reportError(s"illegal type test: $reason", posOpt)
        }
        (BoolType, cfAfterFormulaEval)
    }
    val outCf = if outTypeRaw == NothingType then ControlFlowInfo.exited else cfAfterEval
    (outTypeRaw.withTypeVarsExpanded, outCf)
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
      ts.typeOfOpt(idValue).map(_.baseType) match {
        case Some(NamedType(knownType, _, Nil)) =>
          (Set(TypeInfo(idValue, knownType, List(testedType), List.empty)),
            Set(TypeInfo(idValue, knownType, List.empty, List(testedType))))
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

  private def checkFieldAndReturnType(
                                       ownerVal: Value,
                                       ownerType: BaseType,
                                       fieldName: FunOrVarId,
                                       posOpt: Option[Position],
                                       checkIsReassignable: Boolean,
                                       ownerThatMustBeThis: Option[Formula]
                                     )(using er: ErrorReporter, program: Program): Option[Type] = {
    program.forceComputeJoins(program.desugarType(ownerType).baseType) match {
      case Some(Types.NamedType(typeName, typeArgs, args)) =>

        def subst(sig: RuntimeTypeSignature, tpe: Type): Type = {
          val subst = sig.typeParams.map(_._1).zip(typeArgs).toMap
          tpe.substitute(subst, Map.empty)
        }

        program.resolveSignatureAs[RuntimeTypeSignature](typeName).flatMap {
          case recordSig: RecordSignature =>
            recordSig.fields.get(fieldName) match {
              case Some(field) => Some(subst(recordSig, field.tpe))
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
                Some(subst(classSig, field.tpe))
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
    case CanDowncast(tpe: NamedType)
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
                  targetSig.toType(newTargetSubst, Map.empty) match {
                    case namedType: NamedType => CanDowncast(namedType)
                    case tpe => CannotDowncast(s"type $tpe is not eligible for downcasting")
                  }
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

  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Err(TypeChecking, msg, posOpt))
  }

  private def warn(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Warning(TypeChecking, msg, posOpt))
  }

  private case class ClosureInfo(body: List[Instr], funCtx: FunctionContext, startCf: ControlFlowInfo, expectedRetTypeVar: TypeVariable, posOpt: Option[Position])

}
