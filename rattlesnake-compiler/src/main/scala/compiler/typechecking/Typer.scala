package compiler.typechecking

import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.*
import compiler.typechecking.TypeCheckingContext.TypeInfo
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.*
import lang.Operators.OperatorSignature
import lang.Types.*
import lang.Types.PrimitiveType.*
import lang.Values.*

import scala.util.boundary


final class Typer(private val er: ErrorReporter, private val continueIfErrors: Boolean = false) extends CompilerStep[Program, (Program, TypeStore)] {

  override def apply(program: Program): (Program, TypeStore) = {
    val ts = new MutableTypeStore
    for ((funSig, func) <- program.functions) {
      val (thisVal, thisType) = funSig.paramsInclThis.head
      for ((argVal, argType) <- funSig.paramsInclThis) {
        ts(argVal) = argType
      }
      func.bodyOpt.foreach { body =>
        val startCtx = TypeCheckingContext(program, Map.empty, thisVal, alwaysExitsFlag = false, expectedReturnType = funSig.retType)
        val endCtx = traverseAll(body, startCtx)(using ts, er, program)
        if (funSig.retType.baseType != VoidType && !endCtx.alwaysExitsFlag) {
          reportError(s"missing return in non-$VoidType method", func.posOpt)
        }
      }
    }
    if (!continueIfErrors) {
      er.displayAndTerminateIfErrors()
    }
    (program, ts)
  }

  private def traverseAll(instructions: List[Instr], tcCtx: TypeCheckingContext)(using ts: MutableTypeStore, er: ErrorReporter, program: Program): TypeCheckingContext =
    instructions.foldLeft(tcCtx) { (ctx, instr) =>
      traverse(instr, ctx)
    }

  private def traverse(instr: Instr, tcCtx: TypeCheckingContext)(using ts: MutableTypeStore, er: ErrorReporter, program: Program): TypeCheckingContext = {
    given posOpt: Option[Position] = instr.getAstNodeOpt.flatMap(_.getPosition)

    val endCtxRaw = instr match {
      case SSA.Loop(cond, body, variables) =>
        for (LoopVarInfo(varId, beforeLoopVal, bodyStartVal, bodyEndVal, afterLoopVal) <- variables) {
          ts(bodyStartVal) = computeType(beforeLoopVal)(using tcCtx)
        }
        val condType = computeType(cond)(using tcCtx)
        enforceBaseSubtypingConstraint(condType, BoolType)(using "loop condition")
        val (bodyInfos, afterLoopInfos) = extractTypeInfos(cond)
        val bodyCtx = tcCtx.withTypeInfoRefined(bodyInfos)
        val afterBodyCtx = traverseAll(body, bodyCtx)
        for (LoopVarInfo(varId, beforeLoopVal, bodyStartVal, bodyEndVal, afterLoopVal) <- variables) {
          val typeAtEndOfBody = computeType(bodyEndVal)(using afterBodyCtx)
          val typeAtBeginningOfBody = ts.typeOf(bodyStartVal)
          enforceBaseSubtypingConstraint(typeAtEndOfBody.baseType, typeAtBeginningOfBody.baseType)(using s"base type of $varId at the end of loop body")
        }
        val afterLoopCtx = tcCtx.withTypeInfoRefined(afterLoopInfos)
        for (LoopVarInfo(varId, beforeLoopVal, bodyStartVal, bodyEndVal, afterLoopVal) <- variables) {
          ts(afterLoopVal) = Types.join(computeType(beforeLoopVal)(using afterLoopCtx), computeType(bodyEndVal)(using afterLoopCtx))
        }
        afterLoopCtx
      case SSA.Disjunction(cond, thenBr, elseBr, postMerges) =>
        val condType = computeType(cond)(using tcCtx)
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
        ts(assignedValue) = Types.join(inValues.map(computeType(_)(using tcCtx)))
        tcCtx
      case SSA.Assignment(assignedValue, rhs) =>
        val rhsType = computeType(rhs)(using tcCtx)
        ts(assignedValue) = rhsType
        tcCtx
      case SSA.Instantiate(assignedValue, classOrRecordName, typeArgs, initialization) =>
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
                    computeType(rhs)(using tcCtx)
                  case _ => ()
                }
            }
        }
        tcCtx
      case SSA.Cast(resultValue, castValue, targetType) =>
        val castValueType = computeType(castValue)(using tcCtx)
        import DowncastTargetCheckResult.*
        checkDowncastTarget(castValueType, targetType) match {
          case CanDowncast(tpe) =>
            ts(resultValue) = tpe
          case CannotDowncast(reason) =>
            reportError(s"illegal cast: $reason", instr.getAstNodeOpt.flatMap(_.getPosition))
        }
        tcCtx.withTypeInfoRefined(Set(TypeInfo(castValue, targetType, Set(targetType), Set.empty)))
      case SSA.StaticTypeAssert(value, tpe) =>
        enforceBaseSubtypingConstraint(computeType(value)(using tcCtx), tpe)(using "type ascription")
        tcCtx
      case SSA.StaticAssert(formula) =>
        computeType(formula)(using tcCtx)
        tcCtx
      case SSA.FieldWrite(owner, fieldName, rhs) =>
        val ownerType = computeType(owner)(using tcCtx)
        val rhsType = computeType(rhs)(using tcCtx)
        checkFieldAndReturnItsType(ownerType.baseType, fieldName, posOpt,
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
        val retType = computeType(retVal)(using tcCtx)
        enforceBaseSubtypingConstraint(retType, tcCtx.expectedReturnType)(using "return value")
        if (tcCtx.expectedReturnType == VoidType) {
          reportError(s"$VoidType method returning a value", posOpt)
        }
        tcCtx.withAlwaysExitsFlagRaised
      case SSA.Panic(msg) =>
        val msgType = computeType(msg)(using tcCtx)
        enforceBaseSubtypingConstraint(msgType, StringType)(using "panic message")
        tcCtx.withAlwaysExitsFlagRaised
      case SSA.Evaluate(formula) =>
        val tpe = computeType(formula)(using tcCtx)
        if tpe.baseType == NothingType then tcCtx.withAlwaysExitsFlagRaised else tcCtx
      case SSA.DynamicAssert(formula) => ???
    }
    endCtxRaw.withAlwaysExitsFlagRecomputed
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
      ts.baseTypeOfOpt(idValue) match {
        case Some(NamedType(knownType, _, Nil)) =>
          (Set(TypeInfo(idValue, knownType, Set(testedType), Set.empty)),
            Set(TypeInfo(idValue, knownType, Set.empty, Set(testedType))))
        case _ => (Set.empty, Set.empty)
      }
    case _ => (Set.empty, Set.empty)
  }

  private def computeType(formula: Formula)
                         (using tcCtx: TypeCheckingContext, ts: TypeStore, er: ErrorReporter, program: Program): Type = {
    val posOpt =
      if program.formulaPositions.containsKey(formula)
      then Some(program.formulaPositions.get(formula))
      else None
    val tpeRaw = formula match {
      case idValue: IdValue =>
        ts.typeOfOpt(idValue) match {
          case Some(regularType) =>
            tcCtx.inferredTypeFor(idValue) match {
              case Some(typeId) =>
                import DowncastTargetCheckResult.*
                checkDowncastTarget(regularType, typeId) match {
                  case CanDowncast(tpe) => tpe
                  case CannotDowncast(reason) => regularType
                }
              case _ => regularType
            }
          // typically, the type of a missing value because of an illegal construct
          case _ => NothingType
        }
      case True | False => BoolType
      case NullPtr => NullType
      case IntConstant(value) => IntType
      case DoubleConstant(value) => DoubleType
      case StringConstant(value) => StringType
      case op: BinOp =>
        val lhsType = computeType(op.lhs)
        // TODO smartcasts for second branch
        val rhsType = computeType(op.rhs)
        if (lhsType.baseType == NothingType || rhsType.baseType == NothingType) {
          NothingType
        } else {
          val candidateOperators = Operators.binaryOperators.filter { opSig =>
            opSig.op == op.operator
              && lhsType.baseType.trivialSubtypeOf(opSig.leftOperandType.baseType)
              && rhsType.baseType.trivialSubtypeOf(opSig.rightOperandType.baseType)
          }
          resolveCandidatesOp(candidateOperators, op.operator, s"operand types $lhsType and $rhsType", posOpt) match {
            case Some(opSig) =>
              enforceBaseSubtypingConstraint(lhsType, opSig.leftOperandType)(using "operand", posOpt)
              opSig.retType
            case None => NothingType
          }
        }
      case op: UnaryOp =>
        val operandType = computeType(op.operand)
        if (operandType == NothingType) {
          NothingType
        } else {
          val candidatesOperators = Operators.unaryOperators.filter { opSig =>
            opSig.op == op.operator && operandType.baseType.trivialSubtypeOf(opSig.operandType.baseType)
          }
          resolveCandidatesOp(candidatesOperators, op.operator, s"operand type $operandType", posOpt) match {
            case Some(opSig) =>
              enforceBaseSubtypingConstraint(operandType, opSig.operandType)(using "operand", posOpt)
              opSig.retType
            case None => NothingType
          }
        }
      case Call(receiver, funId, typeArgs, args) =>
        val receiverType = computeType(receiver)
        val argTypes = args.map(computeType)
        forceComputeJoins(program.desugarType(receiverType).baseType) match {
          case Some(Types.NamedType(receiverTypeName, receiverTypeArgs, receiverArgs)) =>
            assert(receiverArgs.isEmpty)
            program.resolveSignatureAs[RuntimeTypeSignature](receiverTypeName) match {
              case None =>
                reportError(s"type not found: $receiverTypeName", posOpt)
              case Some(_: Unencapsulated) =>
                reportMethodNotFoundInType(receiverType.baseType, funId, posOpt)
              case Some(receiverTypeSig: Encapsulated) =>
                receiverTypeSig.functions.get(funId) match {
                  case None => reportMethodNotFoundInType(receiverType.baseType, funId, posOpt)
                  case Some(funSig) =>
                    val argsSizeMatch = args.size == funSig.paramsInclThis.size - 1
                    if (!argsSizeMatch) {
                      reportError(s"wrong number of arguments for method $funId: expected ${funSig.paramsInclThis.size - 1}, was ${args.size}", posOpt)
                    }
                    val substOpt = for {
                      funcSubst <- generateTypeParamsMapping(funSig.typeParams, typeArgs, posOpt, s"$funId", reportIfLengthMismatch = true)
                    } yield generateTypeParamsMapping(receiverTypeSig.typeParams.map(_._1), receiverTypeArgs, posOpt, "recverr", reportIfLengthMismatch = false) match {
                      case Some(receiverSubst) => receiverSubst ++ funcSubst
                      case None => funcSubst
                    }

                    def substIfNeeded(tpe: Type): Type = {
                      substOpt match {
                        case None => tpe
                        case Some(subst) => tpe.substitute(subst, Map.empty)
                      }
                    }

                    if (argsSizeMatch) {
                      for (((_, paramTypeRaw), argType) <- funSig.paramsInclThis.tail zip argTypes) {
                        val paramType = program.desugarType(substIfNeeded(paramTypeRaw))
                        enforceBaseSubtypingConstraint(paramType, argType)(using "method argument", posOpt)
                      }
                    }
                    program.desugarType(substIfNeeded(funSig.retType))
                }
            }
          case None =>
            reportMethodNotFoundInType(receiverType.baseType, funId, posOpt)
        }
      case Select(owner, fieldName) =>
        val ownerType = computeType(owner)
        if ownerType.baseType == NothingType then NothingType
        else checkFieldAndReturnItsType(ownerType.baseType, fieldName, posOpt, checkIsReassignable = false, Some(owner))
          .getOrElse(NothingType)
      case HasType(formula, tpe) =>
        import DowncastTargetCheckResult.*
        val formulaType = computeType(formula)
        checkDowncastTarget(formulaType, tpe) match {
          case CanDowncast(tpe) => ()
          case CannotDowncast(reason) =>
            reportError(s"illegal type test: $reason", posOpt)
        }
        BoolType
    }
    tpeRaw.withTypeVarsExpanded
  }

  private def generateTypeParamsMapping(typeParams: List[TypeIdentifier], typeArgs: List[Type], posOpt: Option[Position], contextDescr: String, reportIfLengthMismatch: Boolean): Option[Map[TypeIdentifier, Type]] = {
    if (typeArgs.nonEmpty && typeArgs.size != typeParams.size) {
      if (reportIfLengthMismatch) {
        reportError(s"wrong number of type arguments: expected ${typeParams.size}, was ${typeArgs.size}", posOpt)
      }
      None
    } else if (typeArgs.isEmpty && typeParams.nonEmpty) Some {
      typeParams.map(tp => tp -> new TypeVariable(s"${contextDescr}_$tp")).toMap
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

  private def checkFieldAndReturnItsType(
                                          ownerType: BaseType, fieldName: FunOrVarId,
                                          posOpt: Option[Position],
                                          checkIsReassignable: Boolean, ownerThatMustBeThis: Option[Formula]
                                        )(using tcCtx: TypeCheckingContext, er: ErrorReporter, program: Program): Option[Type] = {
    forceComputeJoins(program.desugarType(ownerType).baseType) match {
      case Some(Types.NamedType(typeName, typeArgs, args)) =>

        def subst(sig: RuntimeTypeSignature, tpe: Type): Type = {
          val subst = sig.typeParams.map(_._1).zip(typeArgs).toMap
          tpe.substitute(subst, Map.empty)
        }

        program.resolveSignatureAs[RuntimeTypeSignature](typeName) match {
          case None =>
            reportError(s"type not found: $typeName", posOpt)
            None
          case Some(recordSig: RecordSignature) =>
            recordSig.fields.get(fieldName) match {
              case Some(field) => Some(subst(recordSig, field.tpe))
              case None =>
                reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
            }
          case Some(classSig: ClassSignature) if ownerThatMustBeThis.forall(_ == tcCtx.thisVal) =>
            classSig.fields.get(fieldName) match {
              case None =>
                reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
              case Some(field) =>
                if (checkIsReassignable && field.isStable) {
                  reportError(s"field $fieldName is not reassignable", posOpt)
                }
                Some(subst(classSig, field.tpe))
            }
          case Some(_: ClassSignature) =>
            reportError(s"field not found or not accessible in $typeName; note that class fields are always private and should be accessed from the outside through getters only", posOpt)
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

  private def reportMethodNotFoundInType(receiverType: BaseType, funId: FunOrVarId, posOpt: Option[Position])(using Program): NothingType.type = {
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

  private def reportError(msg: String, posOpt: Option[Position]): NothingType.type = {
    er.push(Err(TypeChecking, msg, posOpt))
    NothingType
  }

  extension [T](l: Iterable[T]) private def zipCommons[U](r: Iterable[U]): Iterable[(T, U)] =
    l.take(r.size).zip(r.take(l.size))

}
