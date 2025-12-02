package compiler.typechecking

import compiler.irs.SSA
import compiler.irs.SSA.Instr
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.*
import identifiers.FunOrVarId
import lang.*
import lang.Operators.OperatorSignature
import lang.Types.PrimitiveType.*
import lang.Types.{BaseType, Type, TypeVariable}
import lang.Values.*

final class Typer(private val er: ErrorReporter) extends CompilerStep[(Map[FunctionSignature, SSA.Function], Program), (Map[FunctionSignature, SSA.Function], Program, TypeStore)] {

  override def apply(input: (Map[FunctionSignature, SSA.Function], Program)): (Map[FunctionSignature, SSA.Function], Program, TypeStore) = {
    val (functions, program) = input
    val ts = new PartialTypeStore
    for ((funSig, func) <- functions) {
      val (thisVal, thisType) = funSig.paramsInclThis.head
      ts(thisVal) = thisType
      val tcCtx = TypeCheckingContext(program, Map.empty, thisVal)
      func.bodyOpt.foreach { body =>
        traverseAll(body, tcCtx)(using ts, er, program)
      }
    }
    (functions, program, ts)
  }

  private def traverseAll(instructions: List[Instr], tcCtx: TypeCheckingContext)(using ts: PartialTypeStore, er: ErrorReporter, program: Program): TypeCheckingContext =
    instructions.foldLeft(tcCtx) { (ctx, instr) =>
      traverse(instr, ctx)
    }

  private def traverse(instr: Instr, tcCtx: TypeCheckingContext)(using ts: PartialTypeStore, er: ErrorReporter, program: Program): TypeCheckingContext = {
    given Option[Position] = instr.getAstNodeOpt.flatMap(_.getPosition)

    instr match {
      case SSA.Loop(cond, body, variables) =>
        val condType = computeTypes(cond)(using tcCtx)
        enforceSubtypingConstraint(condType, BoolType)(using "loop condition")
        val bodyCtx = tcCtx.withAdditionalSmartCasts(extractSmartcastsForThenBranch(cond))
        traverseAll(body, bodyCtx)
        tcCtx.withAdditionalSmartCasts(extractSmartcastsForElseBranch(cond))
      case SSA.Disjunction(cond, thenBr, elseBr, postMerges) =>
        val condType = computeTypes(cond)(using tcCtx)
        enforceSubtypingConstraint(condType, BoolType)(using "condition")
        val thenStartCtx = tcCtx.withAdditionalSmartCasts(extractSmartcastsForThenBranch(cond))
        val thenEndCtx = traverseAll(thenBr, thenStartCtx)
        val elseStartCtx = tcCtx.withAdditionalSmartCasts(extractSmartcastsForElseBranch(cond))
        val elseEndCtx = traverseAll(elseBr, elseStartCtx)
        val ctxAfter =
          if thenEndCtx.alwaysExitsFlagIsRaised then elseEndCtx
          else if elseEndCtx.alwaysExitsFlagIsRaised then thenEndCtx
          else tcCtx
        traverseAll(postMerges, ctxAfter)
      case SSA.Phi(assignedValue, inValues) => ???
      case SSA.Assignment(assignedValue, rhs) =>
        val rhsType = computeTypes(rhs)(using tcCtx)
        ts(assignedValue) = rhsType
        tcCtx
      case SSA.Instantiate(assignedValue, classOrStructName) => ???
      case SSA.Cast(assignedValue, inValue, targetType) => ???
      case SSA.StaticTypeAssert(value, tpe) => ???
      case SSA.StaticAssert(formula) =>
        computeTypes(formula)(using tcCtx)
        tcCtx
      case SSA.FieldWrite(owner, fieldName, rhs) => ???
      case SSA.Return(None) =>
        tcCtx.raiseAlwaysExitsFlag()
        tcCtx
      case SSA.Return(Some(retVal)) =>
        computeTypes(retVal)(using tcCtx)
        tcCtx.raiseAlwaysExitsFlag()
        tcCtx
      case SSA.Panic(msg) =>
        computeTypes(msg)(using tcCtx)
        tcCtx.raiseAlwaysExitsFlag()
        tcCtx
      case SSA.Evaluate(formula) =>
        computeTypes(formula)(using tcCtx)
        tcCtx
      case SSA.DynamicAssert(formula) => ???
    }
  }

  private def computeTypes(formula: Formula)
                          (using tcCtx: TypeCheckingContext, ts: TypeStore, er: ErrorReporter, program: Program): Type = {
    val posOpt = if program.formulaPositions.containsKey(formula) then Some(program.formulaPositions.get(formula)) else None
    formula match {
      case value: IdValue =>
        // must be known, otherwise SSA generation would have failed
        tcCtx.smartcasts.getOrElse(value, ts.typeOf(value))
      case True | False => BoolType
      case NullPtr => NullType
      case IntConstant(value) => IntType
      case DoubleConstant(value) => DoubleType
      case StringConstant(value) => StringType
      case op: BinOp =>
        val lhsType = computeTypes(op.lhs)
        val rhsType = computeTypes(op.rhs)
        val candidateOperators = Operators.binaryOperators.filter { opSig =>
          opSig.op == op.operator
            && lhsType.baseType.trivialSubtypeOf(opSig.leftOperandType.baseType)
            && rhsType.baseType.trivialSubtypeOf(opSig.rightOperandType.baseType)
        }
        resolveCandidatesOp(candidateOperators, op.operator, s"operand types $lhsType and $rhsType", posOpt) match {
          case Some(opSig) =>
            enforceSubtypingConstraint(lhsType, opSig.leftOperandType)(using "operand", posOpt)
            opSig.retType
          case None => NothingType
        }
      case op: UnaryOp =>
        val operandType = computeTypes(op.operand)
        val candidatesOperators = Operators.unaryOperators.filter { opSig =>
          opSig.op == op.operator && operandType.baseType.trivialSubtypeOf(opSig.operandType.baseType)
        }
        resolveCandidatesOp(candidatesOperators, op.operator, s"operand type $operandType", posOpt) match {
          case Some(opSig) =>
            enforceSubtypingConstraint(operandType, opSig.operandType)(using "operand", posOpt)
            opSig.retType
          case None => NothingType
        }
      case Call(receiver, funId, args) =>
        val receiverType = computeTypes(receiver)
        val argTypes = args.map(computeTypes)
        program.desugarType(receiverType).baseType match {
          case Types.NamedType(typeName, typeArgs, args) =>
            assert(args.isEmpty)
            program.resolveSignatureAs[RuntimeTypeSignature](typeName) match {
              case None =>
                reportError(s"type not found: $typeName", posOpt)
              case Some(_: UnencapsulatedTypeSignature) =>
                reportMethodNotFoundInType(receiverType.baseType, funId, posOpt)
              case Some(receiverTypeSig: EncapsulatedTypeSignature) =>
                receiverTypeSig.functions.get(funId) match {
                  case None => reportMethodNotFoundInType(receiverType.baseType, funId, posOpt)
                  case Some(funSig) =>
                    val argsSizeMatch = args.size != funSig.paramsInclThis.size - 1
                    if (argsSizeMatch) {
                      reportError(s"wrong number of parameters for method $funId: expected ${funSig.paramsInclThis.size - 1}, was ${args.size}", posOpt)
                    }
                    val substOpt = if (typeArgs.nonEmpty && typeArgs.size != funSig.typeParams.size) {
                      reportError(s"wrong number of type parameters for method $funId: expected ${funSig.typeParams.size}, was ${typeArgs.size}", posOpt)
                      None
                    } else if (typeArgs.isEmpty && funSig.typeParams.nonEmpty) Option.when(argsSizeMatch) {
                      funSig.typeParams.map(_ -> new TypeVariable).toMap
                    } else Some {
                      funSig.typeParams.zip(argTypes).toMap
                    }

                    def substIfNeeded(tpe: Type): Type = {
                      substOpt match {
                        case None => tpe
                        case Some(subst) => tpe.substitute(subst, Map.empty)
                      }
                    }

                    if (argsSizeMatch) {
                      for (((_, paramTypeRaw), argType) <- funSig.paramsInclThis.tail zip argTypes) {
                        val paramType = substIfNeeded(paramTypeRaw)
                        enforceSubtypingConstraint(paramType, argType)(using "method argument", posOpt)
                      }
                    }
                    substIfNeeded(funSig.retType)
                }
            }
          case _ => reportMethodNotFoundInType(receiverType.baseType, funId, posOpt)
        }
      case Select(owner, fieldName) =>
        val ownerType = computeTypes(owner)
        findField(owner, ownerType, fieldName, posOpt, fieldShouldBeReassignable = false)
      case HasType(formula, tpe) => ???
    }
  }

  private def extractSmartcastsForThenBranch(cond: Formula): Map[IdValue, BaseType] = cond match {
    case And(lhs, rhs) => extractSmartcastsForThenBranch(lhs) ++ extractSmartcastsForThenBranch(rhs)
    case HasType(value: IdValue, tpe) => Map(value -> tpe.baseType)
    case _ => Map.empty
  }

  private def extractSmartcastsForElseBranch(cond: Formula): Map[IdValue, BaseType] = cond match {
    case Or(lhs, rhs) => extractSmartcastsForElseBranch(lhs) ++ extractSmartcastsForElseBranch(rhs)
    case HasType(value: IdValue, tpe) => Map(value -> tpe.baseType)
    case _ => Map.empty
  }

  private def findField(owner: Formula, ownerType: Type, fieldName: FunOrVarId, posOpt: Option[Position], fieldShouldBeReassignable: Boolean)(using er: ErrorReporter, program: Program, tcCtx: TypeCheckingContext): Type = {
    program.desugarType(ownerType).baseType match {
      case _: Types.PrimitiveType =>
        reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
      case Types.NamedType(typeName, typeArgs, args) =>
        program.resolveSignatureAs[RuntimeTypeSignature](typeName) match {
          case None =>
            reportError(s"type not found: $typeName", posOpt)
          case Some(structSig: StructSignature) =>
            structSig.fields.get(fieldName) match {
              case Some(field) => field.tpe
              case None =>
                reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
            }
          case Some(classSig: ClassSignature) if owner == tcCtx.thisVal =>
            classSig.fields.get(fieldName) match {
              case None =>
                reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
              case Some(field) =>
                if (fieldShouldBeReassignable && field.isStable) {
                  reportError(s"field $fieldName is not reassignable", posOpt)
                }
                field.tpe
            }
          case Some(_: ClassSignature) =>
            reportError(s"field not found or not accessible in $typeName; note that class fields are always private and should be accessed from the outside through getters only", posOpt)
          case _ =>
            reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
        }
      case _: TypeVariable =>
        reportError(s"access to field $fieldName: cannot resolve receiver type", posOpt)
    }
  }

  private def reportMethodNotFoundInType(receiverType: BaseType, funId: FunOrVarId, posOpt: Option[Position])(using Program): NothingType.type = {
    val receiverTypeDescr = mkReceiverTypeDescr(receiverType)
    reportError(s"method $funId not found in $receiverTypeDescr", posOpt)
  }

  private def reportFieldNotFoundInType(receiverType: BaseType, fieldId: FunOrVarId, posOpt: Option[Position])(using Program): NothingType.type = {
    val receiverTypeDescr = mkReceiverTypeDescr(receiverType)
    reportError(s"field $fieldId not found in $receiverTypeDescr", posOpt)
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
