package compiler.typechecking

import compiler.irs.SSA
import compiler.irs.SSA.Instr
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.baseSubtypeOf
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.*
import lang.Operators.OperatorSignature
import lang.Types.PrimitiveType.*
import lang.Types.{BaseType, Type}
import lang.Values.*

import java.util

final class Typer(private val er: ErrorReporter) extends CompilerStep[(Map[FunctionSignature, SSA.Function], Program), (Map[FunctionSignature, SSA.Function], Program, TypeStore)] {

  override def apply(input: (Map[FunctionSignature, SSA.Function], Program)): (Map[FunctionSignature, SSA.Function], Program, TypeStore) = {
    val (functions, program) = input

    ??? // TODO
  }

  private case class ThisContext(thisVal: IdValue, thisType: BaseType)

  private def traverse(instr: Instr)(using ts: PartialTypeStore, formulaPositions: util.IdentityHashMap[Formula, Position], program: Program, thisCtx: ThisContext): Unit = instr match {
    case SSA.Loop(preBodyCond, cond, body, postMerges) => ???
    case SSA.Disjunction(cond, thenBr, elseBr, postMerges) => ???
    case SSA.RegPhi(assignedValue, inValues) => ???
    case SSA.LoopIterPhi(assignedValue, baseCaseValue, prevIterValue) => ???
    case SSA.LoopExitPhi(assignedValue, bodyEndValue, skipLoopValue) => ???
    case SSA.Assignment(assignedValue, rhs) => ???
    case SSA.Instantiate(assignedValue, classOrStructName) => ???
    case SSA.Cast(assignedValue, inValue, targetType) => ???
    case SSA.StaticTypeAssert(value, tpe) => ???
    case SSA.StaticAssert(formula) => ???
    case SSA.FieldWrite(owner, fieldName, rhs) => ???
    case SSA.Return(retVal) => ???
    case SSA.Panic(msg) => ???
    case SSA.Evaluate(formula) => ???
    case SSA.DynamicAssert(formula) => ???
  }

  private def computeTypes(formula: Formula)
                          (using ts: TypeStore, program: Program, formulaPositions: util.IdentityHashMap[Formula, Position], thisCtx: ThisContext): Type = {
    val posOpt = if formulaPositions.containsKey(formula) then Some(formulaPositions.get(formula)) else None
    formula match {
      case value: IdValue =>
        // must be known, otherwise SSA generation would have failed
        ts.typeOf(value)
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
            && lhsType.baseSubtypeOf(opSig.leftOperandType)
            && rhsType.baseSubtypeOf(opSig.rightOperandType)
        }
        resolveCandidatesOp(candidateOperators, op.operator, s"operand types $lhsType and $rhsType", posOpt)
      case op: UnaryOp =>
        val operandType = computeTypes(op.operand)
        val candidatesOperators = Operators.unaryOperators.filter { opSig =>
          opSig.op == op.operator && operandType.baseSubtypeOf(opSig.operandType)
        }
        resolveCandidatesOp(candidatesOperators, op.operator, s"operand type $operandType", posOpt)
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
                    } else if (typeArgs.isEmpty && funSig.typeParams.nonEmpty) {
                      if (argsSizeMatch) {
                        funSig.paramsInclThis.tail.zip(argTypes).foldLeft(Option(Map.empty[TypeIdentifier, Type])) {
                          case (None, _) => None
                          case (Some(prevSubst), ((_, paramType), argType)) =>
                            TypeInference.unifyInfer(paramType, funSig.typeParams.toSet, argType) match {
                              case None => None
                              case Some(newSubst) if newSubst.exists((tid, _) => prevSubst.get(tid).exists(_ != tid)) => None
                              case Some(newSubst) => Some(prevSubst ++ newSubst)
                            }
                        }
                      } else None
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
                        checkTypeConstraint(paramType, argType, "function argument", posOpt)
                      }
                    }
                    substIfNeeded(funSig.retType)
                }
            }
          case _ => reportMethodNotFoundInType(receiverType.baseType, funId, posOpt)
        }
      case Select(owner, fieldName) =>
        val ownerType = computeTypes(owner)
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
              case Some(_: ClassSignature) =>
                reportError(s"field not found or not accessible in $typeName; note that class fields are always private and should be accessed from the outside through getters only", posOpt)
              case _ =>
                reportFieldNotFoundInType(ownerType.baseType, fieldName, posOpt)
            }
        }
      case HasType(formula, tpe) => ???
    }
  }

  private def checkTypeConstraint(expected: Type, actual: Type, descr: String, posOpt: Option[Position])(using Program): Unit = {
    if (!actual.baseSubtypeOf(expected)) {
      reportError(s"type mismatch on $descr: expected $expected, found $actual", posOpt)
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

  private def resolveCandidatesOp[S <: OperatorSignature](candidateOperators: List[S], op: Operator, operandsDescr: String, posOpt: Option[Position]) = {
    candidateOperators match {
      case Nil =>
        reportError(s"no operator $op found for $operandsDescr", posOpt)
      case List(opSig) => opSig.retType
      case candidates =>
        reportError(s"more than one operators $op found for $operandsDescr: " +
          "candidates are " + candidates.mkString(", "), posOpt)
    }
  }

  private def reportError(msg: String, posOpt: Option[Position]): NothingType.type = {
    er.push(Err(TypeChecking, msg, posOpt))
    NothingType
  }

  extension [T](l: Iterable[T]) private def zipCommons[U](r: Iterable[U]): Iterable[(T, U)] =
    l.take(r.size).zip(r.take(l.size))

}
