package compiler.typechecking

import compiler.irs.SSA
import compiler.irs.SSA.Instr
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.baseSubtypeOf
import lang.Operators.OperatorSignature
import lang.Types.PrimitiveType.*
import lang.Types.Type
import lang.Values.*
import lang.{FunctionSignature, Operator, Operators, Values}

final class Typer(private val er: ErrorReporter) extends CompilerStep[(Map[FunctionSignature, SSA.Function], Program), (Map[FunctionSignature, SSA.Function], Program, TypeStore)] {

  override def apply(input: (Map[FunctionSignature, SSA.Function], Program)): (Map[FunctionSignature, SSA.Function], Program, TypeStore) = {
    val (functions, program) = input

    ??? // TODO
  }

  private def traverse(instr: Instr)(using ts: PartialTypeStore, program: Program, thisId: IdValue): Unit = {
    given Option[Position] = instr.getAstNodeOpt.flatMap(_.getPosition)

    instr match {
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
  }

  private def computeTypes(formula: Formula)
                          (using ts: TypeStore, program: Program, posOpt: Option[Position], thisId: IdValue): Type = formula match {
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
    case Call(receiver, funId, args) => ???
    case Select(owner, fieldName) if owner == thisId => ???
    case Select(owner, fieldName) => ???
    case HasType(formula, tpe) => ???
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

}
