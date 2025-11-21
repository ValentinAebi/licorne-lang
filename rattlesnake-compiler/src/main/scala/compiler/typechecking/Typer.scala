package compiler.typechecking

import compiler.analysisctx.AnalysisContext
import compiler.irs.SSA
import compiler.irs.SSA.Instr
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.ErrorReporter
import lang.Types.PrimitiveType.*
import lang.{FunctionSignature, Operators, Values}
import lang.Types.Type
import lang.Values.*

import scala.collection.mutable

final class Typer(private val er: ErrorReporter) extends CompilerStep[(Map[FunctionSignature, SSA.Function], AnalysisContext), (Map[FunctionSignature, SSA.Function], AnalysisContext, TypeStore)] {

  override def apply(input: (Map[FunctionSignature, SSA.Function], AnalysisContext)): (Map[FunctionSignature, SSA.Function], AnalysisContext, TypeStore) = {
    val (functions, analysisCtx) = input
    
    ??? // TODO
  }
  
  private def traverse(instr: Instr)(using ts: TypeStore, constraintsList: mutable.ListBuffer[Constraint]): Unit = instr match {
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
  
  private def computeTypes(formula: Formula)(using ts: TypeStore, constraintsList: mutable.ListBuffer[Constraint]): Type = formula match {
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
      Operators.binaryOperators.find { opSig =>
        ??? // TODO
      }
      ??? // TODO
    case op: UnaryOp => ???
    case Call(receiver, funId, args) => ???
    case Select(owner, fieldName) => ???
    case HasType(formula, tpe) => ???
  }
  
}
