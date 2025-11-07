package compiler.ssagen

import compiler.irs.Asts.NonFormulaExpr
import compiler.irs.{Asts, SSA}
import compiler.irs.SSA.Instr
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.valuesconversion.{LocalValuesContext, ValuesGenerator}
import identifiers.FunOrVarId
import lang.Values.{Formula, Value}

import scala.collection.mutable

sealed trait ExpressionsGenerationMode {
  
  def generateNonFormulaExpr(nonFormulaExpr: NonFormulaExpr, valsCtx: LocalValuesContext): Formula
  
}

final class FormulasGenerationMode(private val er: ErrorReporter) extends ExpressionsGenerationMode {
  
  override def generateNonFormulaExpr(nonFormulaExpr: NonFormulaExpr, valsCtx: LocalValuesContext): Formula = {
    er.push(Err(SSAGeneration, "illegal expression: only formulas are allowed at this position", nonFormulaExpr.getPosition))
    valsCtx.valuesGen.newIllegalConstruct(nonFormulaExpr)
  }
  
}

final class GeneralExpressionsGenerationMode(private val ssaInstructionsList: mutable.ListBuffer[Instr]) extends ExpressionsGenerationMode {
  
  override def generateNonFormulaExpr(nonFormulaExpr: NonFormulaExpr, valsCtx: LocalValuesContext): Formula = nonFormulaExpr match {
    case Asts.FilledArrayInit(arrayElems) => ???
    case Asts.StructOrClassInstantiation(typeId, initializers) => ???
    case Asts.Ternary(cond, thenBr, elseBr) => ???
    case Asts.Cast(expr, tpe) => ???
  }

  private def saveInstr(instr: SSA.Instr, node: Asts.Ast): Unit = {
    instr.setAstNode(node.originalAst)
    ssaInstructionsList.addOne(instr)
  }
  
}
