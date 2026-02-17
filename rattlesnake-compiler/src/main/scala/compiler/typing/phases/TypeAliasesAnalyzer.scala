package compiler.typing.phases

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.lang.{Formulas, Types}
import compiler.lang.Types.*
import compiler.pipeline.CompilationStep.TypeAliasesAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, TypeParamsContext, TypeVariablesContext}

final class TypeAliasesAnalyzer(er: ErrorReporter, typeVarsCtx: TypeVariablesContext) extends CompilerStep[Program, Program] {
  
  private given CompilationStep = TypeAliasesAnalysis

  override def apply(program: Program): Program = {
    checkTypeAliasesCyclicity(program, ResolutionContext.fromProgram(program))
    er.displayAndTerminateIfErrors()

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val typer = Typer(dealiasingCtx, ResolutionContext.fromProgram(program), typeVarsCtx, er)
    val typedAliasesDefinitions = program.typeAliases.map { (tid, tsig) =>
      val typeParamsCtx = TypeParamsContext(tsig.typeParams)
      val typedRhs = typer.dealiasAndTypeType(tsig.rhs, None, tsig.declPosOpt)(using typeParamsCtx)
      tid -> tsig.copy(rhs = typedRhs)
    }
    program.copy(typeAliases = typedAliasesDefinitions)
  }

  private def checkTypeAliasesCyclicity(program: Program, resolutionCtx: ResolutionContext): Unit = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for ((id, sig) <- program.typeAliases) {
      val rhsFreeTypes = findMentionedTypes(sig.rhs) -- sig.typeParams.map(_._1)
      graphB.addDescendants(id, rhsFreeTypes)
    }
    graphB.build().findShortestCycle().foreach { cycle =>
      resolutionCtx.resolveTypeSig(cycle.head).foreach { sig =>
        er.reportError("cyclic dependencies between the following type aliases: " ++ cycle.mkString(" -> "), sig.declPosOpt)
      }
    }
  }

  private def findMentionedTypes(tpe: Type): Set[TypeIdentifier] = tpe match {
    case primitiveType: Types.PrimitiveType => Set.empty
    case NamedType(typeName, typeParams, params) =>
      Set(typeName) ++ typeParams.flatMap(findMentionedTypes) ++ params.flatMap(findMentionedTypes)
    case _: TypeVariable => Set.empty
    case UnionType(types) =>
      types.flatMap(findMentionedTypes)
    case IntersectionType(types) =>
      types.flatMap(findMentionedTypes)
    case ClosureType(params, resultType) =>
      params.flatMap(findMentionedTypes).toSet ++ findMentionedTypes(resultType)
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      lowerBoundOpt.toSet.flatMap(findMentionedTypes) ++ upperBoundOpt.toSet.flatMap(findMentionedTypes)
  }

  private def findMentionedTypes(formula: Formula): Set[TypeIdentifier] = formula match {
    case value: Formulas.Value => Set.empty
    case op: Formulas.BinOp => findMentionedTypes(op.lhs) ++ findMentionedTypes(op.rhs)
    case op: Formulas.UnaryOp => findMentionedTypes(op.operand)
    case Formulas.Call(receiver, funId, typeArgs, args) => findMentionedTypes(receiver) ++ typeArgs.flatMap(findMentionedTypes) ++ args.flatMap(findMentionedTypes)
    case Formulas.Select(owner, fieldName) => findMentionedTypes(owner)
    case Formulas.HasType(formula, tpe) => findMentionedTypes(formula) + tpe
  }

}
