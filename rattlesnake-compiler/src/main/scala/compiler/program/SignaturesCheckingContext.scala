package compiler.program

import compiler.pipeline.CompilationStep
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import identifiers.TypeIdentifier
import lang.Types.*
import lang.Values.Formula
import lang.{RuntimeTypeSignature, Types, Values, Variance}

final class SignaturesCheckingContext(
                                 val program: Program,
                                 val typeTypeParams: Map[TypeIdentifier, Variance],
                                 val functionTypeParams: Set[TypeIdentifier]
                               ) {

  def varianceOf(tpe: BaseType): Option[Variance] = tpe match {
    case NamedType(typeName, Nil, Nil) => typeTypeParams.get(typeName)
    case _ => None
  }

  def checkTypesWellDefined(tpe: Type, expVarianceOpt: Option[Variance], posOpt: Option[Position])(using tcCtx: SignaturesCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = tpe match {
    case Types.RefinedType(baseType, itValue, predicate) =>
      checkTypesWellDefined(baseType, expVarianceOpt, posOpt)
      checkTypesWellDefined(predicate, posOpt)
    case primitiveType: Types.PrimitiveType => ()
    case tpe@NamedType(typeName, typeArgs, args) =>
      if (functionTypeParams.contains(typeName) || typeTypeParams.contains(typeName)) {
        if (typeArgs.nonEmpty || args.nonEmpty) {
          er.reportError(s"type parameters cannot take parameters: $tpe", posOpt)
        }
        for {
          expVariance <- expVarianceOpt
          actVariance <- tcCtx.varianceOf(tpe)
          if !actVariance.isAssignableTo(expVariance)
        } {
          er.reportError(s"variance error: $actVariance type parameter $typeName in $expVariance position", posOpt)
        }
      } else {
        program.resolveSignature(typeName) match {
          case None =>
            er.reportError(s"type not found: $typeName", posOpt)
          case Some(sig) =>
            val expTypeParamsCnt = sig.typeParams.size
            if (typeArgs.size == expTypeParamsCnt) {
              for (((typeParam, typeParamVariance), typeArg) <- sig.typeParams zip typeArgs) {
                checkTypesWellDefined(typeArg, expVarianceOpt.map(_ * typeParamVariance), posOpt)
              }
            } else {
              er.reportError(s"expected ${singOrPlural(expTypeParamsCnt, "type parameter", "type parameters")}, found ${typeArgs.size}", posOpt)
              typeArgs.foreach(checkTypesWellDefined(_, None, posOpt))
            }
            val expParamsCnt = sig.params.size
            if (args.size != expParamsCnt) {
              er.reportError(s"expected ${singOrPlural(expParamsCnt, "parameter", "parameters")}, found ${typeArgs.size}", posOpt)
            }
        }
        args.foreach(checkTypesWellDefined(_, posOpt))
      }
  }

  private def checkTypesWellDefined(formula: Formula, posOpt: Option[Position])(using tcCtx: SignaturesCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = formula match {
    case _: Values.Value => ()
    case op: Values.BinOp =>
      checkTypesWellDefined(op.lhs, posOpt)
      checkTypesWellDefined(op.rhs, posOpt)
    case op: Values.UnaryOp =>
      checkTypesWellDefined(op.operand, posOpt)
    case Values.Call(receiver, funId, args) =>
      checkTypesWellDefined(receiver, posOpt)
      args.foreach(checkTypesWellDefined(_, posOpt))
    case Values.Select(owner, fieldName) => checkTypesWellDefined(owner, posOpt)
    case Values.HasType(formula, tpe) =>
      checkTypesWellDefined(formula, posOpt)
      if (tcCtx.program.resolveSignatureAs[RuntimeTypeSignature](tpe).isEmpty){
        er.reportError(s"unknown runtime type: $tpe", posOpt)
      }
  }

  private def singOrPlural(cnt: Int, sing: String, plur: String): String =
    if cnt == 0 || cnt == 1 then s"$cnt $sing"
    else s"$cnt $plur"

  extension (er: ErrorReporter) private def reportError(msg: String, posOpt: Option[Position])(using compilationStep: CompilationStep): Unit = {
    er.push(Err(compilationStep, msg, posOpt))
  }

}
