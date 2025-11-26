package compiler.typechecking

import compiler.program.Program
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import identifiers.TypeIdentifier
import lang.Types.*
import lang.Values.{And, Formula}
import lang.{TypeAliasSignature, Types, Values, Variance}

final class TypeCheckingContext(
                                 val program: Program,
                                 val typeTypeParams: Map[TypeIdentifier, Variance],
                                 val functionTypeParams: Set[TypeIdentifier]
                               ) {

  def desugarType(tpe: Type): Type = {
    val desugaredType = tpe match {
      case RefinedType(baseTypeRaw, itValueRaw, predicateRaw) =>
        desugarType(baseTypeRaw) match {
          case RefinedType(baseTypeDes, itValueDes, predicateDes) =>
            RefinedType(baseTypeDes, itValueRaw, And(predicateRaw, predicateDes.substitute(Map.empty, Map(itValueDes -> itValueRaw))))
          case baseTypeDes: BaseType =>
            RefinedType(baseTypeDes, itValueRaw, predicateRaw)
        }
      case primitiveType: Types.PrimitiveType => primitiveType
      case Types.NamedType(typeName, typeArgs, args) =>
        program.typeAliases.get(typeName) match {
          case Some(TypeAliasSignature(id, typeParams, thisValue, params, rhs)) =>
            val typesSubst = typeParams.map((id, variance) => id).zipCommons(typeArgs).toMap
            val valsSubst = params.map {
              case (paramId, (paramType, paramVal)) => paramVal
            }.zipCommons(args).toMap
            rhs.substitute(typesSubst, valsSubst)
          case None => tpe
        }
      case typeVar: Types.TypeVar => typeVar
    }
    if desugaredType == tpe then tpe
    else desugarType(desugaredType)
  }

  def checkTypesWellDefined(tpe: Type, posOpt: Option[Position])(using tcCtx: TypeCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = tpe match {
    case Types.RefinedType(baseType, itValue, predicate) =>
      checkTypesWellDefined(baseType, posOpt)
      checkTypesWellDefined(predicate, posOpt)
    case typeVar: Types.TypeVar =>
      throw AssertionError("should not happen: unexpected type variable")
    case primitiveType: Types.PrimitiveType => ()
    case NamedType(typeName, typeArgs, args) =>
      if (!functionTypeParams.contains(typeName) && !typeTypeParams.contains(typeName)) {
        program.resolveSignature(typeName) match {
          case None =>
            er.reportError(s"type not found: $typeName", posOpt)
          case Some(sig) =>
            val expTypeParamsCnt = sig.typeParams.size
            if (typeArgs.size == expTypeParamsCnt) {
              for (((typeParam, paramVariance), typeArg) <- sig.typeParams.zip(typeArgs)) {
                tcCtx.varianceOf(typeArg.baseType).foreach { argVariance =>
                  if (!argVariance.isAssignableTo(paramVariance)) {
                    er.reportError(s"variance error: cannot instantiate type parameter $typeParam of $typeName to type parameter $typeArg", posOpt)
                  }
                }
              }
            } else {
              er.reportError(s"expected ${singOrPlural(expTypeParamsCnt, "type parameter", "type parameters")}, found ${typeArgs.size}", posOpt)
            }
            val expParamsCnt = sig.params.size
            if (args.size != expParamsCnt) {
              er.reportError(s"expected ${singOrPlural(expParamsCnt, "parameter", "parameters")}, found ${typeArgs.size}", posOpt)
            }
        }
        typeArgs.foreach(checkTypesWellDefined(_, posOpt))
        args.foreach(checkTypesWellDefined(_, posOpt))
      }
  }

  def varianceOf(tpe: BaseType): Option[Variance] = tpe match {
    case NamedType(typeName, Nil, Nil) => typeTypeParams.get(typeName)
    case _ => None
  }

  private def singOrPlural(cnt: Int, sing: String, plur: String): String =
    if cnt == 0 || cnt == 1 then s"$cnt $sing"
    else s"$cnt $plur"

  private def checkTypesWellDefined(formula: Formula, posOpt: Option[Position])(using tcCtx: TypeCheckingContext, er: ErrorReporter, compilationStep: CompilationStep): Unit = formula match {
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
      checkTypesWellDefined(tpe, posOpt)
  }

  extension (er: ErrorReporter) private def reportError(msg: String, posOpt: Option[Position])(using compilationStep: CompilationStep): Unit = {
    er.push(Err(compilationStep, msg, posOpt))
  }

  extension [T](l: Iterable[T]) private def zipCommons[U](r: Iterable[U]): Iterable[(T, U)] =
    l.take(r.size).zip(r.take(l.size))

}
