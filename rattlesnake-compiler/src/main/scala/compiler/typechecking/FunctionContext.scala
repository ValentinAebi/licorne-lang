package compiler.typechecking

import compiler.pipeline.CompilationStep
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.enforceExpectedBaseSubtypingConstraint
import identifiers.TypeIdentifier
import lang.*
import lang.Types.*
import lang.Types.PrimitiveType.BoolType
import lang.Values.IdValue
import lang.Variance.{Contravariant, Covariant}

import scala.annotation.tailrec

// TODO refactor: see if the methods of Typer invoked from here can be moved to a separate object (and pass less givens)

final case class FunctionContext(
                                      program: Program,
                                      typeTypeParams: Map[TypeIdentifier, TypeTypeParamInfo],
                                      functionTypeParams: Map[TypeIdentifier, FunctionTypeParamInfo],
                                      thisVal: IdValue,
                                      ownerId: TypeIdentifier,
                                      expectedReturnType: Type
                                    )(using typer: Typer, ts: TypeStore) {

  private given FunctionContext = this

  private given Program = program

  def copyForClosureBody(expectedResultType: Type): FunctionContext =
    copy(expectedReturnType = expectedResultType)

  def varianceOf(tpe: BaseType): Option[Variance] = tpe match {
    case NamedType(typeName, Nil, Nil) => typeTypeParams.get(typeName).map(_.variance)
    case _ => None
  }

  def checkType(tpe: Type, expVarianceOpt: Option[Variance], posOpt: Option[Position])
               (using er: ErrorReporter, compilationStep: CompilationStep): Unit = tpe match {
    case Types.RefinedType(baseType, itValue, predicate) =>
      checkType(baseType, expVarianceOpt, posOpt)
      ts(itValue) = baseType
      val (predType, _) = typer.analyze(predicate, ControlFlowInfo.empty)
      enforceExpectedBaseSubtypingConstraint(predType, BoolType)(using "type predicate", posOpt)
    case primitiveType: Types.PrimitiveType => ()
    case tpe@NamedType(typeName, typeArgs, args) =>
      if (functionTypeParams.contains(typeName) || typeTypeParams.contains(typeName)) {
        if (typeArgs.nonEmpty || args.nonEmpty) {
          reportError(s"type parameters cannot take parameters: $tpe", posOpt)
        }
        for {
          expVariance <- expVarianceOpt
          actVariance <- varianceOf(tpe)
          if !actVariance.isAssignableTo(expVariance)
        } {
          reportError(s"variance error: $actVariance type parameter $typeName in $expVariance position", posOpt)
        }
      } else {
        program.resolveSignature(typeName) match {
          case None =>
            reportError(s"type not found: $typeName", posOpt)
            args.foreach(typer.analyze(_, ControlFlowInfo.empty))
          case Some(sig) =>
            if (typeArgs.size == sig.typeParams.size) {
              for ((TypeTypeParamInfo(typeParam, typeParamVariance, upperBounds, lowerBounds), typeArg) <- sig.typeParams zip typeArgs) {
                checkType(typeArg, expVarianceOpt.map(_ * typeParamVariance), posOpt)
              }
            }
            typer.generateTypeParamsMapping(sig.typeParams, typeArgs, posOpt, s"tapp_${sig.id}", reportIfLengthMismatch = true).foreach { typeParamsSubst =>
              val expParamsCnt = sig.params.size
              if (args.size == expParamsCnt) {
                for (((paramId, (paramTypeRaw, paramValue)), arg) <- sig.params zip args) {
                  val paramType = program.desugarType(paramTypeRaw.substitute(typeParamsSubst, Map.empty))
                  val (argType, _) = typer.analyze(arg, ControlFlowInfo.empty)
                  enforceExpectedBaseSubtypingConstraint(argType, paramType)(using "type application", posOpt)
                }
              } else {
                reportError(s"wrong number of arguments: expected $expParamsCnt, found ${args.size}", posOpt)
              }
            }
        }
      }
    case ClosureType(params, resultType) =>
      for (paramType <- params) {
        checkType(paramType, expVarianceOpt.map(_ * Contravariant), posOpt)
      }
      checkType(resultType, expVarianceOpt.map(_ * Covariant), posOpt)
    case _: (UnionType | BaseUnionType | TypeVariable) =>
      assert(false)
  }

  private def reportError(msg: String, posOpt: Option[Position])(using er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    er.report(Err(compilationStep, msg, posOpt))
  }

}
