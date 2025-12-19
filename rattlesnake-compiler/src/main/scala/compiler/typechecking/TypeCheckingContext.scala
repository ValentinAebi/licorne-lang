package compiler.typechecking

import compiler.pipeline.CompilationStep
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typechecking.BaseSubtypeRelation.enforceBaseSubtypingConstraint
import compiler.typechecking.TypeCheckingContext.TypeInfo
import identifiers.TypeIdentifier
import lang.*
import lang.Types.*
import lang.Types.PrimitiveType.BoolType
import lang.Values.IdValue
import lang.Variance.{Contravariant, Covariant}

import scala.annotation.tailrec

// TODO refactor: see if the methods of Typer invoked from here can be moved to a separate object (and pass less givens)

final case class TypeCheckingContext(
                                      program: Program,
                                      typeTypeParams: Map[TypeIdentifier, Variance],
                                      functionTypeParams: Set[TypeIdentifier],
                                      typeInfos: Map[IdValue, TypeInfo],
                                      thisVal: IdValue,
                                      ownerId: TypeIdentifier,
                                      alwaysExitsFlag: Boolean,
                                      expectedReturnType: Type
                                    )(using typer: Typer, ts: MutableTypeStore) {

  private given TypeCheckingContext = this

  private given Program = program

  def copyForClosureBody(expectedResultType: Type): TypeCheckingContext =
    copy(alwaysExitsFlag = false, expectedReturnType = expectedResultType)

  def varianceOf(tpe: BaseType): Option[Variance] = tpe match {
    case NamedType(typeName, Nil, Nil) => typeTypeParams.get(typeName)
    case _ => None
  }

  def checkType(tpe: Type, expVarianceOpt: Option[Variance], posOpt: Option[Position])
               (using er: ErrorReporter, compilationStep: CompilationStep): Unit = tpe match {
    case Types.RefinedType(baseType, itValue, predicate) =>
      checkType(baseType, expVarianceOpt, posOpt)
      ts(itValue) = baseType
      val predType = typer.computeType(predicate)
      enforceBaseSubtypingConstraint(predType, BoolType)(using "type predicate", posOpt)
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
            args.foreach(typer.computeType(_))
          case Some(sig) =>
            if (typeArgs.size == sig.typeParams.size) {
              for (((typeParam, typeParamVariance), typeArg) <- sig.typeParams zip typeArgs) {
                checkType(typeArg, expVarianceOpt.map(_ * typeParamVariance), posOpt)
              }
            }
            typer.generateTypeParamsMapping(sig.typeParams.map(_._1), typeArgs, posOpt, s"tapp_${sig.id}", reportIfLengthMismatch = true).foreach { typeParamsSubst =>
              val expParamsCnt = sig.params.size
              if (args.size == expParamsCnt) {
                for (((paramId, (paramTypeRaw, paramValue)), arg) <- sig.params zip args) {
                  val paramType = program.desugarType(paramTypeRaw.substitute(typeParamsSubst, Map.empty))
                  val argType = typer.computeType(arg)
                  enforceBaseSubtypingConstraint(argType, paramType)(using "type application", posOpt)
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

  def withTypeInfoRefined(newTypeInfosSet: Set[TypeInfo]): TypeCheckingContext = {
    var alwaysExits = alwaysExitsFlag
    val newTypeInfosMap = for ((idValue, allInfos) <- (typeInfos.values.toSet ++ newTypeInfosSet).groupBy(_.value)) yield {
      val knownIs = allInfos.flatMap(_.knownIs)
      val knownIsNot = allInfos.flatMap(_.knownIsNot)
      val info = TypeInfo(idValue, allInfos.head.tpe, knownIs, knownIsNot)
      alwaysExits |= info.mostPreciseType(using program).isEmpty
      idValue -> info
    }
    copy(typeInfos = newTypeInfosMap, alwaysExitsFlag = alwaysExits)
  }

  def withAlwaysExitsFlagRecomputed(using program: Program): TypeCheckingContext = {
    if alwaysExitsFlag then this
    else {
      val iter = typeInfos.iterator
      while (iter.hasNext) {
        val (_, typeInfo) = iter.next()
        if (typeInfo.mostPreciseType.isEmpty) {
          return copy(alwaysExitsFlag = true)
        }
      }
      this
    }
  }

  def withAlwaysExitsFlagRaised: TypeCheckingContext = copy(alwaysExitsFlag = true)

  def inferredTypeFor(idValue: IdValue): Option[TypeIdentifier] =
    typeInfos.get(idValue).flatMap(_.mostPreciseType(using program))

  private def reportError(msg: String, posOpt: Option[Position])(using er: ErrorReporter, compilationStep: CompilationStep): Unit = {
    er.push(Err(compilationStep, msg, posOpt))
  }

}

object TypeCheckingContext {

  final case class TypeInfo(value: IdValue, tpe: TypeIdentifier, knownIs: Set[TypeIdentifier], knownIsNot: Set[TypeIdentifier]) {

    def mergedWith(that: TypeInfo): TypeInfo = {
      require(this.value == that.value)
      require(this.tpe == that.tpe)
      TypeInfo(value, tpe, this.knownIs ++ that.knownIs, this.knownIsNot ++ that.knownIsNot)
    }

    /**
     * @return None if all possible types were excluded (in the typical context this implies that we are in an unreachable branch)
     */
    def mostPreciseType(using program: Program): Option[TypeIdentifier] = {

      @tailrec def narrowDown(front: Set[TypeIdentifier], oldLastBottleneck: TypeIdentifier): Option[TypeIdentifier] = {
        val lastBottleneck = if front.size == 1 then front.head else oldLastBottleneck
        val narrowed = (front -- knownIsNot).flatMap {
          program.resolveSignature(_) match {
            case Some(datatypeSignature: DatatypeSignature) => datatypeSignature.directSubtypes
            case Some(recordSignature: RecordSignature) => Set(recordSignature.id)
            case _ => front
          }
        }
        if narrowed.isEmpty then None
        else if narrowed == front then Some(lastBottleneck)
        else narrowDown(narrowed, lastBottleneck)
      }

      val startFront = if knownIs.isEmpty then Set(tpe) else knownIs
      narrowDown(startFront, tpe)
    }

  }

}
