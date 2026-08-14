package compiler.reasoning

import compiler.identifiers.TypeIdentifier
import compiler.irs.ssa.Formulas.Formula
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{AnyType, IntType, NothingType, NullType}
import compiler.lang.Variance.*
import compiler.lang.{RuntimeTypeSignature, Types}
import compiler.reasoning.{Simplifier, Solver}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeParamsContext}
import compiler.util.{SeqSet, asIterableOfType}
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable
import scala.util.boundary

// TODO caching
// TODO check edge cases in join and meet computation (e.g. all types are Null/Nothing/Any)
final class MeetJoinComputer(
                              dealiasingCtx: DealiasingContext,
                              resolutionCtx: ResolutionContext,
                              subtypingCtx: SubtypingContext,
                              solver: Solver,
                              globalValuesContext: GlobalValuesContext
                            ) {

  private[reasoning] val simplifier = Simplifier(subtypingCtx, solver, dealiasingCtx, this, globalValuesContext)

  def computeJoin(types: Type*)(using TypeParamsContext): Type =
    computeJoin(Iterable.from(types))

  def computeJoin(inputTypes: Iterable[Type])(using TypeParamsContext): Type = {

    val expandedTypes = SeqSet(inputTypes.flatMap { tpe =>
      tpe.withTypeVarsExpanded match {
        case UnionType(unitedTypes) => unitedTypes
        case tpe => List(tpe)
      }
    })

    var nullableFlag = false

    val nonNullType = boundary {
      expandedTypes.size match {
        case 0 => NothingType
        case 1 => expandedTypes.head
        case _ =>
          val nonNullDealiasedTypes = expandedTypes.flatMap { rawType =>
            dealiasingCtx.dealiasType(rawType) match {
              case NullableType(nullatedType) =>
                nullableFlag = true
                Some(nullatedType)
              case NullType =>
                nullableFlag = true
                None
              case tpe => Some(tpe)
            }
          }
          nonNullDealiasedTypes.size match {
            case 0 => NullType
            case 1 => nonNullDealiasedTypes.head
            case _ => nonNullDealiasedTypes.find(superT => nonNullDealiasedTypes.forall(subtypingCtx.isSubtype(_, superT))).getOrElse {

              val namedTypes = mutable.ListBuffer.empty[NamedType]
              val closureTypes = mutable.ListBuffer.empty[ClosureType]
              val intRangeTypes = mutable.ListBuffer.empty[IntRangeType]

              val typesIter = nonNullDealiasedTypes.iterator

              def dispatch(tpe: Type): Unit = tpe match {
                case tv: TypeVariable =>
                  dispatch(tv.upperBoundOpt.getOrElse(AnyType))
                case AnyType =>
                  boundary.break(AnyType)
                case NothingType => ()
                case namedType: NamedType =>
                  namedTypes.addOne(namedType)
                case closureType: ClosureType =>
                  closureTypes.addOne(closureType)
                case intRangeType: IntRangeType =>
                  intRangeTypes.addOne(intRangeType)
                case RefinedType(baseType, predicate) =>
                  dispatch(baseType)
                case unionType: UnionType =>
                  throw AssertionError(s"unexpected ${classOf[UnionType].getSimpleName}: $unionType")
                case nullableType: NullableType =>
                  throw AssertionError(s"unexpected nullable type: $nullableType")
                case _ => ()
              }

              while (typesIter.hasNext) {
                dispatch(typesIter.next())
              }
              
              val rawJoin = {
                if namedTypes.isEmpty && intRangeTypes.isEmpty && closureTypes.isEmpty then NothingType
                else if namedTypes.isEmpty && intRangeTypes.isEmpty && closureTypes.nonEmpty then computeJoinOfClosures(closureTypes.distinct).getOrElse(AnyType)
                else if namedTypes.isEmpty && intRangeTypes.nonEmpty then computeJoinOfRanges(intRangeTypes.distinct)
                else if namedTypes.nonEmpty then computeJoinOfNamed(namedTypes.distinct).getOrElse(AnyType)
                else AnyType
              }
              
              simplifier.simplify(rawJoin)
            }
          }
      }
    }
    if nullableFlag
    then NullableType(nonNullType)
    else nonNullType
  }

  def computeJoinOfNamed(types: Iterable[NamedType])(using TypeParamsContext): Option[NamedType] = {
    val typesToSubst = Map.from(for {
      tpe@NamedType(tid, typeArgs, args) <- types
    } yield {
      tpe -> (resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](tid) match {
        case Some(tSig) =>
          tSig.typeParams.map(_.tid).zip(typeArgs).toMap
        case None =>
          Map.empty[TypeIdentifier, Type]
      })
    })
    val candidatesIdsIter = computeJoinOfTypeIds(types.map(_.typeName))
    while (candidatesIdsIter.hasNext) {
      val candidateSig = candidatesIdsIter.next()
      val candidateSubstOpt = boundary {
        val candidateSubstB = Map.newBuilder[TypeIdentifier, Type]
        for (tParam <- candidateSig.typeParams) yield {
          val instantiated = SeqSet(for ((tpe, tpeSubst) <- typesToSubst) yield {
            subtypingCtx.subToSuperSubst(tpe.typeName, candidateSig.id).get
              .apply(tParam.tid)
              .substitute(tpeSubst, Map.empty)
          })

          def checkAndSaveOrAbort(inferredTArg: Type) = {
            if (subtypingCtx.checkBounds(tParam, inferredTArg)) {
              candidateSubstB.addOne(tParam.tid -> inferredTArg)
            } else {
              boundary.break(None)
            }
          }

          tParam.variance match {
            case Invariant if instantiated.size == 1 =>
              candidateSubstB.addOne(tParam.tid -> instantiated.head)
            case Invariant => boundary.break(None)
            case Covariant =>
              checkAndSaveOrAbort(computeJoin(instantiated))
            case Contravariant =>
              checkAndSaveOrAbort(computeMeet(instantiated))
          }
        }
        Some(candidateSubstB.result())
      }
      candidateSubstOpt match {
        case Some(candidateSubst) =>
          return Some(candidateSig.toType(candidateSubst))
        case None => ()
      }
    }
    None
  }

  def computeJoinOfClosures(types: Iterable[ClosureType])(using TypeParamsContext): Option[ClosureType] = if types.isEmpty then None else {
    val paramLengthsMatch = types.map(_.params.size).toSet.size == 1
    val paramTypesMeetsB = List.newBuilder[Type]
    val paramTypesIterators = types.map(_.params.iterator)
    for (_ <- types.head.params) {
      paramTypesMeetsB.addOne(computeMeet(paramTypesIterators.map(_.next())))
    }
    val resultTypeJoin = computeJoin(types.map(_.result))
    val enforcedPure = types.forall(_.enforcedPure)
    Some(ClosureType(paramTypesMeetsB.result(), resultTypeJoin, enforcedPure))
  }

  def computeJoinOfTypeIds(types: Iterable[TypeIdentifier]): Iterator[RuntimeTypeSignature] = {
    val alreadyChecked = mutable.HashSet.empty[TypeIdentifier]
    val worklist = mutable.Queue.empty[TypeIdentifier]
    worklist.enqueueAll(types)

    enum State {
      case Unknown
      case HasNext(next: RuntimeTypeSignature)
      case Finished
    }

    import State.*
    new Iterator[RuntimeTypeSignature] {
      private var state = Unknown

      private def search(): Unit = {
        if (state != Unknown) {
          return
        }
        while (worklist.nonEmpty) {
          val curr = worklist.dequeue()
          val currSigOpt = resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](curr)
          val isValidSupertypeOfAll = currSigOpt.isDefined && types.forall(tpe => subtypingCtx.subToSuperSubst(tpe, curr).isDefined)
          alreadyChecked.add(curr)
          worklist.enqueueAll(
            currSigOpt.toList
              .flatMap(_.directSupertypes.map(_.typeName))
              .filterNot(alreadyChecked.contains)
          )
          if (isValidSupertypeOfAll) {
            state = HasNext(currSigOpt.get)
            return
          }
        }
        state = Finished
      }

      override def hasNext: Boolean = {
        search()
        state.isInstanceOf[HasNext]
      }

      override def next(): RuntimeTypeSignature = {
        search()
        state match {
          case State.HasNext(next) => next
          case _ =>
            throw new NoSuchElementException()
        }
      }
    }
  }

  def computeJoinOfRanges(types: Iterable[IntRangeType]): Type = {

    def filterNoEmpty(bounds: Iterable[Option[Formula]], minOrMax: Iterable[Formula] => Option[Formula]): Option[Formula] = {
      if bounds.isEmpty || bounds.exists(_.isEmpty) then None
      else minOrMax(bounds.flatten)
    }

    mapUnboundedToInt {
      IntRangeType(
        filterNoEmpty(types.map(_.lowerBoundOpt), solver.intMin),
        filterNoEmpty(types.map(_.upperBoundOpt), solver.intMax)
      )
    }
  }

  def computeMeet(types: Type*)(using TypeParamsContext): Type =
    computeMeet(types.toList)

  def computeMeet(types: Iterable[Type])(using TypeParamsContext): Type = {
    val expandedTypes = SeqSet(types).map(_.withTypeVarsExpanded)
    if expandedTypes.size == 1 then expandedTypes.head
    else {

      var nullableFlag = true
      var knownNullFlag = false

      val dealiasedNonNullTypes = expandedTypes.flatMap { rawType =>
        dealiasingCtx.dealiasType(rawType) match {
          case NullableType(nullatedType) =>
            Some(nullatedType)
          case NullType =>
            knownNullFlag = true
            None
          case tpe =>
            nullableFlag = false
            Some(tpe)
        }
      }
      val rawMeet = {
        if dealiasedNonNullTypes.size == 1 then dealiasedNonNullTypes.head
        else if knownNullFlag && !nullableFlag then NothingType
        else dealiasedNonNullTypes.find(subT => dealiasedNonNullTypes.forall(superT => subtypingCtx.isSubtype(subT, superT))) match {
          case Some(meet) => meet
          case None =>
            dealiasedNonNullTypes.asIterableOfType[IntRangeType] match {
              case Some(ranges) => computeMeetOfRanges(ranges)
              case None => dealiasedNonNullTypes.lastOption.getOrElse(AnyType)
            }
        }
      }
      simplifier.simplify {
        if nullableFlag
        then NullableType(rawMeet)
        else rawMeet
      }
    }
  }

  def computeMeetOfRanges(types: Iterable[IntRangeType])(using TypeParamsContext): Type = {
    val lowerBounds = solver.discardNonMax(types.flatMap(_.lowerBoundOpt))
    val upperBounds = solver.discardNonMins(types.flatMap(_.upperBoundOpt))
    val minMaxTypes = rangesFromBounds(lowerBounds, upperBounds)
    val rawMeet = IntersectionType(minMaxTypes)
    mapUnboundedToInt {
      types.find { tpe =>
        subtypingCtx.isSubtype(tpe, rawMeet) && !subtypingCtx.isSubtype(rawMeet, tpe)
      }.getOrElse(rawMeet)
    }
  }

  private def mapUnboundedToInt(tpe: Type): Type = tpe match {
    case IntRangeType(None, None) => IntType
    case tpe => tpe
  }

  private def rangesFromBounds(lowerBounds: Iterable[Formula], upperBounds: Iterable[Formula]) = {
    lowerBounds.zip(upperBounds).map(IntRangeType(_, _))
      ++ lowerBounds.drop(upperBounds.size).map(IntRangeType.ofLowerBound)
      ++ upperBounds.drop(lowerBounds.size).map(IntRangeType.ofUpperBound)
  }

}
