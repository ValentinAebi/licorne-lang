package compiler.smt

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{AnyType, IntType, NothingType}
import compiler.lang.Variance.*
import compiler.lang.{RuntimeTypeSignature, TypeTypeParamInfo, Types}
import compiler.smt.{Simplifier, Solver}
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext}
import compiler.util.{SeqSet, asIterableOfType, zipCommons}

import scala.collection.mutable
import scala.util.boundary

// TODO caching
final class MeetJoinComputer(
                              dealiasingCtx: DealiasingContext,
                              resolutionCtx: ResolutionContext,
                              subtypingCtx: SubtypingContext,
                              solver: Solver
                            ) {

  private[smt] val simplifier = Simplifier(subtypingCtx, solver, dealiasingCtx, this)

  def computeJoin(types: Type*): Type =
    computeJoin(Iterable.from(types))

  def computeJoin(inputTypes: Iterable[Type]): Type = {

    // first pass: flatten UnionTypes and remove duplicates
    val expandedTypes = SeqSet(inputTypes.flatMap { tpe =>
      tpe.withTypeVarsExpanded match {
        case UnionType(unitedTypes) => unitedTypes
        case tpe => List(tpe)
      }
    })

    expandedTypes.size match {
      case 0 => NothingType
      case 1 => expandedTypes.head
      case _ =>
        val dealiasedTypes = expandedTypes.map(dealiasingCtx.dealiasType)
        dealiasedTypes.size match {
          case 0 => NothingType
          case 1 => dealiasedTypes.head
          case _ =>

            // second pass: remove Nothing, shortcut if Any
            val primitiveTypes = mutable.ListBuffer.empty[PrimitiveType]
            val namedTypes = mutable.ListBuffer.empty[NamedType]
            val closureTypes = mutable.ListBuffer.empty[ClosureType]
            val rangeTypes = mutable.ListBuffer.empty[IntRangeType]

            def categorizeType(tpe: Type): Unit = tpe match {
              case IntType =>
                primitiveTypes.addOne(IntType)
                rangeTypes.addOne(IntRangeType(None, None))
              case primitiveType: PrimitiveType =>
                primitiveTypes.addOne(primitiveType)
              case namedType: NamedType =>
                namedTypes.addOne(namedType)
              case closureType: ClosureType =>
                closureTypes.addOne(closureType)
              case tv: TypeVariable =>
                throw AssertionError(s"unexpected type variable: $tv")
              case unionType: UnionType =>
                throw AssertionError(s"unexpected ${classOf[UnionType].getSimpleName}: $unionType")
              case IntersectionType(types) =>
                for (tpe <- types) {
                  categorizeType(tpe)
                }
              case intRangeType: IntRangeType =>
                rangeTypes.addOne(intRangeType)
            }

            // third pass: categorize types
            var retainedTypesCnt = 0
            val typesIter = dealiasedTypes.iterator
            while (typesIter.hasNext) {
              typesIter.next() match {
                case (_: TypeVariable) | AnyType =>
                  return AnyType
                case NothingType => ()
                case tpe =>
                  categorizeType(tpe)
                  retainedTypesCnt += 1
              }
            }

            val rawJoin =
              if namedTypes.size >= retainedTypesCnt then computeJoinOfNamed(namedTypes.distinct).getOrElse(AnyType)
              else if rangeTypes.size >= retainedTypesCnt then computeJoinOfRanges(rangeTypes.distinct)
              else if primitiveTypes.size >= retainedTypesCnt then computeJoinOfPrimitives(primitiveTypes)
              else if closureTypes.size >= retainedTypesCnt then computeJoinOfClosures(closureTypes.distinct).getOrElse(AnyType)
              else AnyType
            simplifier.simplify(rawJoin)
        }
    }
  }

  def computeJoinOfPrimitives(types: Iterable[PrimitiveType]): PrimitiveType = {
    val remTypes = mutable.LinkedHashSet.from(types)
    remTypes.remove(NothingType)
    remTypes.size match {
      case 0 => NothingType
      case 1 => remTypes.head
      case _ => AnyType
    }
  }

  def computeJoinOfNamed(types: Iterable[NamedType]): Option[NamedType] = {
    val typesToSubst = Map.from(for {
      tpe@NamedType(tid, typeArgs, args) <- types
    } yield {
      tpe -> (resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](tid) match {
        case Some(tSig) =>
          tSig.typeParams.map(_.tid).zipCommons(typeArgs).toMap
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

  def computeJoinOfClosures(types: Iterable[ClosureType]): Option[ClosureType] = if types.isEmpty then None else {
    val paramLengthsMatch = types.map(_.params.size).toSet.size == 1
    val paramTypesMeetsB = List.newBuilder[Type]
    val paramTypesIterators = types.map(_.params.iterator)
    for (_ <- types.head.params) {
      paramTypesMeetsB.addOne(computeMeet(paramTypesIterators.map(_.next())))
    }
    val resultTypeJoin = computeJoin(types.map(_.result))
    Some(ClosureType(paramTypesMeetsB.result(), resultTypeJoin))
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

  def computeMeet(types: Type*): Type =
    computeMeet(types.toList)

  def computeMeet(types: Iterable[Type]): Type = {
    val expandedTypes = SeqSet(types).map(_.withTypeVarsExpanded)
    if expandedTypes.size == 1 then expandedTypes.head
    else {
      val dealiasedTypes = expandedTypes.map(dealiasingCtx.dealiasType)
      val rawMeet =
        if dealiasedTypes.size == 1 then dealiasedTypes.head
        else dealiasedTypes.find(subT => dealiasedTypes.forall(superT => subtypingCtx.isSubtype(subT, superT))) match {
          case Some(meet) => meet
          case None =>
            dealiasedTypes.asIterableOfType[IntRangeType] match {
              case Some(ranges) => computeMeetOfRanges(ranges)
              case None => dealiasedTypes.lastOption.getOrElse(AnyType)
            }
        }
      simplifier.simplify(rawMeet)
    }
  }

  def computeMeetOfRanges(types: Iterable[IntRangeType]): Type = {

    def filterNoEmpty(bounds: Iterable[Option[Formula]], minOrMax: Iterable[Formula] => Option[Formula]): Option[Formula] = {
      if bounds.isEmpty || bounds.forall(_.isEmpty) then None
      else minOrMax(bounds.flatten)
    }

    val rawMeet = IntRangeType(
      filterNoEmpty(types.map(_.lowerBoundOpt), solver.intMax),
      filterNoEmpty(types.map(_.upperBoundOpt), solver.intMin)
    )
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

}
