package compiler.typing

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.Formula
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{AnyType, NothingType}
import compiler.smt.Solver
import compiler.typing.contexts.{DealiasingContext, SubtypingContext}
import compiler.util.SeqSet

import scala.collection.mutable

final class MeetJoinComputer(
                              dealiasingCtx: DealiasingContext,
                              subtypingCtx: SubtypingContext,
                              solver: Solver
                            ) {

  def dealiasAndComputeJoin(types: Type*): Type =
    dealiasAndComputeJoin(Iterable.from(types))

  def computeJoin(types: Type*): Type =
    computeJoin(Iterable.from(types))

  def dealiasAndComputeJoin(types: Iterable[Type]): Type =
    computeJoin(types.map(dealiasingCtx.dealiasType))

  def computeJoin(inputTypes: Iterable[Type]): Type = {

    // first pass: flatten UnionTypes and remove duplicates
    val expandedTypes = SeqSet(inputTypes.flatMap {
      case UnionType(unitedTypes) => unitedTypes
      case tpe => List(tpe)
    })

    expandedTypes.size match {
      case 0 => NothingType
      case 1 => expandedTypes.head
      case _ =>

        // second pass: remove Nothing, shortcut if Any
        val primitiveTypes = mutable.ListBuffer.empty[PrimitiveType]
        val namedTypes = mutable.ListBuffer.empty[NamedType]
        val closureTypes = mutable.ListBuffer.empty[ClosureType]
        val rangeTypes = mutable.ListBuffer.empty[IntRangeType]

        def categorizeType(tpe: Type): Unit = tpe match {
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
            for {
              tpe <- types
              if tpe != NothingType
            } {
              categorizeType(tpe)
            }
          case intRangeType: IntRangeType =>
            rangeTypes.addOne(intRangeType)
        }

        // third pass: categorize types
        var retainedTypesCnt = 0
        val typesIter = expandedTypes.iterator
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

        if namedTypes.size == retainedTypesCnt then computeJoinOfNamed(namedTypes.distinct)
        else if rangeTypes.size == retainedTypesCnt then computeJoinOfRanges(rangeTypes.distinct)
        else if primitiveTypes.size == retainedTypesCnt then computeJoinOfPrimitives(primitiveTypes)
        else if closureTypes.size == retainedTypesCnt then computeJoinOfClosures(closureTypes.distinct).getOrElse(AnyType)
        else AnyType
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

  def computeJoinOfNamed(types: Iterable[NamedType]): NamedType = {
    ???
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

  def computeJoinOfTypeIds(types: Iterable[TypeIdentifier]): Option[TypeIdentifier] = {
    ???
  }

  def computeJoinOfRanges(types: Iterable[IntRangeType]): IntRangeType = IntRangeType(
    filterNoEmpty(types.map(_.lowerBoundOpt), solver.intMin),
    filterNoEmpty(types.map(_.upperBoundOpt), solver.intMax)
  )

  def computeMeet(types: Iterable[Type]): Type = ???

  def computeMeetOfNamed(types: Iterable[NamedType]): Type = ???

  def computeMeetOfTypeIds(types: Iterable[TypeIdentifier]): Option[TypeIdentifier] = ???

  def computeMeetOfClosures(types: Iterable[ClosureType]): Type = ???

  def computeMeetOfRanges(types: Iterable[IntRangeType]): IntRangeType = IntRangeType(
    filterNoEmpty(types.map(_.lowerBoundOpt), solver.intMax),
    filterNoEmpty(types.map(_.upperBoundOpt), solver.intMin)
  )

  private def filterNoEmpty(bounds: Iterable[Option[Formula]], minOrMax: Iterable[Formula] => Option[Formula]): Option[Formula] = {
    if bounds.isEmpty || bounds.exists(_.isEmpty) then None
    else minOrMax(bounds.flatten)
  }

}
