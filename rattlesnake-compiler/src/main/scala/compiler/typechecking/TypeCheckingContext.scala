package compiler.typechecking

import compiler.program.Program
import compiler.typechecking.TypeCheckingContext.TypeInfo
import identifiers.TypeIdentifier
import lang.Types.Type
import lang.Values.IdValue
import lang.{DatatypeSignature, RecordSignature}

import scala.annotation.tailrec
import scala.util.boundary

final case class TypeCheckingContext(
                                      program: Program,
                                      typeInfos: Map[IdValue, TypeInfo],
                                      thisVal: IdValue,
                                      alwaysExitsFlag: Boolean,
                                      expectedReturnType: Type
                                    ) {

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
            case _ => Set.empty
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
