package compiler.typechecking

import compiler.program.Program
import compiler.typechecking.ControlFlowInfo.{TypeInfo, exited}
import identifiers.TypeIdentifier
import lang.{DatatypeSignature, RecordSignature}
import lang.Values.IdValue

import scala.annotation.tailrec
import scala.util.boundary

final case class ControlFlowInfo private(private val typeInfosOpt: Option[Map[IdValue, TypeInfo]]) {

  def refined(newTypeInfosSet: Iterable[TypeInfo])(using program: Program): ControlFlowInfo = typeInfosOpt match {
    case None => this
    case Some(typeInfos) => boundary {
      val allTypeInfos = for ((idValue, allInfos) <- (typeInfos.values.toSet ++ newTypeInfosSet).groupBy(_.value)) yield {
        val knownIs = allInfos.flatMap(_.knownIs)
        val knownIsNot = allInfos.flatMap(_.knownIsNot)
        val info = TypeInfo(idValue, allInfos.head.tpe, knownIs, knownIsNot)
        if (info.mostPreciseType(using program).isEmpty) {
          boundary.break(exited)
        }
        idValue -> info
      }
      ControlFlowInfo(Some(allTypeInfos))
    }
  }

  def inferredTypeFor(idValue: IdValue)(using Program): Option[TypeIdentifier] =
    typeInfosOpt.flatMap(_.get(idValue).flatMap(_.mostPreciseType))

  def hasExited: Boolean = typeInfosOpt.isEmpty

  def merged(that: ControlFlowInfo)(using Program): ControlFlowInfo = (this, that) match {
    case (ControlFlowInfo(Some(thisInfoMap)), ControlFlowInfo(Some(thatInfoMap))) =>
      val newTypeInfos = (thisInfoMap.keys ++ thatInfoMap.keys).flatMap(idVal => {
        for {
          TypeInfo(val1, type1, knownIs1, knownIsNot1) <- thisInfoMap.get(idVal)
          TypeInfo(val2, type2, knownIs2, knownIsNot2) <- thatInfoMap.get(idVal)
        } yield {
          assert(val1 == val2)
          assert(type1 == type2)
          idVal -> TypeInfo(val1, type1, knownIs1.intersect(knownIs2), knownIsNot1.intersect(knownIsNot2))
        }
      }).toMap
      ControlFlowInfo(newTypeInfos)
    case (_, ControlFlowInfo(None)) => this
    case (ControlFlowInfo(None), _) => that
  }

}

object ControlFlowInfo {

  def apply(typeInfos: Map[IdValue, TypeInfo])(using Program): ControlFlowInfo =
    if isConsistent(typeInfos) then ControlFlowInfo(Some(typeInfos)) else exited

  private def isConsistent(typeInfos: Map[IdValue, TypeInfo])(using Program): Boolean = {
    val iter = typeInfos.iterator
    while (iter.hasNext) {
      val (_, typeInfo) = iter.next()
      if (typeInfo.mostPreciseType.isEmpty) {
        return false
      }
    }
    true
  }

  val exited: ControlFlowInfo = ControlFlowInfo(None)
  val empty: ControlFlowInfo = ControlFlowInfo(Some(Map.empty))

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
      
      def narrowDown(tid: TypeIdentifier): Option[TypeIdentifier] = {
        program.resolveSignature(tid) match {
          case Some(sig: DatatypeSignature) =>
            val notExcluded = sig.directSubtypes.toSet.diff(knownIsNot).intersect(knownIs)
            notExcluded.size match {
              case 0 => None
              case 1 if notExcluded.head != tid => narrowDown(notExcluded.head)
              case _ => Some(tid)
            }
          case _ => Some(tid).filterNot(knownIsNot.contains)
        }
      }
      
      val start = if knownIs.size == 1 then knownIs.head else tpe
      narrowDown(start)
    }

  }

}
