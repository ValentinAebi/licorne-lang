package compiler.typechecking

import compiler.program.Program
import compiler.typechecking.ControlFlowInfo.{TypeInfo, exited}
import identifiers.TypeIdentifier
import lang.Types.{BaseUnionType, NamedType}
import lang.{DatatypeSignature, Encapsulated, RecordSignature, Unencapsulated}
import lang.Values.IdValue

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.boundary

final case class ControlFlowInfo private(private val typeInfosOpt: Option[Map[IdValue, TypeInfo]]) {

  def refined(newTypeInfosSet: Iterable[TypeInfo])(using program: Program): ControlFlowInfo = typeInfosOpt match {
    case None => this
    case Some(typeInfos) => boundary {
      val allTypeInfos = for ((idValue, allInfos) <- (typeInfos.values ++ newTypeInfosSet).groupBy(_.value)) yield {
        val knownIs = allInfos.flatMap(_.knownIs).toList
        val knownIsNot = allInfos.flatMap(_.knownIsNot).toList
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

  def merged(that: ControlFlowInfo)(using program: Program): ControlFlowInfo = {
    
    def effectivelyMerged = (this, that) match {
      case (ControlFlowInfo(Some(thisInfoMap)), ControlFlowInfo(Some(thatInfoMap))) =>
        val newTypeInfos = (thisInfoMap.keys ++ thatInfoMap.keys).flatMap(idVal => {
          for {
            tInfo1@TypeInfo(val1, type1, knownIs1, knownIsNot1) <- thisInfoMap.get(idVal)
            tInfo2@TypeInfo(val2, type2, knownIs2, knownIsNot2) <- thatInfoMap.get(idVal)
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
    
    if this.hasExited then that
    else if that.hasExited then this
    else effectivelyMerged
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

  final case class TypeInfo(value: IdValue, tpe: TypeIdentifier, knownIs: List[TypeIdentifier], knownIsNot: List[TypeIdentifier]) {
    private var cachesMostPreciseType = Option.empty[Option[TypeIdentifier]]

    def mergedWith(that: TypeInfo): TypeInfo = {
      require(this.value == that.value)
      require(this.tpe == that.tpe)
      TypeInfo(value, tpe, (this.knownIs ++ that.knownIs).distinct, (this.knownIsNot ++ that.knownIsNot).distinct)
    }
    
    def substitute(subst: Map[IdValue, IdValue]): TypeInfo = {
      if subst.contains(value) then copy(value = subst.apply(value))
      else this
    }

    /**
     * @return None if all possible types were excluded (in the typical context this implies that we are in an unreachable branch)
     */
    def mostPreciseType(using program: Program): Option[TypeIdentifier] = cachesMostPreciseType match {
      case Some(cachedResult) => cachedResult
      case None =>
        val result = boundary {
          program.resolveSignature(tpe) match {
            case Some(sig: Encapsulated) => knownIs.headOption.orElse(Some(tpe))
            case Some(sig: Unencapsulated) =>
              program.developUnencapsulated(tpe) match {
                case Some(records) =>
                  records.filter(r => knownIs.forall(ki => program.isEnumCaseOf(r.id, ki)) && !knownIsNot.exists(kin => program.isEnumCaseOf(r.id, kin))) match {
                    case Nil => None
                    case List(sig) => Some(sig.id)
                    case _ => Some(tpe)
                  }
                case None => Some(tpe)
              }
            case _ => Some(tpe)
          }
        }
        cachesMostPreciseType = Some(result)
        result
    }

  }

}
