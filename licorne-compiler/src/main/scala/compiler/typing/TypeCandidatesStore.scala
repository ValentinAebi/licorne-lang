package compiler.typing

import compiler.irs.ircorne.Formulas.{Formula, IdValue}
import compiler.lang.Types
import compiler.lang.Types.Type

import scala.collection.mutable


final class TypeCandidatesStore {
  private val candidates = mutable.Map.empty[IdValue, mutable.LinkedHashSet[Type]]
  private val pureClosureCandidates = mutable.Set.empty[IdValue]

  def offerCandidate(idVal: IdValue, tpe: Type): Unit = {
    tpe.withTypeVarsSubstituted.foreach { tpe =>
      candidates.getOrElseUpdate(idVal, mutable.LinkedHashSet.empty).add(tpe)
      tpe match {
        case Types.RefinedType(baseType, predicate) =>
          candidates.apply(idVal).add(baseType)
        case _ => ()
      }
    }
    tpe match {
      case Types.ClosureType(params, result, enforcedPure) if enforcedPure =>
        pureClosureCandidates.add(idVal)
      case _ => ()
    }
  }

  def getCandidates(idVal: IdValue): Iterable[Type] = {
    candidates.get(idVal) match {
      case Some(candidates) => candidates
      case None => List.empty
    }
  }

  def getCandidatesIfIdVal(f: Formula): Iterable[Type] = f match {
    case idVal: IdValue => getCandidates(idVal)
    case _ => List.empty
  }
  
  def hasPureClosureCandidateFor(idValue: IdValue): Boolean =
    pureClosureCandidates.contains(idValue)

  override def toString: String = candidates.map { (idVal, candidates) =>
    s"   $idVal: ${candidates.mkString("{ ", ", ", " }")}"
  }.mkString("{\n", ",\n", "\n}")

}

object TypeCandidatesStore {
  def newEmpty: TypeCandidatesStore = TypeCandidatesStore()
}
