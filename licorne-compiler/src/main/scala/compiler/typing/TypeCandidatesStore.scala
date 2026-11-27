package compiler.typing

import compiler.irs.ircorne.Formulas.IdValue
import compiler.lang.Types
import compiler.lang.Types.Type
import compiler.typing.contexts.SubtypingContext.SubtypeCheckingMode
import compiler.typing.contexts.{ResolutionContext, SubtypingContext, TypeParamsContext}
import compiler.valproxies.ProxyStore

import scala.collection.mutable


final class TypeCandidatesStore {
  private val candidates = mutable.Map.empty[IdValue, mutable.LinkedHashSet[Type]]
  private val uniqueCandidates = mutable.Map.empty[IdValue, Type]

  def discardUnresolvedCandidates(): Unit = {
    candidates.mapValuesInPlace { (_, candidatesSet) =>
      candidatesSet.map(_.withTypeVarsExpanded)
        .filter(_.allTypeVariables.isEmpty)
    }
  }

  def offerCandidate(idVal: IdValue, tpe: Type)(using tpCtx: TypeParamsContext, proxyStore: ProxyStore, resolCtx: ResolutionContext, subtypingCtx: SubtypingContext): Unit = {
    if (uniqueCandidates.contains(idVal)) {
      return
    }
    val devType = tpe.withDependenciesTransformed(proxyStore.developNearest(_))
    val candidatesList = candidates.getOrElseUpdate(idVal, mutable.LinkedHashSet.empty)
    candidatesList.filterInPlace(!subtypingCtx.isSubtype(tpe, _)(using SubtypeCheckingMode.CheckOnly))
    devType match {
      case Types.NullableType(nullatedType) =>
        candidatesList.add(nullatedType)
      case _ => ()
    }
    candidatesList.add(devType)
    devType match {
      case Types.RefinedType(baseType, predicate) =>
        candidatesList.add(baseType)
      case _ => ()
    }
  }

  def setUniqueCandidate(idVal: IdValue, tpe: Type): Unit = {
    uniqueCandidates.put(idVal, tpe)
  }

  def getCandidates(idVal: IdValue): Iterable[Type] = {
    uniqueCandidates.get(idVal) match {
      case Some(uniqueCandidate) => List(uniqueCandidate)
      case None => candidates.get(idVal) match {
        case Some(candidatesRaw) =>
          val candidatesExp = candidatesRaw.map(_.withTypeVarsExpanded)
          candidates(idVal) = candidatesExp
          candidatesExp
        case None => List.empty
      }
    }
  }

  override def toString: String =
    uniqueCandidates.map((idVal, cand) => s"$idVal -> $cand").mkString("unique: {\b", ",\n", "\n}")
      ++ candidates.map { (idVal, candidates) =>
      s"   $idVal: ${candidates.mkString("{ ", ", ", " }")}"
    }.mkString("regular: {\n", ",\n", "\n}")

}

object TypeCandidatesStore {
  def newEmpty: TypeCandidatesStore = TypeCandidatesStore()
}
