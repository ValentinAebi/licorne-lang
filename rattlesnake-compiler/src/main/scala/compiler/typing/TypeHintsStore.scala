package compiler.typing

import compiler.irs.ssa.Formulas.{Formula, IdValue}
import compiler.lang.Types.Type

import scala.collection.mutable


final class TypeHintsStore {
  private val hints = mutable.Map.empty[IdValue, mutable.LinkedHashSet[Type]]

  def offerHint(idVal: IdValue, tpe: Type): Unit = tpe.withTypeVarsSubstituted.foreach { tpe =>
    hints.getOrElseUpdate(idVal, mutable.LinkedHashSet.empty).add(tpe)
  }

  def getHints(idVal: IdValue): Iterable[Type] = {
    hints.get(idVal) match {
      case Some(hints) => hints
      case None => List.empty
    }
  }

  def getHintsIfIdVal(f: Formula): Iterable[Type] = f match {
    case idVal: IdValue => getHints(idVal)
    case _ => List.empty
  }

  override def toString: String = hints.map { (idVal, hints) =>
    s"   $idVal: ${hints.mkString("{ ", ", ", " }")}"
  }.mkString("{\n", ",\n", "\n}")

}
