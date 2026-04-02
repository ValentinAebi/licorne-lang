package compiler.typing

import compiler.lang.Formulas.IdValue
import compiler.lang.Types.Type

import scala.collection.mutable


final class TypeHintsStore {
  private val hints = mutable.Map.empty[IdValue, mutable.LinkedHashSet[Type]]

  def addHint(idVal: IdValue, tpe: Type): Unit = {
    hints.getOrElseUpdate(idVal, mutable.LinkedHashSet.empty).add(tpe)
  }

  def getHints(idVal: IdValue): Iterable[Type] = {
    hints.get(idVal) match {
      case Some(hints) => hints
      case None => List.empty
    }
  }

  override def toString: String = hints.map { (idVal, hints) =>
    s"   $idVal: ${hints.mkString("{ ", ", ", " }")}"
  }.mkString("{\n", ",\n", "\n}")

}
