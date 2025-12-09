package compiler.valuesconversion

import identifiers.{Identifier, NormalFunOrVarId}
import lang.Values.IdValue

import scala.collection.mutable

final class ValuesGenerator(globalValuesContext: GlobalValuesContext) {
  private val uidGen = mutable.Map.empty[Identifier, Int]

  def newValue(): IdValue = newValue(NormalFunOrVarId("$"))

  def newErrorValue(): IdValue = newValue(NormalFunOrVarId("err"))

  def newValue(id: Identifier): IdValue = {
    val uidIdx = uidGen.getOrElse(id, 0)
    uidGen(id) = uidIdx + 1
    IdValue(id.toString, uidIdx)
  }
}
