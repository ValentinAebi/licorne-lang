package compiler.valuesconversion

import compiler.identifiers.{Identifier, NormalFunOrVarId}
import compiler.lang.Formulas.{IdValue, RegularIdValue}

import scala.collection.mutable

final class ValuesGenerator(globalValuesContext: GlobalValuesContext) {
  private val uidGen = mutable.Map.empty[Identifier, Int]

  def newValue(): IdValue = newValue(NormalFunOrVarId("$"))

  def newErrorValue(): IdValue = newValue(NormalFunOrVarId("err"))

  def newValue(id: Identifier): IdValue = {
    val uidIdx = uidGen.getOrElse(id, 0)
    uidGen(id) = uidIdx + 1
    RegularIdValue(id.toString, uidIdx)
  }
}
