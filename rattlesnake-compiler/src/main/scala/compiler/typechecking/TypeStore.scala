package compiler.typechecking

import lang.Types

import scala.collection.mutable
import lang.Types.{BaseType, Type}
import lang.Formulas.IdValue

final class TypeStore {
  private val store = mutable.Map.empty[IdValue, Type]

  export store.update
  
  def typeOfOpt(idValue: IdValue): Option[Type] = store.get(idValue)
  
  def typeOf(idValue: IdValue): Type = store.apply(idValue)

  def widenType(idValue: IdValue, tpe: Type): Unit = {
    val prevType = typeOf(idValue)
    this (idValue) = Types.join(prevType, tpe)
  }

}
