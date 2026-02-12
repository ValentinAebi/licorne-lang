package compiler.typing

import compiler.lang.Types
import scala.collection.mutable
import Types.Type
import compiler.lang.Formulas.IdValue

final class TypeStore {
  private val store = mutable.Map.empty[IdValue, Type]

  export store.update
  
  def typeOfOpt(idValue: IdValue): Option[Type] = store.get(idValue)
  
  def typeOf(idValue: IdValue): Type = store.apply(idValue)

}
