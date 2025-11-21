package compiler.typechecking

import scala.collection.mutable

import lang.Types.Type
import lang.Values.IdValue

trait TypeStore {
  
  def typeOf(idVal: IdValue): Type = typeOfOpt(idVal).get
  
  def typeOfOpt(idVal: IdValue): Option[Type]

}

final class PartialTypeStore extends TypeStore {
  private val types = mutable.Map.empty[IdValue, Type]
  
  export types.update
  export types.get as typeOfOpt
  
}
