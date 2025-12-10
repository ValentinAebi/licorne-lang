package compiler.typechecking

import scala.collection.mutable
import lang.Types.{BaseType, Type}
import lang.Values.IdValue

trait TypeStore {
  
  def typeOf(idVal: IdValue): Type = typeOfOpt(idVal).get
  
  def typeOfOpt(idVal: IdValue): Option[Type]
  
  def baseTypeOfOpt(idVal: IdValue): Option[BaseType] = typeOfOpt(idVal).map(_.baseType)

}

final class MutableTypeStore extends TypeStore {
  private val types = mutable.Map.empty[IdValue, Type]
  
  export types.update
  export types.get as typeOfOpt
  
}
