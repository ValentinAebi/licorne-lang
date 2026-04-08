package compiler.typing

import compiler.lang.Formulas.HeapVarIdValue
import compiler.lang.Types.Type

import scala.collection.mutable

final class HeapVarsTypeStore {
  private val types = mutable.Map.empty[HeapVarIdValue, Type]
  
  export types.put as saveType
  export types.get as getType
  export types.apply as getTypeUnsafe
  export types.contains

}
