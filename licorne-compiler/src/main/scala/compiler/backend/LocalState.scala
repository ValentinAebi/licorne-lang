package compiler.backend

import compiler.backend.LocalState.LocalValue
import compiler.identifiers.FunOrVarId
import compiler.lang.Types.Type

import scala.collection.mutable


final class LocalState {
  private val currentlyKnownValues = mutable.Map.empty[FunOrVarId, LocalValue]
  private val stack = mutable.LinkedHashMap.empty[LocalValue, Int]
  
  def getVal(id: FunOrVarId): Unit = {
    val localVal = currentlyKnownValues.apply(id)
    ???
  }
  
}

object LocalState {
  
  final class LocalValue(idOpt: Option[FunOrVarId], tpe: Type, slotOpt: Option[Int])
  
}
