package compiler.valuesconversion

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.Value

import scala.collection.mutable

final class GlobalValuesContext extends ValuesContext {
  private val valuesDebugInfo = mutable.WeakHashMap.empty[Value, ValueKind]
  private val objects = mutable.Map.empty[TypeIdentifier, Value]

  val valuesGen: ValuesGenerator = ValuesGenerator(this)
  
  def resolveObject(objectId: TypeIdentifier): Value = objects.getOrElseUpdate(objectId, valuesGen.newObject(objectId))

  override private[valuesconversion] def updateLocal(id: FunOrVarId, value: Value): Boolean = false

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[ValuesContext.LocalInfo] = None

  private[valuesconversion] def saveDebugInfo(value: Value, kind: ValueKind): Unit = {
    valuesDebugInfo(value) = kind
  }

}
