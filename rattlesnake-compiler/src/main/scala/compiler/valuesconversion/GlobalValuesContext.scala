package compiler.valuesconversion

import identifiers.TypeIdentifier
import lang.Values.Value

import scala.collection.mutable

final class GlobalValuesContext {
  private val valuesDebugInfo = mutable.WeakHashMap.empty[Value, ValueKind]
  private val objects = mutable.Map.empty[TypeIdentifier, Value]

  val valuesGen: ValuesGenerator = ValuesGenerator(this)
  
  def resolveObject(objectId: TypeIdentifier): Value = objects.getOrElseUpdate(objectId, valuesGen.newObject(objectId))
  
  private[valuesconversion] def saveDebugInfo(value: Value, kind: ValueKind): Unit = {
    valuesDebugInfo(value) = kind
  }

}
