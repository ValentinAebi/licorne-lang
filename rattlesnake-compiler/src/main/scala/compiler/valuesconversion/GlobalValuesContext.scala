package compiler.valuesconversion

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.Value

import scala.collection.mutable

final class GlobalValuesContext {
  private val valuesDebugInfo = mutable.WeakHashMap.empty[Value, ValueKind]
  private val packages = mutable.Map.empty[TypeIdentifier, Value]

  val valuesGen: ValuesGenerator = ValuesGenerator(this)
  
  def resolvePackage(packageId: TypeIdentifier): Value = packages.getOrElseUpdate(packageId, valuesGen.newPackage(packageId))
  
  private[valuesconversion] def saveDebugInfo(value: Value, kind: ValueKind): Unit = {
    valuesDebugInfo(value) = kind
  }

}
