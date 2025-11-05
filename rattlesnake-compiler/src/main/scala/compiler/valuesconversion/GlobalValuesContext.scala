package compiler.valuesconversion

import compiler.irs.Asts
import compiler.valuesconversion.ValueKind.LocalKind
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.Value

import scala.collection.mutable

final class GlobalValuesContext extends ValuesContext {
  private val valuesDebugInfo = mutable.WeakHashMap.empty[Value, ValueKind]
  private val objects = mutable.Map.empty[TypeIdentifier, Value]

  override val globalCtx: GlobalValuesContext = this
  override val valuesGen: ValuesGenerator = ValuesGenerator(this)

  def resolveObject(objectId: TypeIdentifier): Value = objects.getOrElseUpdate(objectId, valuesGen.newObject(objectId))

  override def copyWithSameGlobals: ValuesContext = this

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[ValuesContext.LocalInfo] = None

  def saveDebugInfo(value: Value, kind: ValueKind): Unit = {
    valuesDebugInfo(value) = kind
  }

}
