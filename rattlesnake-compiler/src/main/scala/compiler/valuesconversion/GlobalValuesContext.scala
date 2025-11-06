package compiler.valuesconversion

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.{Formula, Value}

import java.util
import scala.collection.mutable

final class GlobalValuesContext extends ValuesContext {
  private val valuesDebugInfo = mutable.Map[Value, ValueKind]()
  private val objects = mutable.Map.empty[TypeIdentifier, Value]

  override val globalCtx: GlobalValuesContext = this
  override val valuesGen: ValuesGenerator = ValuesGenerator(this)

  def resolveObject(objectId: TypeIdentifier): Value = objects.getOrElseUpdate(objectId, valuesGen.newObject(objectId))

  override def copyWithSameGlobals: ValuesContext = this

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[ValuesContext.LocalInfo] = None

  def offerDebugInfo(value: Value, kind: ValueKind): Unit = {
    val oldValueOrdinal = valuesDebugInfo.get(value).map(_.ordinal).getOrElse(Int.MaxValue)
    if (kind.ordinal < oldValueOrdinal) {
      valuesDebugInfo.put(value, kind)
    }
  }

  def debugInfoOf(value: Value): Option[ValueKind] = valuesDebugInfo.get(value)

}
