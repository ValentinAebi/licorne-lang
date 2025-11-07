package compiler.valuesconversion

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.{Constant, Formula, IdValue, Value}

import java.util
import scala.collection.mutable

final class GlobalValuesContext extends ValuesContext {
  private val valuesDebugInfo = mutable.Map[IdValue, ValueKind]()
  private val objects = mutable.Map.empty[TypeIdentifier, IdValue]

  override val globalCtx: GlobalValuesContext = this
  override val valuesGen: ValuesGenerator = ValuesGenerator(this)

  def resolveObject(objectId: TypeIdentifier): IdValue =
    objects.getOrElseUpdate(objectId, valuesGen.newObject(objectId))

  override def copyWithSameGlobals: ValuesContext = this

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[ValuesContext.LocalInfo] = None
  
  def saveDebugInfo(value: IdValue, kind: ValueKind): Unit = {
    valuesDebugInfo.put(value, kind)
  }

  def debugInfoOf(value: IdValue): Option[ValueKind] = valuesDebugInfo.get(value)

}
