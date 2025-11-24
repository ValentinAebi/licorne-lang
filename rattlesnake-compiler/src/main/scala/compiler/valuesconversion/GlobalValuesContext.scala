package compiler.valuesconversion

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Values.{Constant, Formula, IdValue, Value}

import java.util
import scala.collection.mutable

final class GlobalValuesContext extends ValuesContext {
  private val valuesDebugInfo = mutable.Map[IdValue, ValueKind]()
  private val idToObjName = mutable.Map.empty[TypeIdentifier, IdValue]
  private val objNameToId = mutable.Map.empty[IdValue, TypeIdentifier]

  override val globalCtx: GlobalValuesContext = this
  override val valuesGen: ValuesGenerator = ValuesGenerator(this)

  def resolveObject(objectId: TypeIdentifier): IdValue =
    idToObjName.getOrElseUpdate(objectId, {
      val value = valuesGen.newObject(objectId)
      objNameToId(value) = objectId
      value
    })
    
  def getNameOfObject(objectVal: IdValue): TypeIdentifier =
    objNameToId.apply(objectVal)

  override def deepCopyWithSameGlobalCtx: ValuesContext = this

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[ValuesContext.LocalInfo] = None
  
  def saveDebugInfo(value: IdValue, kind: ValueKind): Unit = {
    valuesDebugInfo.put(value, kind)
  }

  def debugInfoOf(value: IdValue): Option[ValueKind] = valuesDebugInfo.get(value)

}
