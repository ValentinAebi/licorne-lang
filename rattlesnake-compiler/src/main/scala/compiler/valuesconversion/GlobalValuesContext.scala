package compiler.valuesconversion

import compiler.reporting.Position
import identifiers.{FunOrVarId, TypeIdentifier}
import lang.Types.TypeVariable
import lang.Formulas.{Constant, Formula, IdValue, Value}

import java.util
import scala.collection.mutable

final class GlobalValuesContext extends ValuesContext {
  private val idToObjName = mutable.Map.empty[TypeIdentifier, IdValue]
  private val objNameToId = mutable.Map.empty[IdValue, TypeIdentifier]
  private val typeVariables = mutable.ListBuffer.empty[(TypeVariable, Option[Position])]

  override val globalCtx: GlobalValuesContext = this
  override val valuesGen: ValuesGenerator = ValuesGenerator(this)

  def resolveObject(objectId: TypeIdentifier): IdValue =
    idToObjName.getOrElseUpdate(objectId, {
      val value = valuesGen.newValue(objectId)
      objNameToId(value) = objectId
      value
    })
    
  def getNameOfObject(objectVal: IdValue): TypeIdentifier =
    objNameToId.apply(objectVal)
    
  def saveTypeVariable(tv: TypeVariable, posOpt: Option[Position]): Unit = {
    typeVariables.addOne((tv, posOpt))
  }
  
  def getTypeVariables: List[(TypeVariable, Option[Position])] = typeVariables.toList

  override def deepCopyWithSameGlobalCtx: ValuesContext = this

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[ValuesContext.LocalInfo] = None

}
