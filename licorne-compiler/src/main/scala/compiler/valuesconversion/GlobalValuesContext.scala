package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.ircorne.Formulas.{IdValue, NamedIdValue, UninterpretedConstIdValue}
import compiler.irs.ircorne.IRcorne.Scope
import compiler.lang.Types.TypeVariable
import compiler.reporting.Position
import compiler.valproxies.ProxyStore

import scala.collection.mutable

final class GlobalValuesContext(val proxyStore: ProxyStore) extends ValuesContext {
  private val idToObjName = mutable.Map.empty[TypeIdentifier, UninterpretedConstIdValue]
  private val objNameToId = mutable.Map.empty[IdValue, TypeIdentifier]
  private val typeVariables = mutable.ListBuffer.empty[TypeVariable]

  override val globalCtx: GlobalValuesContext = this
  
  val globalScope: Scope = Scope.root(this)
  
  val unitVal: NamedIdValue = globalScope.newUninterpretedConst("unit", None)
  val nullVal: NamedIdValue = globalScope.newUninterpretedConst("null", None)
  
  def isPredefLiteralValue(idValue: IdValue): Boolean =
    idValue == unitVal || idValue == nullVal
  
  val itValue: NamedIdValue = globalScope.newUninterpretedConst("it", None)

  def resolveObject(objectId: TypeIdentifier, posOpt: Option[Position]): UninterpretedConstIdValue = {
    idToObjName.getOrElseUpdate(objectId, {
      val value = globalScope.newUninterpretedConst(objectId.stringId, posOpt)
      objNameToId(value) = objectId
      value
    })
  }

  def resolveObjectIfKnown(objectId: TypeIdentifier): Option[UninterpretedConstIdValue] =
    idToObjName.get(objectId.copy(isCompanionObject = false))
    
  def getNameOfObject(objectVal: IdValue): Option[TypeIdentifier] =
    objNameToId.get(objectVal)
    
  def allObjects: Iterable[(TypeIdentifier, UninterpretedConstIdValue)] = idToObjName
    
  def saveTypeVariable(tv: TypeVariable): Unit = {
    typeVariables.addOne(tv)
  }
  
  def getTypeVariables: List[TypeVariable] = typeVariables.toList

  override def deepCopyWithSameGlobalCtx: ValuesContext = this

  override def withOneMoreFrame: LocalValuesContext = LocalValuesContext(this)

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[ValuesContext.LocalInfo] = None

}
