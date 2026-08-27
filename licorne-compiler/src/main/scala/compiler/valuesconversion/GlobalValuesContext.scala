package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.ircorne.Formulas.{IdValue, UninterpretedConstIdValue}
import compiler.irs.ircorne.IRcorne.Scope
import compiler.lang.Types.TypeVariable
import compiler.valproxies.ProxyStore

import scala.collection.mutable

final class GlobalValuesContext(val proxyStore: ProxyStore) extends ValuesContext {
  private val idToObjName = mutable.Map.empty[TypeIdentifier, UninterpretedConstIdValue]
  private val objNameToId = mutable.Map.empty[IdValue, TypeIdentifier]
  private val typeVariables = mutable.ListBuffer.empty[TypeVariable]

  override val globalCtx: GlobalValuesContext = this
  
  val globalScope: Scope = Scope.root(this)
  
  val unitVal: IdValue = globalScope.newUninterpretedConst("unit")
  val trueVal: IdValue = globalScope.newUninterpretedConst("true")
  val falseVal: IdValue = globalScope.newUninterpretedConst("false")
  val nullVal: IdValue = globalScope.newUninterpretedConst("null")
  
  val itValue: IdValue = globalScope.newUninterpretedConst("it")

  def resolveObject(objectId: TypeIdentifier): UninterpretedConstIdValue =
    idToObjName.getOrElseUpdate(objectId, {
      val value = globalScope.newUninterpretedConst(objectId.stringId)
      objNameToId(value) = objectId
      value
    })
    
  def getNameOfObject(objectVal: IdValue): Option[TypeIdentifier] =
    objNameToId.get(objectVal)
    
  def saveTypeVariable(tv: TypeVariable): Unit = {
    typeVariables.addOne(tv)
  }
  
  def getTypeVariables: List[TypeVariable] = typeVariables.toList

  override def deepCopyWithSameGlobalCtx: ValuesContext = this

  override def withOneMoreFrame: LocalValuesContext = LocalValuesContext(this)

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[ValuesContext.LocalInfo] = None

}
