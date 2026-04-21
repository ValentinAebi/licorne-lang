package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.SSA.Scope
import compiler.lang.Formulas.{IdValue, UninterpretedConstIdValue}
import compiler.lang.Keyword
import compiler.lang.Types.TypeVariable
import compiler.reporting.Position
import compiler.valproxies.ProxyStore

import java.util
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

  {
    proxyStore.saveProxy(unitVal, unitVal)
    proxyStore.saveProxy(trueVal, trueVal)
    proxyStore.saveProxy(falseVal, falseVal)
  }

  def resolveObject(objectId: TypeIdentifier): UninterpretedConstIdValue =
    idToObjName.getOrElseUpdate(objectId, {
      val value = globalScope.newUninterpretedConst(objectId.stringId)
      objNameToId(value) = objectId
      proxyStore.saveProxy(value, value)
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
