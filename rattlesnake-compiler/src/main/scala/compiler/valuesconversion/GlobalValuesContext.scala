package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.SSA.Scope
import compiler.irs.egraphs.EGraph
import compiler.lang.Formulas.{IdValue, UninterpretedConstIdValue}
import compiler.lang.Keyword
import compiler.reporting.Position
import compiler.lang.Types.TypeVariable

import java.util
import scala.collection.mutable

final class GlobalValuesContext extends ValuesContext {
  private val idToObjName = mutable.Map.empty[TypeIdentifier, UninterpretedConstIdValue]
  private val objNameToId = mutable.Map.empty[IdValue, TypeIdentifier]
  private val typeVariables = mutable.ListBuffer.empty[(TypeVariable, Option[Position])]

  override val globalCtx: GlobalValuesContext = this
  
  val globalScope: Scope = Scope.root(this)
  
  val unitVal: IdValue = globalScope.newUninterpretedConst("unit")
  val trueVal: IdValue = globalScope.newUninterpretedConst("true")
  val falseVal: IdValue = globalScope.newUninterpretedConst("false")

  def resolveObject(objectId: TypeIdentifier): UninterpretedConstIdValue =
    idToObjName.getOrElseUpdate(objectId, {
      val value = globalScope.newUninterpretedConst(objectId.stringId)
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
