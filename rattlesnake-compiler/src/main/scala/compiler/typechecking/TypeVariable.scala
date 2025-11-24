package compiler.typechecking

import com.sun.tools.javac.code.Type.TypeVar
import lang.Types
import lang.Types.Type
import lang.Values.IdValue

import scala.collection.mutable

final class TypeVariable extends Types.TypeVar {
  private val dependencies = mutable.Set.empty[IdValue]
  private var alreadyInstantiated = false
  
  def addDependency(idVal: IdValue): Unit = {
    if (alreadyInstantiated){
      throw IllegalStateException("cannot add a dependency to an already instantiated type variable")
    } else {
      dependencies.add(idVal)
    }
  }
  
  def instantiate(tpe: Type, ts: PartialTypeStore): Unit = {
    for (dep <- dependencies){
      val tpeBefore = ts.typeOf(dep)
      val tpeAfter = tpeBefore.substituteVar(this, tpe)
      ts(dep) = tpeAfter
    }
    alreadyInstantiated = true
  }

  override def typeArgs: List[Type] = List.empty
}
