package compiler.typing

import compiler.irs.ircorne.Formulas.{Formula, IdValue}

import scala.collection.mutable

final class ClosuresCollector {
  private val closures = mutable.LinkedHashMap.empty[IdValue, ClosureInfo]
  
  export closures.{isEmpty, nonEmpty, contains}
  export closures.put as enqueue
  export closures.remove as extract
  
  def dequeue(): ClosureInfo = {
    closures.remove(closures.head._1).get
  }

}
