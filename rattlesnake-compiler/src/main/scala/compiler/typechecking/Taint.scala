package compiler.typechecking

import lang.Values.IdValue

enum Taint {
  case Parameters(params: Set[IdValue])
  case Unstable
  
  def +(that: Taint): Taint = (this, that) match {
    case (Parameters(params1), Parameters(params2)) => Parameters(params1 ++ params2)
    case _ => Unstable
  }
  
  def isCoveredBy(that: Taint): Boolean = (this, that) match {
    case (_, Unstable) => true
    case (Parameters(params1), Parameters(params2)) =>
      params1.subsetOf(params2)
    case _ => false
  }
  
}

object Taint {

  val constant = Parameters(Set.empty)
  
  def ofParam(paramVal: IdValue): Taint = Parameters(Set(paramVal))
  
}
