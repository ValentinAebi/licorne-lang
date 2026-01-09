package compiler.typechecking

import lang.Types

import scala.collection.mutable
import lang.Types.{BaseType, Type}
import lang.Values.IdValue

final class TypeStore {
  private val store = mutable.Map.empty[IdValue, (Type, Taint)]

  export store.update

  def query(idValue: IdValue): Option[(Type, Taint)] = store.get(idValue)

  def typeQuery(idValue: IdValue): Option[Type] = query(idValue).map(_._1)

  def taintQuery(idValue: IdValue): Option[Taint] = query(idValue).map(_._2)

  def widenType(idValue: IdValue, tpe: Type): Unit = {
    val (prevType, taint) = query(idValue).get
    this (idValue) = (Types.join(prevType, tpe), taint)
  }
  
  def widenTaint(idValue: IdValue, taint: Taint): Unit = {
    val (tpe, prevTaint) = query(idValue).get
    this (idValue) = (tpe, prevTaint + taint)
  }

}
