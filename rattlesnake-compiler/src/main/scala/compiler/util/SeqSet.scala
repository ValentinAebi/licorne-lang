package compiler.util

import scala.collection.{WithFilter, mutable}

final class SeqSet[T] private(private val underlyingMap: mutable.LinkedHashMap[T, Null]) extends Set[T] {

  override def incl(elem: T): SeqSet[T] = if contains(elem) then this else {
    val newMap = mutable.LinkedHashMap.from(underlyingMap)
    newMap.put(elem, null)
    new SeqSet(newMap)
  }

  override def excl(elem: T): Set[T] = if !contains(elem) then this else {
    val newMap = mutable.LinkedHashMap.from(underlyingMap)
    newMap.remove(elem)
    new SeqSet(newMap)
  }

  override def contains(elem: T): Boolean = underlyingMap.contains(elem)

  override def filter(pred: T => Boolean): SeqSet[T] = new SeqSet(underlyingMap.filter((k, _) => pred(k)))

  override def iterator: Iterator[T] = underlyingMap.keysIterator

  override def concat(that: IterableOnce[T]): SeqSet[T] =
    SeqSet(this.iterator ++ that.iterator)

  override def map[B](f: T => B): SeqSet[B] =
    new SeqSet(underlyingMap.map((k, _) => (f(k), null)))

  def matches[R](pfs: PartialFunction[T, R]*): Option[List[R]] = if pfs.size == size then {

    def tryToMatchOrdering(ordering: List[T]): Option[List[R]] = {
      val resultB = List.newBuilder[R]
      val orderingIter = ordering.iterator
      val pfsIter = pfs.iterator
      while (orderingIter.hasNext) {
        val elem = orderingIter.next()
        val pf = pfsIter.next()
        pf.lift.apply(elem) match {
          case Some(r) =>
            resultB.addOne(r)
          case None =>
            return None
        }
      }
      Some(resultB.result())
    }

    val orderingsIter = possibleOrderings(toList).iterator
    while (orderingsIter.hasNext) {
      tryToMatchOrdering(orderingsIter.next()) match {
        case some: Some[List[R]] =>
          return some
        case None => ()
      }
    }
    None
  } else None

  private def possibleOrderings(ls: List[T]): List[List[T]] = {

    def traverse(st1: List[T], st2: List[T], prevSolutions: List[List[T]]): List[List[T]] = st2 match {
      case head :: tail =>
        val newSolutions = possibleOrderings(st1 ++ tail).map(head :: _)
        traverse(head :: st1, tail, newSolutions ++ prevSolutions)
      case Nil => prevSolutions
    }

    ls match {
      case Nil => List(Nil)
      case _ => traverse(Nil, ls, Nil)
    }
  }

}

object SeqSet {

  def apply[T](elems: IterableOnce[T]): SeqSet[T] = {
    val lhm = mutable.LinkedHashMap.from(elems.iterator.map(_ -> null))
    new SeqSet(lhm)
  }

  def apply[T](elems: T*): SeqSet[T] = SeqSet(elems.iterator)

  def empty[T]: SeqSet[T] = SeqSet()
  
  def newBuilder[T]: Builder[T] = mutable.LinkedHashMap.empty[T, Null]

  opaque type Builder[T] = mutable.LinkedHashMap[T, Null]

  extension [T](builder: Builder[T]) {

    def addOne(elem: T): Builder[T] = {
      builder.put(elem, null)
      builder
    }
    
    def addAll(elems: IterableOnce[T]): Builder[T] = {
      for (elem <- elems) do {
        builder.addOne(elem -> null)
      }
      builder
    }

    def build(): SeqSet[T] =
      new SeqSet[T](builder)
  }

}
