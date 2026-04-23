package compiler.util

import scala.collection
import scala.collection.immutable
import scala.collection.mutable
import scala.reflect.ClassTag

extension [T](iterable: Iterable[T]) def asIterableOfType[U: ClassTag]: Option[Iterable[U]] = {
  val resultB = Iterable.newBuilder[U]
  val iter = iterable.iterator
  while (iter.hasNext) {
    iter.next() match {
      case u: U =>
        resultB.addOne(u)
      case _ =>
        return None
    }
  }
  Some(resultB.result())
}

extension [A, B](map: Map[A, B]) def mapVals[C](f: B => C): Map[A, C] =
  map.map((a, b) => (a, f(b)))

extension [A, B](map: immutable.SeqMap[A, B]) def mapVals[C](f: B => C): immutable.SeqMap[A, C] =
  map.map((a, b) => (a, f(b)))

extension [A, B1](left: Map[A, B1]) def combine[B2, B3](right: Map[A, B2])(f: (Option[B1], Option[B2]) => Option[B3]): Map[A, B3] =
  doCombine(left, right, Map.newBuilder[A, B3], f)

extension [A, B1](left: collection.SeqMap[A, B1]) def combineInOrder[B2, B3](right: collection.SeqMap[A, B2])(f: (Option[B1], Option[B2]) => Option[B3]): collection.SeqMap[A, B3] =
  doCombine(left, right, collection.SeqMap.newBuilder[A, B3], f)

extension [A, B1](left: Map[A, B1]) def mergeCombine[B2, B3 >: B1 | B2](right: Map[A, B2])(f: (B1, B2) => B3): Map[A, B3] =
  left.combine(right)(mergeOnlyOnConflict(f))

extension [A, B1](left: collection.SeqMap[A, B1]) def mergeCombineInOrder[B2, B3 >: B1 | B2](right: collection.SeqMap[A, B2])(f: (B1, B2) => B3): collection.SeqMap[A, B3] =
  left.combineInOrder(right)(mergeOnlyOnConflict(f))

private def doCombine[A, B1, B2, B3, M](left: collection.Map[A, B1], right: collection.Map[A, B2], builder: mutable.Builder[(A, B3), M], f: (Option[B1], Option[B2]) => Option[B3]): M = {
  for {
    a <- left.keys ++ right.keys
    b <- f(left.get(a), right.get(a))
  } {
    builder.addOne(a -> b)
  }
  builder.result()
}

private def mergeOnlyOnConflict[B1, B2, B3 >: B1 | B2](f: (B1, B2) => B3)(left: Option[B1], right: Option[B2]): Option[B3] = (left, right) match {
  case (Some(b1), Some(b2)) => Some(f(b1, b2))
  case (sb1@Some(_), None) => sb1
  case (None, sb2@Some(_)) => sb2
  case (None, None) => None
}
