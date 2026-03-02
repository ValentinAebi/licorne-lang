package compiler.util

import scala.collection.immutable.SeqMap

extension [T](l: Iterable[T]) def zipCommons[U](r: Iterable[U]): Iterable[(T, U)] =
  l.take(r.size).zip(r.take(l.size))

extension [A, B](map: Map[A, B]) def mapVals[C](f: B => C): Map[A, C] =
  map.map((a, b) => (a, f(b)))

extension [A, B](map: SeqMap[A, B]) def mapVals[C](f: B => C): SeqMap[A, C] =
  map.map((a, b) => (a, f(b)))
