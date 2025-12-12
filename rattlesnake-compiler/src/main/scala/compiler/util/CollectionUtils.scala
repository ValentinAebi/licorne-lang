package compiler.util

extension [T](l: Iterable[T]) def zipCommons[U](r: Iterable[U]): Iterable[(T, U)] =
  l.take(r.size).zip(r.take(l.size))
