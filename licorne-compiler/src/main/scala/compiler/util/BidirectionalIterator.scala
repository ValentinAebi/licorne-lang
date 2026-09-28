package compiler.util

final class BidirectionalIterator[T](iterable: Iterable[T]) {
  private val seq = iterable.toSeq
  private var idx = -1

  def hasCurrent: Boolean = seq.indices.contains(idx)

  def current: T = {
    if (!hasCurrent) {
      throw IllegalStateException("no current element")
    }
    seq(idx)
  }

  def canMoveForward: Boolean = idx < seq.size - 1

  def moveForward(): T = {
    if (!canMoveForward) {
      throw IllegalStateException("no next element")
    }
    idx += 1
    current
  }

  def canMoveBackward: Boolean = idx > 0

  def moveBackward(): T = {
    if (!canMoveBackward) {
      throw IllegalStateException("no previous element")
    }
    idx -= 1
    current
  }

}
