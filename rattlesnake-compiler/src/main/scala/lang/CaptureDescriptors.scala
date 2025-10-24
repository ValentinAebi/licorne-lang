package lang

import lang.Capturables.*

object CaptureDescriptors {

  final case class CaptureSet(set: Set[Capturable]) {
    def coversRoot: Boolean = set.contains(RootCapability)

    def augmentedWith(c: Capturable): CaptureSet = CaptureSet(set + c)
    def union(that: CaptureSet): CaptureSet = CaptureSet(this.set ++ that.set)

    def union(thatOpt: Option[CaptureSet]): CaptureSet =
      thatOpt.map(this.union).getOrElse(this)

    def isEmpty: Boolean = set.isEmpty

    def mapSet(f: Set[Capturable] => Set[Capturable]): CaptureSet = CaptureSet(f(set))

    override def toString: String =
      set.toList
        .map(_.toString)
        .sorted
        .mkString("{", ", ", "}")
  }

  object CaptureSet {

    def apply(values: Capturable*): CaptureSet = CaptureSet(Set(values *))

    val empty: CaptureSet = CaptureSet(Set.empty)
    val singletonOfRoot: CaptureSet = CaptureSet(RootCapability)

  }

  def unionOf(captureDescriptors: Iterable[CaptureSet]): CaptureSet = {
    captureDescriptors.foldLeft[CaptureSet](CaptureSet.empty)(_.union(_))
  }

  val emptyCaptureSet: CaptureSet = CaptureSet.empty
  val singletonSetOfRoot: CaptureSet = CaptureSet.singletonOfRoot

}
