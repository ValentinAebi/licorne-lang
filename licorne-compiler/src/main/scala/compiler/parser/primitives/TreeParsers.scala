package compiler.parser.primitives

import compiler.irs.asts.Asts.Ast
import compiler.irs.tokens.Tokens.*
import ParseTree.^:
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position

/**
 * Parsers for some parts of the syntax
 */
object TreeParsers {

  def withDescription[U, P <: AnyTreeParser[U]](name: String)(p: P): P = {
    p.setDescription(name)
    p
  }

  /**
   * Creates a parser that uses a `PartialFunction`
   *
   * @param expectedDescr description of the expected token (for error reporting)
   * @param pf            the `PartialFunction`, defined at tokens treated by this parser and returning an instance of `U`
   * @param errorReporter errors will be saved there
   * @return the created parser
   */
  inline def treeParser[U](expectedDescr: List[String])(inline pf: PartialFunction[Token, U])
                          (implicit errorReporter: ErrorReporter): FinalTreeParser[U] =
    ExtractorTreeParser(pf, expectedDescr, errorReporter)

  /**
   * Creates a parser that uses a `PartialFunction` and returns the position along with the result
   *
   * @param expectedDescr description of the expected token (for error reporting)
   * @param pf            the `PartialFunction`, defined at tokens treated by this parser and returning an instance of `U`
   * @param errorReporter errors will be saved there
   * @return the created parser
   */
  inline def treeParserPositioned[U](expectedDescr: List[String])(inline pf: PartialFunction[Token, U])
                                    (implicit errorReporter: ErrorReporter): FinalTreeParser[(U, Position)] =
    ExtractorTreeParserPositioned(pf, expectedDescr, errorReporter)

  /**
   * Creates a parser that returns a `Some[U]` with the result of `optional` if `optional` accepts the token and `None` o.w.
   */
  def opt[U](optional: AnyTreeParser[U])
            (implicit errorReporter: ErrorReporter): AnyTreeParser[Option[U]] =
    OptionalTreeParser(optional, errorReporter)

  /**
   * Creates a parser that admits any number of repetitions of the given parser
   */
  def repeat[U](repeated: AnyTreeParser[U])(implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = {
    recursive {
      opt(repeated ::: repeat(repeated)) map {
        case Some(head ^: tail) => head :: tail
        case None => Nil
      }
    }
  }

  /**
   * Creates a parser that admits any non zero number of repetitions of the given parser
   */
  def repeatNonZero[U](repeated: AnyTreeParser[U])(implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = {
    repeated ::: repeat(repeated) map {
      case head ^: tail => head :: tail
    }
  }

  /**
   * Creates a parser that admits any number of repetitions of the given parser, separated by `sep`
   */
  def repeatWithSep[U](repeated: AnyTreeParser[U], sep: Ignored)
                      (implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = {
    opt(repeated ::: repeat(sep ::: repeated)) map {
      case Some(head ^: tail) => head :: tail
      case None => Nil
    }
  }

  /**
   * Creates a parser that admits any non zero number of repetitions of the given parser, separated by `sep`
   */
  def repeatWithSepNonZero[U](repeated: AnyTreeParser[U], sep: FinalIgnored)
                             (implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = recursive {
    repeated ::: opt(sep ::: repeatWithSep(repeated, sep)) map {
      case head ^: Some(tail) => head :: tail
      case single ^: None => List(single)
    }
  }

  /**
   * Similar to [[repeatWithSep]] but accepts an optional `end` at the end of the last `repeated`
   */
  def repeatWithEnd[U](repeated: AnyTreeParser[U], end: FinalIgnored)
                      (implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = recursive {
    opt(repeated ::: opt(end ::: repeatWithEnd(repeated, end))) map {
      case None => Nil
      case Some(single ^: None) => List(single)
      case Some(head ^: Some(tail)) => head :: tail
    }
  }

  /**
   * Similar to [[repeatWithSepNonZero]] but accepts an optional `end` at the end of the last `repeated`
   */
  def repeatWithEndNonZero[U](repeated: AnyTreeParser[U], end: FinalIgnored)
                             (implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = {
    repeated ::: opt(end ::: repeatWithEnd(repeated, end)) map {
      case single ^: None => List(single)
      case head ^: Some(tail) => head :: tail
    }
  }

  extension [W](self: FinalTreeParser[W]) {
    /**
     * Produces a parser that can only be used in a concatenation and whose result is ignored.
     * This parser does not require a next parser.
     */
    def ignored: FinalIgnored = FinalIgnored(self)
  }
  extension [W](self: AnyTreeParser[W]) {
    /**
     * Produces a parser that can only be used in a concatenation and whose result is ignored.
     * This parser requires a next parser.
     */
    def ignored: NonFinalIgnored = NonFinalIgnored(self)
  }

  /**
   * Avoids infinite loops for recursive parsers
   */
  def recursive[T](recursed: => AnyTreeParser[T]): AnyTreeParser[T] = {
    new AnyTreeParser[T] {
      lazy val underlying: AnyTreeParser[T] = recursed
      export underlying.admits
      export underlying.extract
      export underlying.firstExpectedDescrImpl
    }
  }

  /**
   * Avoids infinite loops for recursive parsers
   */
  def recursive[T](recursed: => FinalTreeParser[T]): FinalTreeParser[T] = {
    new FinalTreeParser[T] {
      lazy val underlying: FinalTreeParser[T] = recursed
      export underlying.admits
      export underlying.extract
      export underlying.firstExpectedDescr
    }
  }

  /**
   * Object able to parse a `ParseTree`
   *
   * The parsing method may require info on the next parser (as arguments)
   */
  sealed abstract class AnyTreeParser[+U] {

    private var description: Option[String] = None

    private[primitives] def setDescription(descr: String): Unit = {
      description = Some(descr)
    }

    /**
     * @param ll1Iterator   <b> NOT MUTATED </b>
     *                    @param suffixAdmits function to compute whether the next parser admits the next token
     *                    @return `true` iff this parser admits the next token in `ll1Iterator`
     */
    def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean

    /**
     *
     * @param ll1Iterator   <b> MUTATED </b> (moved forward by 1)
     *                    @param suffixAdmits function to compute whether the next parser admits the next token
     *                    @param suffixDescr description of the next parser (potentially considering the following ones recursively)
     *                    @return the `U` produced by parsing, wrapped in a `Some`, if parsing succeeded, `None` o.w.
     */
    def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean, suffixDescr: => List[String]): U

    /**
     * @param suffixDescr description of the following parser(s)
     * @return a description of the expected tokens, considering the next parser and potentially the following ones, recursively
     */
    final def firstExpectedDescr(suffixDescr: => List[String]): List[String] = description.map(List(_)).getOrElse(firstExpectedDescrImpl(suffixDescr))

    private[primitives] def firstExpectedDescrImpl(suffixDescr: => List[String]): List[String]

    /**
     * Parsers concatenation
     */
    def :::[L](left: AnyTreeParser[L]): AnyTreeParser[L ^: U] = NonFinalConcat(left, this)

    /**
     * Parsers concatenation
     */
    def :::(leftIgnored: Ignored): AnyTreeParser[U] = leftIgnored.ignoredAnyTreeParser ::: this map {
      case _ ^: r => r
    }

    /**
     * @return a parser choosing the parser among `this` and `right` that matches the token
     *
     *         The parser throws an exception reporting that parser is not LL1 if both `this` and `right` match some token it is given
     */
    final infix def OR[T](right: AnyTreeParser[T])(implicit errorReporter: ErrorReporter): AnyTreeParser[U | T] =
      NonFinalDisjunction(this, right, errorReporter)

    /**
     * Creates a new parser that transforms the `U` produced by this parser into a `T` using `f`
     */
    infix def map[T](f: U => T): AnyTreeParser[T] = {
      val original = this
      new AnyTreeParser[T] {
        export original.admits

        override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean, suffixDescr: => List[String]): T = {
          val pos = ll1Iterator.current.position
          val res = f(original.extract(ll1Iterator, suffixAdmits, suffixDescr))
          setPositionIfAst(res, pos)
          res
        }

        export original.firstExpectedDescrImpl
      }
    }

    infix def recover(skipUntil: Token => Boolean): AnyTreeParser[Option[U]] = {
      val original = this
      new AnyTreeParser[Option[U]] {
        export original.admits

        override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean, suffixDescr: => List[String]): Option[U] =
          tryRecover(ll1Iterator, skipUntil)(original.extract(ll1Iterator, suffixAdmits, suffixDescr))

        export original.firstExpectedDescrImpl
      }
    }

    protected def tryRecover[T](ll1Iterator: LL1Iterator, skipUntil: Token => Boolean)(extract: => T): Option[T] = try {
      Some(extract)
    } catch {
      case ParsingMismatchSignal() =>
        while (ll1Iterator.current.token != EndOfFileToken && !skipUntil(ll1Iterator.current.token)) {
          ll1Iterator.moveForward()
        }
        None
    }

  }

  /**
   * Object able to parse a `ParseTree` without considering the (possibly nonexistent) next parser
   */
  sealed abstract class FinalTreeParser[+U] extends AnyTreeParser[U] {

    def admits(ll1Iterator: LL1Iterator): Boolean

    def extract(ll1Iterator: LL1Iterator): U

    def firstExpectedDescr: List[String]

    override def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean = admits(ll1Iterator)

    override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean,
                         suffixDescr: => List[String]): U = extract(ll1Iterator)

    override private[primitives] def firstExpectedDescrImpl(suffixDescr: => List[String]): List[String] = firstExpectedDescr

    final override infix def map[T](f: U => T): FinalTreeParser[T] = {
      val original = this
      new FinalTreeParser[T] {
        export original.admits

        override def extract(ll1Iterator: LL1Iterator): T = {
          val pos = ll1Iterator.current.position
          val res = f(original.extract(ll1Iterator))
          setPositionIfAst(res, pos)
          res
        }

        export original.firstExpectedDescr
      }
    }

    final override infix def recover(skipUntil: Token => Boolean): FinalTreeParser[Option[U]] = {
      val original = this
      new FinalTreeParser[Option[U]] {
        export original.admits

        override def extract(ll1Iterator: LL1Iterator): Option[U] =
          tryRecover(ll1Iterator, skipUntil)(original.extract(ll1Iterator))

        export original.firstExpectedDescr
      }
    }

    final override def :::[L](left: AnyTreeParser[L]): FinalTreeParser[L ^: U] = {
      FinalConcat(left, this)
    }

    final override def :::(leftIgnored: Ignored): FinalTreeParser[U] = {
      leftIgnored.ignoredAnyTreeParser ::: this map {
        case _ ^: r => r
      }
    }

    /**
     * @return a parser choosing the parser among `this` and `right` that matches the token
     *
     *         The parser throws an exception reporting that parser is not LL1 if both `this` and `right` match some token it is given
     */
    final infix def OR[T](right: FinalTreeParser[T])(implicit errorReporter: ErrorReporter): FinalTreeParser[U | T] =
      FinalDisjunction(this, right, errorReporter)

  }

  trait Ignored {
    def ignoredAnyTreeParser: AnyTreeParser[?]
  }

  final case class NonFinalIgnored(ignored: AnyTreeParser[?]) extends Ignored {

    override def ignoredAnyTreeParser: AnyTreeParser[?] = ignored

    def :::[T](left: AnyTreeParser[T]): AnyTreeParser[T] = {
      left ::: ignored map {
        case r ^: _ => r
      }
    }

    def :::(leftIgnored: Ignored): NonFinalIgnored = {
      (leftIgnored ::: ignored).ignored
    }

    infix def OR(right: Ignored)(implicit errorReporter: ErrorReporter): NonFinalIgnored = {
      (this.ignored OR right.ignoredAnyTreeParser).ignored
    }
  }

  final case class FinalIgnored(ignored: FinalTreeParser[?]) extends Ignored {

    override def ignoredAnyTreeParser: AnyTreeParser[?] = ignored

    def :::[T](left: AnyTreeParser[T]): FinalTreeParser[T] = {
      left ::: ignored map {
        case r ^: _ => r
      }
    }

    def :::(leftIgnored: Ignored): FinalIgnored = {
      (leftIgnored ::: ignored).ignored
    }

    infix def OR(right: FinalIgnored)(implicit errorReporter: ErrorReporter): FinalIgnored = {
      (this.ignored OR right.ignored).ignored
    }

    infix def OR(right: NonFinalIgnored)(implicit errorReporter: ErrorReporter): NonFinalIgnored = {
      (this.ignored OR right.ignored).ignored
    }

  }

  private final case class FinalConcat[+L, +R](left: AnyTreeParser[L],
                                               right: FinalTreeParser[R])
    extends FinalTreeParser[L ^: R] {

    override def admits(ll1Iterator: LL1Iterator): Boolean = left.admits(ll1Iterator, right.admits(ll1Iterator))

    override def extract(ll1Iterator: LL1Iterator): L ^: R = {
      left.extract(ll1Iterator, right.admits(ll1Iterator), right.firstExpectedDescr) ^: right.extract(ll1Iterator)
    }

    override def firstExpectedDescr: List[String] = left.firstExpectedDescr(right.firstExpectedDescr)
  }

  private final case class NonFinalConcat[+L, +R](left: AnyTreeParser[L],
                                                  right: AnyTreeParser[R])
    extends AnyTreeParser[L ^: R] {

    override def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean = {
      left.admits(ll1Iterator, right.admits(ll1Iterator, suffixAdmits))
    }

    override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean,
                         suffixDescr: => List[String]): L ^: R = {
      left.extract(ll1Iterator, right.admits(ll1Iterator, suffixAdmits), right.firstExpectedDescr(suffixDescr)) ^: right.extract(ll1Iterator, suffixAdmits, suffixDescr)
    }

    override private[primitives] def firstExpectedDescrImpl(suffixDescr: => List[String]): List[String] = left.firstExpectedDescr(right.firstExpectedDescr(suffixDescr))
  }

  private final case class FinalDisjunction[+L, +R](left: FinalTreeParser[L], right: FinalTreeParser[R], errorReporter: ErrorReporter)
    extends FinalTreeParser[L | R] {

    override def admits(ll1Iterator: LL1Iterator): Boolean = {
      left.admits(ll1Iterator) || right.admits(ll1Iterator)
    }

    override def extract(ll1Iterator: LL1Iterator): L | R = {
      val leftAdmits = left.admits(ll1Iterator)
      val rightAdmits = right.admits(ll1Iterator)
      if (leftAdmits && rightAdmits) {
        reportNonLL1Error(ll1Iterator, left.firstExpectedDescr, right.firstExpectedDescr, "FinalDisjunction")
      }
      else if leftAdmits then left.extract(ll1Iterator)
      else if rightAdmits then right.extract(ll1Iterator)
      else {
        reportMismatch(errorReporter, firstExpectedDescr,
          ll1Iterator.current.token.strValue, ll1Iterator.current.position)
      }
    }

    override def firstExpectedDescr: List[String] = left.firstExpectedDescr ++ right.firstExpectedDescr
  }

  private final case class NonFinalDisjunction[+L, +R](left: AnyTreeParser[L], right: AnyTreeParser[R], errorReporter: ErrorReporter)
    extends AnyTreeParser[L | R] {

    override def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean = {
      left.admits(ll1Iterator, suffixAdmits) || right.admits(ll1Iterator, suffixAdmits)
    }

    override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean, suffixDescr: => List[String]): L | R = {
      val leftAdmits = left.admits(ll1Iterator, suffixAdmits)
      val rightAdmits = right.admits(ll1Iterator, suffixAdmits)
      if (leftAdmits && rightAdmits) {
        reportNonLL1Error(
          ll1Iterator, left.firstExpectedDescr(suffixDescr),
          right.firstExpectedDescr(suffixDescr), "NonFinalDisjunction"
        )
      }
      else if leftAdmits then left.extract(ll1Iterator, suffixAdmits, suffixDescr)
      else if rightAdmits then right.extract(ll1Iterator, suffixAdmits, suffixDescr)
      else {
        reportMismatch(errorReporter, firstExpectedDescr(suffixDescr),
          ll1Iterator.current.token.strValue, ll1Iterator.current.position)
      }
    }

    override private[primitives] def firstExpectedDescrImpl(suffixDescr: => List[String]): List[String] =
      left.firstExpectedDescr(suffixDescr) ++ right.firstExpectedDescr(suffixDescr)
  }

  private abstract sealed class AbstractExtractorTreeParser[+U] extends FinalTreeParser[U] {

    val pf: PartialFunction[Token, ?]

    override def admits(ll1Iterator: LL1Iterator): Boolean =
      pf.isDefinedAt(ll1Iterator.current.token)

  }

  private final case class ExtractorTreeParser[+U]
  (pf: PartialFunction[Token, U], firstExpectedDescr: List[String], errorReporter: ErrorReporter)
    extends AbstractExtractorTreeParser[U] {

    private val liftedPf = pf.lift

    override def extract(ll1Iterator: LL1Iterator): U = {
      val extractedPosTok = ll1Iterator.moveForward()
      liftedPf.apply(extractedPosTok.token) match {
        case None =>
          reportMismatch(errorReporter, firstExpectedDescr, extractedPosTok.token.strValue, extractedPosTok.position)
        case Some(u) => u
      }
    }
  }

  private final case class ExtractorTreeParserPositioned[+U]
  (pf: PartialFunction[Token, U], firstExpectedDescr: List[String], errorReporter: ErrorReporter)
    extends AbstractExtractorTreeParser[(U, Position)] {

    private val liftedPf = pf.lift

    override def extract(ll1Iterator: LL1Iterator): (U, Position) = {
      val extractedPosTok = ll1Iterator.moveForward()
      liftedPf.apply(extractedPosTok.token) match {
        case None =>
          reportMismatch(errorReporter, firstExpectedDescr, extractedPosTok.token.strValue, extractedPosTok.position)
        case Some(u) => (u, extractedPosTok.position)
      }
    }
  }

  private final case class OptionalTreeParser[T](optional: AnyTreeParser[T], errorReporter: ErrorReporter)
    extends AnyTreeParser[Option[T]] {

    override def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean = {
      optional.admits(ll1Iterator, suffixAdmits) || suffixAdmits
    }

    override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean,
                         suffixDescr: => List[String]): Option[T] = {
      val optAdmitsVal = optional.admits(ll1Iterator, suffixAdmits)
      val suffixAdmitsVal = suffixAdmits
      if (optAdmitsVal && suffixAdmitsVal) {
        reportNonLL1Error(ll1Iterator, optional.firstExpectedDescr(suffixDescr), suffixDescr, "OptionalTreeParser")
      }
      else if optAdmitsVal then Some(optional.extract(ll1Iterator, suffixAdmits, suffixDescr))
      else if suffixAdmitsVal then None
      else {
        reportMismatch(errorReporter, firstExpectedDescr(suffixDescr), ll1Iterator.current.token.strValue,
          ll1Iterator.current.position)
      }
    }

    override private[primitives] def firstExpectedDescrImpl(suffixDescr: => List[String]): List[String] = optional.firstExpectedDescr(suffixDescr) ++ suffixDescr
  }

  private def reportMismatch(errorReporter: ErrorReporter, expectedDescr: List[String],
                             found: String, pos: Position): Nothing = {
    val thresholdForDisplayExp = 3
    val msg = s"unexpected token: '$found'" ++ {
      if expectedDescr.size == 1 then s", expected ${expectedDescr.head}"
      else if 0 <= expectedDescr.size && expectedDescr.size <= thresholdForDisplayExp then s", expected ${expectedDescr.mkString(" or ")}"
      else ""
    }
    errorReporter.report(Err(CompilationStep.Parsing, msg, Some(pos)))
    throw ParsingMismatchSignal()
  }

  private def reportNonLL1Error(ll1Iterator: LL1Iterator, opt1: Any, opt2: Any, situationDescr: String): Nothing = {
    val nKeep = 10
    val remaining = ll1Iterator.current :: ll1Iterator.remaining
    throw new Error(s"grammar is not LL1: conflict found: $situationDescr at ${
      remaining.take(nKeep)
    }${if remaining.size > nKeep then "..." else ""}\n" +
      s"Option 1 expected: $opt1\n" + s"Option 2 expected: $opt2")
  }

  private def setPositionIfAst(optObj: Any, pos: Position, maxPropagationDepth: Int = 2): Unit = {
    if (maxPropagationDepth >= 0) {
      optObj match {
        case ast: Ast =>
          if (ast.getPosition.isEmpty) {
            ast.setPosition(pos)
          }
          for child <- ast.children do {
            setPositionIfAst(Some(child), ast.getPosition.get, maxPropagationDepth - 1)
          }
        case _ => ()
      }
    }
  }

}
