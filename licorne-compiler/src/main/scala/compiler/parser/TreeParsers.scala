package compiler.parser

import compiler.ExprToStringMacro.exprToString
import compiler.irs.asts.Asts.Ast
import compiler.irs.tokens.Tokens.*
import compiler.parser.ParseTree.^:
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position

/**
 * Parsers for some parts of the syntax
 */
object TreeParsers {

  /**
   * Creates a parser that uses a `PartialFunction`
   * @param expectedDescr description of the expected token (for error reporting)
   * @param pf the `PartialFunction`, defined at tokens treated by this parser and returning an instance of `U`
   * @param errorReporter errors will be saved there
   * @return the created parser
   */
  inline def treeParser[U](expectedDescr: String)(inline pf: PartialFunction[Token, U])
                          (implicit errorReporter: ErrorReporter): FinalTreeParser[U] = {
    ExtractorTreeParser(pf, expectedDescr, errorReporter, pfToDescr(pf)) setNameResetable expectedDescr
  }

  /**
   * Creates a parser that uses a `PartialFunction` and returns the position along with the result
   *
   * @param expectedDescr description of the expected token (for error reporting)
   * @param pf            the `PartialFunction`, defined at tokens treated by this parser and returning an instance of `U`
   * @param errorReporter errors will be saved there
   * @return the created parser
   */
  inline def treeParserPositioned[U](expectedDescr: String)(inline pf: PartialFunction[Token, U])
                                 (implicit errorReporter: ErrorReporter): FinalTreeParser[(U, Position)] = {
    ExtractorTreeParserPositioned(pf, expectedDescr, errorReporter, pfToDescr(pf)) setNameResetable expectedDescr
  }

  /**
   * Creates a parser that returns a `Some[U]` with the result of `optional` if `optional` accepts the token and `None` o.w.
   */
  def opt[U](optional: AnyTreeParser[U])
            (implicit errorReporter: ErrorReporter): AnyTreeParser[Option[U]] = {
    OptionalTreeParser(optional, errorReporter) setNameResetable s"opt(${optional.getName})"
  }

  /**
   * Creates a parser that admits any number of repetitions of the given parser
   */
  def repeat[U](repeated: AnyTreeParser[U])(implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = {
    recursive {
      opt(repeated ::: repeat(repeated)) map {
        case Some(head ^: tail) => head :: tail
        case None => Nil
      }
    } setNameResetable s"repeat(${repeated.getName})"
  }

  /**
   * Creates a parser that admits any non zero number of repetitions of the given parser
   */
  def repeatNonZero[U](repeated: AnyTreeParser[U])(implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = {
    repeated ::: repeat(repeated) map {
      case head ^: tail => head :: tail
    } setNameResetable s"repeatNonZero(${repeated.getName})"
  }

  /**
   * Creates a parser that admits any number of repetitions of the given parser, separated by `sep`
   */
  def repeatWithSep[U](repeated: AnyTreeParser[U], sep: Ignored)
                      (implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = {
    opt(repeated ::: repeat(sep ::: repeated)) map {
      case Some(head ^: tail) => head :: tail
      case None => Nil
    } setNameResetable s"repeatWithSep(${repeated.getName})"
  }

  /**
   * Creates a parser that admits any non zero number of repetitions of the given parser, separated by `sep`
   */
  def repeatWithSepNonZero[U](repeated: AnyTreeParser[U], sep: FinalIgnored)
                             (implicit errorReporter: ErrorReporter): AnyTreeParser[List[U]] = recursive {
    repeated ::: opt(sep ::: repeatWithSep(repeated, sep)) map {
      case head ^: Some(tail) => head :: tail
      case single ^: None => List(single)
    } setNameResetable s"repeatWithSepNonZero(${repeated.getName})"
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

  extension[W](self: FinalTreeParser[W]) {
    /**
     * Produces a parser that can only be used in a concatenation and whose result is ignored.
     * This parser does not require a next parser.
     */
    def ignored: FinalIgnored = FinalIgnored(self)
  }
  extension[W](self: AnyTreeParser[W]) {
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
      export underlying.firstExpectedDescr
      override def safeToStringImpl(remDepth: Int): String = underlying.safeToStringImpl(remDepth)
    } setNameResetable recursed.getName
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
      override def safeToStringImpl(remDepth: Int): String = underlying.safeToStringImpl(remDepth)
    } setNameResetable recursed.getName
  }

  /**
   * Object able to parse a `ParseTree`
   *
   * The parsing method may require info on the next parser (as arguments)
   */
  sealed abstract class AnyTreeParser[+U] {

    private var nameOpt: Option[() => String] = None
    private var nameWasSet = false

    protected[TreeParsers] infix def setNameResetable(name: => String): AnyTreeParser[U] = {
      this.nameOpt = Some(() => name)
      this
    }

    /**
     * Sets a name for this parser (useful for debugging)
     * @return `this`
     */
    infix def setName(name: String): AnyTreeParser[U] = {
      if (nameWasSet) throw IllegalStateException("parser name assigned twice")
      this.nameOpt = Some(() => name)
      nameWasSet = true
      this
    }

    def getName: String = nameOpt.map(_.apply()).getOrElse("<?>")

    /**
     * @param ll1Iterator <b> NOT MUTATED </b>
     * @param suffixAdmits function to compute whether the next parser admits the next token
     * @return `true` iff this parser admits the next token in `ll1Iterator`
     */
    def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean

    /**
     *
     * @param ll1Iterator <b> MUTATED </b> (moved forward by 1)
     * @param suffixAdmits function to compute whether the next parser admits the next token
     * @param suffixDescr description of the next parser (potentially considering the following ones recursively)
     * @param firstSuffix next parser
     * @return the `U` produced by parsing, wrapped in a `Some`, if parsing succeeded, `None` o.w.
     */
    def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean, suffixDescr: => String, firstSuffix: AnyTreeParser[?]): Option[U]

    /**
     * @param suffixDescr description of the following parser(s)
     * @return a description of the expected tokens, considering the next parser and potentially the following ones, recursively
     */
    def firstExpectedDescr(suffixDescr: => String): String

    /**
     * Parsers concatenation
     */
    def :::[L](left: AnyTreeParser[L]): AnyTreeParser[L ^: U] = {
      NonFinalConcat(left, this) setNameResetable s"${left.getName} ::: ${this.getName}"
    }

    /**
     * Parsers concatenation
     */
    def :::(leftIgnored: Ignored): AnyTreeParser[U] = {
      leftIgnored.ignoredAnyTreeParser ::: this map {
        case _ ^: r => r
      } setNameResetable s"${leftIgnored.getName} ::: ${this.getName}"
    }

    /**
     * @return a parser choosing the parser among `this` and `right` that matches the token
     *
     * The parser throws an exception reporting that parser is not LL1 if both `this` and `right` match some token it is given
     */
    final infix def OR[T](right: AnyTreeParser[T])(implicit errorReporter: ErrorReporter): AnyTreeParser[U | T] = {
      NonFinalDisjunction(this, right, errorReporter) setNameResetable s"${this.getName} OR ${right.getName}"
    }

    /**
     * Creates a new parser that transforms the `U` produced by this parser into a `T` using `f`
     */
    infix def map[T](f: U => T): AnyTreeParser[T] = {
      val original = this
      new AnyTreeParser[T] {
        export original.admits
        override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean,
                             suffixDescr: => String, firstSuffix: AnyTreeParser[?]): Option[T] = {
          val pos = ll1Iterator.current.position
          val res = original.extract(ll1Iterator, suffixAdmits, suffixDescr, firstSuffix).map(f)
          setPositionIfAst(res, pos)
          res
        }
        export original.firstExpectedDescr
        override def safeToStringImpl(remDepth: Int): String = s"mapped of ${original.safeToString(remDepth)}"
      } setNameResetable s"mapped of $getName"
    }

    // toString with a depth check to avoid infinite recursions
    protected[TreeParsers] def safeToStringImpl(remDepth: Int): String
    protected[TreeParsers] final def safeToString(remDepth: Int): String = {
      if remDepth > 0 then safeToStringImpl(remDepth - 1) else "..."
    }
    override final def toString: String = {
      s"${nameOpt.getOrElse("<?>")} ${safeToString(5)}"
    }

  }

  /**
   * Object able to parse a `ParseTree` without considering the (possibly nonexistent) next parser
   */
  sealed abstract class FinalTreeParser[+U] extends AnyTreeParser[U]{

    override final infix def setName(name: String): FinalTreeParser[U] = {
      super.setName(name)
      this
    }

    override protected[TreeParsers] final infix def setNameResetable(name: => String): FinalTreeParser[U] = {
      super.setNameResetable(name)
      this
    }

    def admits(ll1Iterator: LL1Iterator): Boolean
    def extract(ll1Iterator: LL1Iterator): Option[U]
    def firstExpectedDescr: String

    override def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean = admits(ll1Iterator)

    override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean,
                         suffixDescr: => String, firstSuffix: AnyTreeParser[?]): Option[U] = extract(ll1Iterator)

    override def firstExpectedDescr(suffixDescr: => String): String = firstExpectedDescr

    final override infix def map[T](f: U => T): FinalTreeParser[T] = {
      val original = this
      new FinalTreeParser[T] {
        export original.admits
        override def extract(ll1Iterator: LL1Iterator): Option[T] = {
          val pos = ll1Iterator.current.position
          val res = original.extract(ll1Iterator).map(f)
          setPositionIfAst(res, pos)
          res
        }
        export original.firstExpectedDescr
        override def safeToStringImpl(remDepth: Int): String = s"mapped of ${original.safeToStringImpl(remDepth)}"
      } setNameResetable s"mapped of $getName"
    }

    final override def :::[L](left: AnyTreeParser[L]): FinalTreeParser[L ^: U] = {
      FinalConcat(left, this) setNameResetable s"${left.getName} ::: ${this.getName}"
    }

    final override def :::(leftIgnored: Ignored): FinalTreeParser[U] = {
      leftIgnored.ignoredAnyTreeParser ::: this map {
        case _ ^: r => r
      } setNameResetable s"${leftIgnored.getName} ::: ${this.getName}"
    }

    /**
     * @return a parser choosing the parser among `this` and `right` that matches the token
     *
     * The parser throws an exception reporting that parser is not LL1 if both `this` and `right` match some token it is given
     */
    final infix def OR[T](right: FinalTreeParser[T])(implicit errorReporter: ErrorReporter): FinalTreeParser[U | T] = {
      FinalDisjunction(this, right, errorReporter) setNameResetable s"${this.getName} OR ${right.getName}"
    }

  }

  trait Ignored {
    def ignoredAnyTreeParser: AnyTreeParser[?]

    def getName: String = s"ignored(${ignoredAnyTreeParser.getName})"
  }

  final case class NonFinalIgnored(ignored: AnyTreeParser[?]) extends Ignored {

    override def ignoredAnyTreeParser: AnyTreeParser[?] = ignored

    def :::[T](left: AnyTreeParser[T]): AnyTreeParser[T] = {
      left ::: ignored map {
        case r ^: _ => r
      } setNameResetable s"${left.getName} ::: ${this.getName}"
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
    } setNameResetable s"${left.getName} ::: ${this.getName}"

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

    override def extract(ll1Iterator: LL1Iterator): Option[L ^: R] = {
      for
        l <- left.extract(ll1Iterator, right.admits(ll1Iterator), right.firstExpectedDescr, right)
        r <- right.extract(ll1Iterator)
      yield
        l ^: r
    }

    override def firstExpectedDescr: String = left.firstExpectedDescr(right.firstExpectedDescr)

    override protected[TreeParsers] def safeToStringImpl(remDepth: Int): String = {
      s"FinalConcat(${left.safeToString(remDepth)}, ${right.safeToString(remDepth)})"
    }
  }

  private final case class NonFinalConcat[+L, +R](left: AnyTreeParser[L],
                                                  right: AnyTreeParser[R])
    extends AnyTreeParser[L ^: R]{

    override def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean = {
      left.admits(ll1Iterator, right.admits(ll1Iterator, suffixAdmits))
    }

    override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean,
                         suffixDescr: => String, firstSuffix: AnyTreeParser[?]): Option[L ^: R] = {
      for
        l <- left.extract(ll1Iterator, right.admits(ll1Iterator, suffixAdmits), right.firstExpectedDescr(suffixDescr), right)
        r <- right.extract(ll1Iterator, suffixAdmits, suffixDescr, firstSuffix)
      yield
        l ^: r
    }

    override def firstExpectedDescr(suffixDescr: => String): String = left.firstExpectedDescr(right.firstExpectedDescr(suffixDescr))

    override protected[TreeParsers] def safeToStringImpl(remDepth: Int): String = {
      s"NonFinalConcat(${left.safeToString(remDepth)}, ${right.safeToString(remDepth)})"
    }
  }

  private final case class FinalDisjunction[+L, +R](left: FinalTreeParser[L], right: FinalTreeParser[R], errorReporter: ErrorReporter)
    extends FinalTreeParser[L | R] {

    override def admits(ll1Iterator: LL1Iterator): Boolean = {
      left.admits(ll1Iterator) || right.admits(ll1Iterator)
    }

    override def extract(ll1Iterator: LL1Iterator): Option[L | R] = {
      val leftAdmits = left.admits(ll1Iterator)
      val rightAdmits = right.admits(ll1Iterator)
      if (leftAdmits && rightAdmits) {
        reportNonLL1Error(ll1Iterator, left.firstExpectedDescr, right.firstExpectedDescr, left.getName, right.getName, "FinalDisjunction")
      }
      else if leftAdmits then left.extract(ll1Iterator)
      else if rightAdmits then right.extract(ll1Iterator)
      else {
        reportMismatch(errorReporter, firstExpectedDescr,
          ll1Iterator.current.token.strValue, ll1Iterator.current.position)
        None
      }
    }

    override def firstExpectedDescr: String = s"${left.firstExpectedDescr} or ${right.firstExpectedDescr}"

    override def safeToStringImpl(remDepth: Int): String = {
      s"FinalDisjunction(${left.safeToString(remDepth)}, ${right.safeToString(remDepth)})"
    }
  }

  private final case class NonFinalDisjunction[+L, +R](left: AnyTreeParser[L], right: AnyTreeParser[R], errorReporter: ErrorReporter)
    extends AnyTreeParser[L | R]{

    override def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean = {
      left.admits(ll1Iterator, suffixAdmits) || right.admits(ll1Iterator, suffixAdmits)
    }

    override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean,
                         suffixDescr: => String, firstSuffix: AnyTreeParser[?]): Option[L | R] = {
      val leftAdmits = left.admits(ll1Iterator, suffixAdmits)
      val rightAdmits = right.admits(ll1Iterator, suffixAdmits)
      if (leftAdmits && rightAdmits) {
        reportNonLL1Error(
          ll1Iterator, left.firstExpectedDescr(suffixDescr),
          right.firstExpectedDescr(suffixDescr), left.getName, right.getName, "NonFinalDisjunction"
        )
      }
      else if leftAdmits then left.extract(ll1Iterator, suffixAdmits, suffixDescr, firstSuffix)
      else if rightAdmits then right.extract(ll1Iterator, suffixAdmits, suffixDescr, firstSuffix)
      else {
        reportMismatch(errorReporter, firstExpectedDescr(suffixDescr),
          ll1Iterator.current.token.strValue, ll1Iterator.current.position)
        None
      }
    }

    override def firstExpectedDescr(suffixDescr: => String): String = {
      s"${left.firstExpectedDescr(suffixDescr)} or ${right.firstExpectedDescr(suffixDescr)}"
    }

    override def safeToStringImpl(remDepth: Int): String = {
      s"NonFinalDisjunction(${left.safeToString(remDepth)}, ${right.safeToString(remDepth)})"
    }
  }

  private abstract sealed class AbstractExtractorTreeParser[+U] extends FinalTreeParser[U]{

    val pf: PartialFunction[Token, ?]
    val pfCode: String

    override def admits(ll1Iterator: LL1Iterator): Boolean = {
      pf.isDefinedAt(ll1Iterator.current.token)
    }

    override def safeToStringImpl(remDepth: Int): String = {
      s"$firstExpectedDescr: $pfCode"
    }

  }

  private final case class ExtractorTreeParser[+U]
  (pf: PartialFunction[Token, U], firstExpectedDescr: String, errorReporter: ErrorReporter, pfCode: String)
    extends AbstractExtractorTreeParser[U] {

    private val liftedPf = pf.lift

    override def extract(ll1Iterator: LL1Iterator): Option[U] = {
      val extractedPosTok = ll1Iterator.moveForward()
      liftedPf.apply(extractedPosTok.token) match {
        case None =>
          reportMismatch(errorReporter, firstExpectedDescr, extractedPosTok.token.strValue, extractedPosTok.position)
          None
        case s@Some(_) => s
      }
    }
  }

  private final case class ExtractorTreeParserPositioned[+U]
  (pf: PartialFunction[Token, U], firstExpectedDescr: String, errorReporter: ErrorReporter, pfCode: String)
    extends AbstractExtractorTreeParser[(U, Position)] {

    private val liftedPf = pf.lift

    override def extract(ll1Iterator: LL1Iterator): Option[(U, Position)] = {
      val extractedPosTok = ll1Iterator.moveForward()
      liftedPf.apply(extractedPosTok.token) match {
        case None =>
          reportMismatch(errorReporter, firstExpectedDescr, extractedPosTok.token.strValue, extractedPosTok.position)
          None
        case Some(u) => Some((u, extractedPosTok.position))
      }
    }
  }

  private final case class OptionalTreeParser[T](optional: AnyTreeParser[T], errorReporter: ErrorReporter)
    extends AnyTreeParser[Option[T]]{

    override def admits(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean): Boolean = {
      optional.admits(ll1Iterator, suffixAdmits) || suffixAdmits
    }

    override def extract(ll1Iterator: LL1Iterator, suffixAdmits: => Boolean,
                         suffixDescr: => String, firstSuffix: AnyTreeParser[?]): Option[Option[T]] = {
      val optAdmitsVal = optional.admits(ll1Iterator, suffixAdmits)
      val suffixAdmitsVal = suffixAdmits
      if (optAdmitsVal && suffixAdmitsVal){
        reportNonLL1Error(ll1Iterator, optional.firstExpectedDescr(suffixDescr), suffixDescr,
          optional.getName, firstSuffix.getName, "OptionalTreeParser")
      }
      else if optAdmitsVal then optional.extract(ll1Iterator, suffixAdmits, suffixDescr, firstSuffix).map(Some(_))
      else if suffixAdmitsVal then Some(None)
      else {
        reportMismatch(errorReporter, firstExpectedDescr(suffixDescr), ll1Iterator.current.token.strValue,
          ll1Iterator.current.position)
        None
      }
    }

    override def firstExpectedDescr(suffixDescr: => String): String = s"${optional.firstExpectedDescr(suffixDescr)} or $suffixDescr"

    override protected[TreeParsers] def safeToStringImpl(remDepth: Int): String = {
      s"Optional(${optional.safeToString(remDepth)})"
    }
  }

  private def reportMismatch(errorReporter: ErrorReporter, expectedDescr: String,
                             found: String, pos: Position): Unit = {
    val msg = s"expected $expectedDescr, found $found"
    errorReporter.report(Err(CompilationStep.Parsing, msg, Some(pos)))
  }

  private def reportNonLL1Error(ll1Iterator: LL1Iterator,
                                      opt1: Any, opt2: Any, name1: String,
                                      name2: String, situationDescr: String): Nothing = {
    val nKeep = 10
    val remaining = ll1Iterator.current :: ll1Iterator.remaining
    throw new Error(s"grammar is not LL1: conflict found: $situationDescr at ${
      remaining.take(nKeep)
    }${if remaining.size > nKeep then "..." else ""}\n" +
      s"Option 1 ($name1) expected: $opt1\n" + s"Option 2 ($name2) expected: $opt2")
  }

  private def setPositionIfAst(optObj: Option[Any], pos: Position, maxPropagationDepth: Int = 2): Unit = {
    if (maxPropagationDepth >= 0){
      optObj match {
        case Some(ast: Ast) =>
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

  private inline def pfToDescr(inline pf: PartialFunction[?, ?]): String = {
    try {
      val raw = exprToString(pf)
      raw.dropWhile(c => c != '{').dropRight(1).replaceAll("compiler.Tokens.", "")
    } catch {
      case _: Throwable => "<description not available>"
    }
  }

}
