package compiler.lexer

import compiler.ExprToStringMacro.exprToString

import scala.annotation.tailrec

object Matchers {

  /**
   * Takes `target` if the matched string starts with it
   */
  def string(target: String): Matcher = StringMatcher(target)

  /**
   * Takes the longest prefix of the matched string s.t. all chars match the predicate.
   * Fails if there is not at least one such char.
   */
  inline def string(inline predicate: Char => Boolean): Matcher = repeatNon0(char(predicate))

  /**
   * Matches the given char
   */
  def char(c: Char): Matcher = CharMatcher(c)

  /**
   * Matches any char
   */
  def anyChar: Matcher = AnyCharMatcher

  /**
   * Matches any char except the given one
   */
  def anyCharBut(chars: Char*): Matcher = BlacklistedCharsMatcher(chars.toSet)

  /**
   * Matches any char in the given range
   */
  def charInRange(min: Char, max: Char): Matcher = CharRangeMatcher(min, max)

  /**
   * Takes the longest prefix s.t. all chars are in the given range.
   * Fails if there is not at least one such char.
   */
  def stringInRange(min: Char, max: Char): Matcher = repeatNon0(charInRange(min, max))

  /**
   * Matches a char according to the given predicate
   */
  inline def char(inline predicate: Char => Boolean): Matcher =
    PredicateSingleCharMatcher(
      predicate,
      removeUselessPredicateStringPart(exprToString(predicate))
    )

  extension (left: Matcher){
    /**
     * Matchers concatenation (`left` and then `right`)
     */
    def ++(right: Matcher): Matcher = {
      (left, right) match {
        case (SeqMatcher(leftMatchers), SeqMatcher(rightMatchers)) => SeqMatcher(leftMatchers ++ rightMatchers)
        case (SeqMatcher(leftMatchers), _) => SeqMatcher(leftMatchers :+ right)
        case (_, SeqMatcher(rightMatchers)) => SeqMatcher(left :: rightMatchers)
        case (_, _) => SeqMatcher(List(left, right))
      }
    }

    /**
     * Matchers disjunction (`left` or `right`)
     */
    def |(right: Matcher): Matcher = {
      (left, right) match {
        case (DisjunctionMatcher(leftMatchers), DisjunctionMatcher(rightMatchers)) =>
          DisjunctionMatcher(leftMatchers ++ rightMatchers)
        case (DisjunctionMatcher(leftMatchers), _) => DisjunctionMatcher(leftMatchers :+ right)
        case (_, DisjunctionMatcher(rightMatchers)) => DisjunctionMatcher(left +: rightMatchers)
        case (_, _) => DisjunctionMatcher(LazyList(left, right))
      }
    }
  }

  /**
   * Repeat any number of times
   */
  def repeat(repeatedMatcher: Matcher): Matcher = RepetitionMatcher(repeatedMatcher)

  /**
   * Repeat at least once
   */
  def repeatNon0(repeatedMatcher: Matcher): Matcher = repeatedMatcher ++ repeat(repeatedMatcher)

  /**
   * Match if any, o.w. do nothing
   */
  def opt(optMatcher: Matcher): Matcher = optMatcher | EmptyMatcher

  sealed trait Matcher {

    /**
     * @return the length of the longest prefix of `str` s.t. the matcher matches it (possibly 0 in some cases),
     *         wrapped in `Some`, or `None` if matching failed
     */
    def matches(str: String): Option[Int]

    /**
     * @return (prefix, suffix), where:
     *         - prefix macthes the matcher
     *         - suffix is the rest of the string
     */
    final def split(str: String): Option[(String, String)] = matches(str).map(idx => str.splitAt(idx))

    /**
     * Takes the matching prefix and transforms it into a `T` according to `transform`
     * @param transform the transformation to apply to the prefix
     * @param str the string to match
     * @return `Some`((transformation result, rest of the string, length of the matched prefix)),
     *         or `None` if matching failed
     */
    final infix def into[T](transform: String => T)(str: String): Option[(T, String, Int)] = {
      split(str).map((tokStr, remStr) => (transform(tokStr), remStr, tokStr.length))
    }

    /**
     * Same as [[into]] but with `transform` returning an option
     */
    final infix def intoOpt[T](transform: String => Option[T])(str: String): Option[(T, String, Int)] = {
      split(str).flatMap {
        (tokStr, remStr) => transform(tokStr).map((_, remStr, tokStr.length))
      }
    }

    /**
     * Same as [[into]] but the preduced `T` is constant
     */
    final infix def into[T](transformResult: T)(str: String): Option[(T, String, Int)] = {
      into((_: String) => transformResult)(str)
    }
  }

  private object EmptyMatcher extends Matcher {
    override def matches(str: String): Option[Int] = Some(0)
  }
  
  private object AnyCharMatcher extends Matcher {
    override def matches(str: String): Option[Int] = Some(if str.nonEmpty then 1 else 0)
  }

  private final case class StringMatcher(target: String) extends Matcher {
    override def matches(str: String): Option[Int] = {
      if str.startsWith(target) then Some(target.length)
      else None
    }

    override def toString: String = s"$target"
  }

  private final case class CharMatcher(target: Char) extends Matcher {
    override def matches(str: String): Option[Int] = {
      str.headOption.filter(_ == target).map(_ => 1)
    }

    override def toString: String = s"'$target'"
  }
  
  private final case class BlacklistedCharsMatcher(blacklistedChars: Set[Char]) extends Matcher {
    override def matches(str: String): Option[Int] = {
      str.headOption.filter(!blacklistedChars.contains(_)).map(_ => 1)
    }

    override def toString: String = s"? != ${blacklistedChars.mkString(",")}"
  }

  private final case class CharRangeMatcher(min: Char, max: Char) extends Matcher {
    override def matches(str: String): Option[Int] = {
      str.headOption.filter(c => min <= c && c <= max).map(_ => 1)
    }

    override def toString: String = s"['$min','$max']"
  }

  private final case class PredicateSingleCharMatcher(predicate: Char => Boolean, predStr: String) extends Matcher {

    override def matches(str: String): Option[Int] = {
      str.headOption.flatMap(c => if predicate(c) then Some(1) else None)
    }

    override def toString: String = s"$predStr?"
  }

  private final case class SeqMatcher(matchers: List[Matcher]) extends Matcher {
    override def matches(str: String): Option[Int] = {

      @tailrec def matchesRem(remStr: String, remMatchers: List[Matcher], cnt: Int): Option[Int] = {
        remMatchers match {
          case Nil => Some(cnt)
          case headMatcher :: tailMatchers => {
            headMatcher.matches(remStr) match {
              case None => None
              case Some(len) => matchesRem(remStr.substring(len), tailMatchers, cnt + len)
            }
          }
        }
      }

      matchesRem(str, matchers, 0)
    }

    override def toString: String = matchers.mkString("( ", " ) ++ ( ", " )")
  }

  private final case class DisjunctionMatcher(matchers: LazyList[Matcher]) extends Matcher {
    override def matches(str: String): Option[Int] = {
      matchers.map(_.matches(str)).find(_.isDefined).flatten
    }

    override def toString: String = matchers.mkString("( ", " ) | ( ", " )")
  }

  private final case class RepetitionMatcher(repeatedMatcher: Matcher) extends Matcher {
    override def matches(str: String): Option[Int] = {

      @tailrec def matchesRem(remStr: String, cnt: Int): Option[Int] = {
        val matchRes = repeatedMatcher.matches(remStr)
        matchRes match {
          case None | Some(0) => Some(cnt)
          case Some(len) => {
            val newRem = remStr.substring(len)
            matchesRem(newRem, cnt + len)
          }
        }
      }

      matchesRem(str, 0)
    }

    override def toString: String = s"($repeatedMatcher)*"
  }

  private def removeUselessPredicateStringPart(str: String): String = {
    try {

      // this one is not inlined, which avoids endless expansion
      def char(pred: Char => Boolean): Matcher = PredicateSingleCharMatcher(pred, "<unavailable>")

      def stringPred(pred: Char => Boolean): Matcher = repeatNon0(char(pred))

      def string(target: String): Matcher = StringMatcher(target)

      val matcher =
        string("((_$")
          ++ stringPred(_.isDigit)
          ++ string(": scala.Char) => ")
          ++ opt(string("scala.Predef.charWrapper(_$")
          ++ stringPred(_.isDigit)
          ++ string(")."))
      matcher.split(str) match {
        case Some((_, rem)) => "(" ++ rem
        case None => str
      }
    } catch {
      case _: Throwable => "<description not available>"
    }
  }

}

