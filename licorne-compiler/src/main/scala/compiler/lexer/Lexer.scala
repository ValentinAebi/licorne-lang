package compiler.lexer

import compiler.io.SourceCodeProvider
import compiler.irs.tokens.Tokens.*
import compiler.lang.{Keyword, Operator}
import compiler.lexer.Matchers.*
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.reporting.Errors.{Err, ErrorReporter, Fatal}
import compiler.reporting.Position

import scala.annotation.tailrec
import scala.util.{Failure, Success}

final class Lexer(errorReporter: ErrorReporter) extends CompilerStep[SourceCodeProvider, (List[PositionedToken], String)] {

  /*
   * tokenization is performed line-by-line, there is no support for multi-line tokens
   */

  // Elementary matchers -----------------------------------------------------------------

  private val uppercaseLetter: Matcher = charInRange('A', 'Z')
  private val lowercaseLetter: Matcher = charInRange('a', 'z')

  private val digit: Matcher = charInRange('0', '9')
  private val digitsSeq: Matcher = stringInRange('0', '9')

  private val underscore: Matcher = char('_')
  private val letterDigitUnderscore: Matcher = uppercaseLetter | lowercaseLetter | digit | underscore


  // Composite matchers ------------------------------------------------------------------

  /**
   * See [[Matcher.into]]
   */
  private type IntoResult = (Token, String, Int)

  private val keywordsMatchers: List[String => Option[IntoResult]] =
    Keyword.values.toList.map { kw =>
      string(kw.str) into KeywordToken(kw)
    }

  private val operatorsMatchers: List[String => Option[IntoResult]] =
    Operator.values.toList.map { op =>
      string(op.str) into OperatorToken(op)
    }

  private val explicitelyDefinedMatchersByPriorityOrder: List[String => Option[IntoResult]] = List(

    string(_.isWhitespace) into SpaceToken,
    
    string("unit") into UnitLitToken,

    string("true") | string("false") into {
      str => BoolLitToken(str.toBoolean)
    },

    uppercaseLetter ++ repeat(letterDigitUnderscore) into {
      FirstUppercaseIdentifierToken(_)
    },

    lowercaseLetter ++ repeat(letterDigitUnderscore) into {
      FirstLowercaseIdentifierToken(_)
    },

    digitsSeq intoOpt {
      str => str.toIntOption.map(IntLitToken.apply)
    },

    digitsSeq ++ char('.') ++ digitsSeq intoOpt {
      str => str.toDoubleOption.map(DoubleLitToken.apply)
    },

    char('\'') ++ char('\\') ++ char('n') ++ char('\'') into {
      str => CharLitToken('\n')
    },

    char('\'') ++ anyChar ++ char('\'') into {
      str => CharLitToken(str(1))
    },

    char('"') ++ repeat(anyCharBut('"')) ++ char('"') into {
      str => StringLitToken(str.drop(1).dropRight(1).replace("\\n", "\n"))
    },

    string("//") ++ repeat(anyChar) into {
      CommentToken(_)
    },
  )

  private val matchersByPriorityOrder =
    keywordsMatchers ++ operatorsMatchers ++ explicitelyDefinedMatchersByPriorityOrder


  // Tokenization ------------------------------------------------------------------------

  private def tokenizeLine(line: String, lineIdxZeroBased: Int, srcCodeProvider: SourceCodeProvider): List[(Token, Int)] = {

    // takes longest match, if two candidates with maximum match then first in order is taken
    @tailrec def tokenizeRemaining(rem: String, tokensReversed: List[(Token, Int)], colZeroBased: Int): List[(Token, Int)] = {
      if rem.isEmpty then ((EndlToken, colZeroBased) :: tokensReversed).reverse
      else {
        val matcherRes = matchersByPriorityOrder
          .flatMap(_.apply(rem))
          .maxByOption(_._3)  // take longest match
        matcherRes match {

          case Some((newTok, newRem, len)) =>
            tokenizeRemaining(newRem, (newTok, colZeroBased) :: tokensReversed, colZeroBased + len)

          case None => {
            errorReporter.report(Err(CompilationStep.Lexing,
              s"syntax error: '${stringLengthLimited(20, rem)}'", Some(Position(srcCodeProvider, lineIdxZeroBased + 1, colZeroBased + 1))))
            val splitIdx = rem.indexOf(' ')
            if (splitIdx >= 0) {
              val (errTokStr, newRem) = rem.splitAt(splitIdx)
              tokenizeRemaining(newRem, (ErrorToken(errTokStr), colZeroBased) :: tokensReversed, colZeroBased + splitIdx)
            }
            else ((ErrorToken(rem), colZeroBased) :: tokensReversed).reverse
          }
        }
      }
    }

    tokenizeRemaining(line, Nil, 0)
  }

  /**
   * @return `str`, unless it is too long in which case it is truncated and postfixed with "..."
   */
  private def stringLengthLimited(maxLen: Int, str: String): String = {
    if str.length > maxLen then s"$str..."
    else str
  }

  override def apply(sourceCodeProvider: SourceCodeProvider): (List[PositionedToken], String) = {
    sourceCodeProvider.lines match {

      case Failure(_) => errorReporter.reportFatal(Fatal(CompilationStep.Lexing,
        s"could not read source code from source '${sourceCodeProvider.name}'", None))

      case Success(lines) => {
        val indexedLines = lines.toList.zipWithIndex
        val tokenizedLines = indexedLines.map((line, idx) => tokenizeLine(line, idx, sourceCodeProvider))
        errorReporter.displayAndTerminateIfErrors()
        val positionedTokens =
          for (line, lineIdxZeroBased) <- tokenizedLines.zipWithIndex; (token, colIdx) <- line yield {
            PositionedToken(token, Position(sourceCodeProvider, line = lineIdxZeroBased + 1, col = colIdx + 1))
          }
        (positionedTokens, sourceCodeProvider.name)
      }
    }
  }

}
