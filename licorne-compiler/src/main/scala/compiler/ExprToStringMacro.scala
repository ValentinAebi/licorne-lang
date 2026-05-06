package compiler

import scala.quoted.*

object ExprToStringMacro {

  /**
   * Debug macro that transforms `expr` into a `String` of its source code
   */
  inline def exprToString(inline expr: Any): String = ${exprToStringImpl('expr)}

  private def exprToStringImpl(expr: Expr[Any])(using Quotes): Expr[String] = {
    import quotes.reflect._
    Expr(expr.asTerm.show)
  }

}
