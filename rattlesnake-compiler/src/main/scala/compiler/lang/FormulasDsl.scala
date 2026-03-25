package compiler.lang

import compiler.lang.Formulas.*

object FormulasDsl {

  extension (l: Formula) {

    infix def +(r: Formula): Formula = Plus(l, r)
    infix def +(r: Int): Formula = Plus(l, IntConst(r))
    infix def -(r: Formula): Formula = Plus(l, Neg(r))
    infix def -(r: Int): Formula = Plus(l, IntConst(-r))
    infix def *(r: Formula): Formula = Times(l, r)
    infix def /(r: Formula): Formula = DivBy(l, r)
    infix def %(r: Formula): Formula = Modulo(l, r)

    infix def ===(r: Formula): Formula = Equality(l, r)
    infix def <(r: Formula): Formula = LessThan(l, r)
    infix def <=(r: Formula): Formula = LessOrEq(l, r)

    def unary_- = Neg(l)

  }

  given autoConvertIntToIConst: Conversion[Int, Formula] = IntConst(_)

}
