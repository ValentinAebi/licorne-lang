package compiler.lang

import compiler.lang.Types.PrimitiveType.*
import compiler.lang.Types.{PrimitiveType, Type}
import compiler.stdlib.StdLib.stringType

enum TypeConversion(val from: PrimitiveType, val to: Type) {

  case Int2Double extends TypeConversion(IntType, DoubleType)
  case Double2Int extends TypeConversion(DoubleType, IntType)
  case IntToChar extends TypeConversion(IntType, CharType)
  case CharToInt extends TypeConversion(CharType, IntType)

  case IntToString extends TypeConversion(IntType, stringType)
  case BoolToString extends TypeConversion(BoolType, stringType)
  case CharToString extends TypeConversion(CharType, stringType)
  case DoubleToString extends TypeConversion(DoubleType, stringType)
}

object TypeConversion {

  def conversionFor(from: Type, to: Type): Option[TypeConversion] = {
    TypeConversion.values.find(conv => conv.from == from && conv.to == to)
  }

}
