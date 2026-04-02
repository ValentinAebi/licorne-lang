package compiler.lang

import Types.PrimitiveType.*
import Types.{PrimitiveType, PrincipalType, Type}

enum TypeConversion(val from: PrimitiveType, val to: PrimitiveType) {
  
  case Int2Double extends TypeConversion(IntType, DoubleType)
  case Double2Int extends TypeConversion(DoubleType, IntType)
  case IntToChar extends TypeConversion(IntType, CharType)
  case CharToInt extends TypeConversion(CharType, IntType)
  
  case IntToString extends TypeConversion(IntType, StringType)
  case BoolToString extends TypeConversion(BoolType, StringType)
  case CharToString extends TypeConversion(CharType, StringType)
  case DoubleToString extends TypeConversion(DoubleType, StringType)
}

object TypeConversion {
  
  def conversionFor(from: PrincipalType, to: PrincipalType): Option[TypeConversion] = {
    TypeConversion.values.find(conv => conv.from == from && conv.to == to)
  }
  
}
