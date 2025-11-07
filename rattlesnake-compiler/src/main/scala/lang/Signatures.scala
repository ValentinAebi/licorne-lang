package lang

import identifiers.*
import lang.Field.StableField
import lang.Values.IdValue
import lang.Types.{Type, BasicType}

import scala.collection.mutable

final case class FunctionSignature(
                                    ownerName: TypeIdentifier,
                                    functionName: FunOrVarId,
                                    typeParams: List[TypeIdentifier],
                                    paramsInclThis: mutable.LinkedHashMap[IdValue, Type],
                                    retType: Type,
                                    visibility: Visibility
                                  ) {
  override def toString: String = {
    val sb = StringBuilder()
    sb.append(visibility).append(" ").append(ownerName).append(".").append(functionName)
    printListIfNonEmpty(typeParams, "<", ">", sb)
    printListIfNonEmpty(paramsInclThis, "(", ")", sb, (param, tpe) => s"$param: $tpe")
    sb.append(" -> ").append(retType)
    sb.toString()
  }
}

private def printListIfNonEmpty[T](ls: Iterable[T], opening: String, closing: String, sb: StringBuilder, paramsToStr: T => String = (t: T) => t.toString): Unit = {
  if (ls.nonEmpty){
    sb.append(opening)
    val iter = ls.iterator
    while (iter.hasNext) {
      sb.append(paramsToStr(iter.next()))
      if (iter.hasNext) {
        sb.append(",")
      }
    }
    sb.append(closing)
  }
}

sealed trait TypeSignature {
  def id: TypeIdentifier
}

final case class TypeAliasSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[(TypeIdentifier, Variance)],
                                     thisValue: IdValue,
                                     params: mutable.LinkedHashMap[FunOrVarId, (Type, IdValue)]
                                   ) extends TypeSignature

sealed trait RuntimeTypeSignature extends TypeSignature

sealed trait ConcreteTypeSignature extends RuntimeTypeSignature

sealed trait Encapsulated {
  this: RuntimeTypeSignature =>

  def functions: Map[FunOrVarId, FunctionSignature]

  def directSupertypes: List[BasicType]
}

sealed trait Unencapsulated {
  this: RuntimeTypeSignature =>

  def directSupertypes: List[TypeIdentifier]
}

sealed trait TypeParametric extends RuntimeTypeSignature {
  this: TypeSignature =>

  def typeParams: List[(TypeIdentifier, Variance)]
}

final case class InterfaceSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[(TypeIdentifier, Variance)],
                                     functions: Map[FunOrVarId, FunctionSignature],
                                     directSupertypes: List[BasicType]
                                   )
  extends RuntimeTypeSignature, TypeParametric, Encapsulated

final case class ClassSignature(
                                 id: TypeIdentifier,
                                 typeParams: List[(TypeIdentifier, Variance)],
                                 fields: mutable.LinkedHashMap[FunOrVarId, Field],
                                 importedObjects: mutable.LinkedHashSet[IdValue],
                                 functions: Map[FunOrVarId, FunctionSignature],
                                 directSupertypes: List[BasicType]
                               )
  extends RuntimeTypeSignature, ConcreteTypeSignature, TypeParametric, Encapsulated

final case class ClassFieldInfo(tpe: Type, isReassignable: Boolean)

final case class ObjectSignature(
                                  id: TypeIdentifier,
                                  importedObjects: mutable.LinkedHashSet[IdValue],
                                  functions: Map[FunOrVarId, FunctionSignature],
                                  directSupertypes: List[BasicType]
                                )
  extends RuntimeTypeSignature, ConcreteTypeSignature, Encapsulated

final case class DatatypeSignature(
                                    id: TypeIdentifier,
                                    typeParams: List[(TypeIdentifier, Variance)],
                                    directSupertypes: List[TypeIdentifier],
                                    directSubtypes: mutable.LinkedHashSet[TypeIdentifier]
                                  )
  extends RuntimeTypeSignature, Unencapsulated, TypeParametric

final case class StructSignature(
                                  id: TypeIdentifier,
                                  typeParams: List[(TypeIdentifier, Variance)],
                                  fields: mutable.LinkedHashMap[FunOrVarId, StableField],
                                  directSupertypes: List[TypeIdentifier]
                                )
  extends RuntimeTypeSignature, ConcreteTypeSignature, Unencapsulated, TypeParametric

enum Field {
  case ReassignableField(tpe: Type)
  case StableField(tpe: Type, value: IdValue)

  def tpe: Type
}
