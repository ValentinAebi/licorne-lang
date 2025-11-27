package lang

import identifiers.*
import lang.Field.StableField
import lang.Types.{NamedType, Type}
import lang.Values.{Formula, IdValue}

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
    printListIfNonEmpty(typeParams, "[", "]", sb)
    printListIfNonEmpty(paramsInclThis, "(", ")", sb, (param, tpe) => s"$param: $tpe")
    sb.append(" -> ").append(retType)
    sb.toString()
  }
}

private def printListIfNonEmpty[T](ls: Iterable[T], opening: String, closing: String, sb: StringBuilder, paramsToStr: T => String = (t: T) => t.toString): Unit = {
  if (ls.nonEmpty) {
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

  def typeParams: List[(TypeIdentifier, Variance)]

  def params: mutable.LinkedHashMap[FunOrVarId, (Type, IdValue)]

  def toType(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Type = {
    NamedType(id,
      typeParams.map((tid, _) => NamedType(tid, List.empty, List.empty)),
      params.map(_._2._2).toList).substitute(typesSubst, valsSubst)
  }
}

final case class TypeAliasSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[(TypeIdentifier, Variance)],
                                     thisValue: IdValue,
                                     params: mutable.LinkedHashMap[FunOrVarId, (Type, IdValue)],
                                     rhs: Type
                                   ) extends TypeSignature

sealed trait RuntimeTypeSignature extends TypeSignature {
  override def params: mutable.LinkedHashMap[FunOrVarId, (Type, IdValue)] = mutable.LinkedHashMap.empty

  def directSupertypes: List[NamedType]
}

sealed trait ConcreteTypeSignature {
  this: RuntimeTypeSignature =>
}

sealed trait AbstractTypeSignature extends RuntimeTypeSignature {
  this: RuntimeTypeSignature =>
}

sealed trait EncapsulatedTypeSignature extends RuntimeTypeSignature {
  def functions: Map[FunOrVarId, FunctionSignature]
}

sealed trait UnencapsulatedTypeSignature extends RuntimeTypeSignature {
  this: RuntimeTypeSignature =>
}

sealed trait TypeParametricTypeSignature extends RuntimeTypeSignature {
  this: TypeSignature =>
}

final case class InterfaceSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[(TypeIdentifier, Variance)],
                                     functions: Map[FunOrVarId, FunctionSignature],
                                     directSupertypes: List[NamedType]
                                   )
  extends RuntimeTypeSignature, TypeParametricTypeSignature, EncapsulatedTypeSignature

final case class ClassSignature(
                                 id: TypeIdentifier,
                                 typeParams: List[(TypeIdentifier, Variance)],
                                 fields: mutable.LinkedHashMap[FunOrVarId, Field],
                                 importedObjects: mutable.LinkedHashSet[IdValue],
                                 functions: Map[FunOrVarId, FunctionSignature],
                                 directSupertypes: List[NamedType]
                               )
  extends RuntimeTypeSignature, ConcreteTypeSignature, TypeParametricTypeSignature, EncapsulatedTypeSignature

final case class ClassFieldInfo(tpe: Type, isReassignable: Boolean)

final case class ObjectSignature(
                                  id: TypeIdentifier,
                                  importedObjects: mutable.LinkedHashSet[IdValue],
                                  functions: Map[FunOrVarId, FunctionSignature],
                                  directSupertypes: List[NamedType]
                                )
  extends RuntimeTypeSignature, AbstractTypeSignature, ConcreteTypeSignature, EncapsulatedTypeSignature {
  override def typeParams: List[(TypeIdentifier, Variance)] = List.empty
}

final case class DatatypeSignature(
                                    id: TypeIdentifier,
                                    typeParams: List[(TypeIdentifier, Variance)],
                                    directSupertypes: List[NamedType],
                                    directSubtypes: mutable.LinkedHashSet[TypeIdentifier]
                                  )
  extends RuntimeTypeSignature, AbstractTypeSignature, UnencapsulatedTypeSignature, TypeParametricTypeSignature

final case class StructSignature(
                                  id: TypeIdentifier,
                                  typeParams: List[(TypeIdentifier, Variance)],
                                  fields: mutable.LinkedHashMap[FunOrVarId, StableField],
                                  directSupertypes: List[NamedType]
                                )
  extends RuntimeTypeSignature, ConcreteTypeSignature, UnencapsulatedTypeSignature, TypeParametricTypeSignature

enum Field {
  case ReassignableField(id: FunOrVarId, tpe: Type)
  case StableField(id: FunOrVarId, tpe: Type, value: IdValue)

  def id: FunOrVarId

  def tpe: Type

  def isStable: Boolean = this match {
    case _: ReassignableField => false
    case _: StableField => true
  }
}
