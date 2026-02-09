package lang

import identifiers.*
import lang.Field.StableField
import lang.Types.{NamedType, Type}
import lang.Formulas.{Formula, IdValue}
import lang.Keyword.{Sub, Super}

import scala.collection.{SeqMap, mutable}

final case class FunctionSignature(
                                    ownerName: TypeIdentifier,
                                    functionName: FunOrVarId,
                                    typeParams: List[FunctionTypeParamInfo],
                                    paramsInclThis: SeqMap[IdValue, Type],
                                    retType: Type,
                                    visibility: Visibility
                                  ) {

  val (receiverVal: IdValue, receiverType: Type) = paramsInclThis.head

  override def toString: String = {
    val sb = StringBuilder()
    sb.append(visibility).append(" ").append(ownerName).append(".").append(functionName)
    printListIfNonEmpty(typeParams, "[", "]", sb)
    printListIfNonEmpty(paramsInclThis, "(", ")", sb) { case (param, tpe) => s"$param: $tpe" }
    sb.append(" -> ").append(retType)
    sb.toString()
  }
}

private def printListIfNonEmpty[T](ls: Iterable[T], opening: String, closing: String, sb: StringBuilder): Unit =
  printListIfNonEmpty(ls, opening, closing, sb)((t: T) => t.toString)

private def printListIfNonEmpty[T](ls: Iterable[T], opening: String, closing: String, sb: StringBuilder)(paramsToStr: T => String): Unit = {
  if (ls.nonEmpty) {
    sb.append(opening)
    val iter = ls.iterator
    while (iter.hasNext) {
      sb.append(paramsToStr(iter.next()))
      if (iter.hasNext) {
        sb.append(", ")
      }
    }
    sb.append(closing)
  }
}

sealed trait TypeSignature {
  def id: TypeIdentifier

  def typeParams: List[TypeTypeParamInfo]

  def params: SeqMap[FunOrVarId, (Type, IdValue)]

  def toType(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Type = {
    NamedType(id,
      typeParams.map { case TypeTypeParamInfo(tid, _, _, _) => NamedType(tid, List.empty, List.empty) },
      params.map(_._2._2).toList).substitute(typesSubst, valsSubst)
  }

  def varianceOf(tParam: TypeIdentifier): Option[Variance] =
    typeParams.find(_._1 == tParam).map(_._2)
}

final case class TypeAliasSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[TypeTypeParamInfo],
                                     itValue: IdValue,
                                     params: SeqMap[FunOrVarId, (Type, IdValue)],
                                     rhs: Type
                                   ) extends TypeSignature

sealed trait RuntimeTypeSignature extends TypeSignature {
  override def params: SeqMap[FunOrVarId, (Type, IdValue)] = mutable.LinkedHashMap.empty

  def directSupertypes: List[NamedType]
}

sealed trait Concrete {
  this: RuntimeTypeSignature =>
}

sealed trait UserInstantiable {
  this: Concrete =>

  def fields: SeqMap[FunOrVarId, Field]
}

sealed trait Abstract extends RuntimeTypeSignature {
  this: RuntimeTypeSignature =>
}

sealed trait Encapsulated extends RuntimeTypeSignature {
  def functions: Map[FunOrVarId, FunctionSignature]
}

sealed trait Unencapsulated extends RuntimeTypeSignature {
  this: RuntimeTypeSignature =>
}

sealed trait TypeParametric extends RuntimeTypeSignature {
  this: TypeSignature =>
}

final case class InterfaceSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[TypeTypeParamInfo],
                                     functions: Map[FunOrVarId, FunctionSignature],
                                     directSupertypes: List[NamedType]
                                   )
  extends RuntimeTypeSignature, TypeParametric, Encapsulated

final case class ClassSignature(
                                 id: TypeIdentifier,
                                 typeParams: List[TypeTypeParamInfo],
                                 fields: SeqMap[FunOrVarId, Field],
                                 importedObjects: mutable.LinkedHashSet[IdValue],
                                 functions: Map[FunOrVarId, FunctionSignature],
                                 directSupertypes: List[NamedType]
                               )
  extends RuntimeTypeSignature, Concrete, TypeParametric, Encapsulated, UserInstantiable

final case class ClassFieldInfo(tpe: Type, isReassignable: Boolean)

final case class ObjectSignature(
                                  id: TypeIdentifier,
                                  importedObjects: mutable.LinkedHashSet[IdValue],
                                  functions: Map[FunOrVarId, FunctionSignature],
                                  directSupertypes: List[NamedType]
                                )
  extends RuntimeTypeSignature, Abstract, Concrete, Encapsulated {
  override def typeParams: List[TypeTypeParamInfo] = List.empty
}

final case class DatatypeSignature(
                                    id: TypeIdentifier,
                                    typeParams: List[TypeTypeParamInfo],
                                    directSupertypes: List[NamedType],
                                    directSubtypes: mutable.LinkedHashSet[TypeIdentifier]
                                  )
  extends RuntimeTypeSignature, Abstract, Unencapsulated, TypeParametric

final case class RecordSignature(
                                  id: TypeIdentifier,
                                  typeParams: List[TypeTypeParamInfo],
                                  fields: SeqMap[FunOrVarId, StableField],
                                  directSupertypes: List[NamedType]
                                )
  extends RuntimeTypeSignature, Concrete, Unencapsulated, TypeParametric, UserInstantiable

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

sealed trait TypeParamInfo {
  val tid: TypeIdentifier
  val upperBoundOpt: Option[Type]
  val lowerBoundOpt: Option[Type]
}

final case class TypeTypeParamInfo(tid: TypeIdentifier, variance: Variance, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type]) extends TypeParamInfo {
  override def toString: String =
    s"${varianceDescr(variance)}$tid${boundDescr(Sub, upperBoundOpt)}${boundDescr(Super, lowerBoundOpt)}"
}

final case class FunctionTypeParamInfo(tid: TypeIdentifier, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type]) extends TypeParamInfo {
  override def toString: String =
    s"$tid${boundDescr(Sub, upperBoundOpt)}${boundDescr(Super, lowerBoundOpt)}"
}

private def varianceDescr(variance: Variance): String = variance match {
  case Variance.Invariant => ""
  case Variance.Covariant => Operator.Plus.toString
  case Variance.Contravariant => Operator.Minus.toString
}

private def boundDescr(subOrSuper: Keyword, boundOpt: Option[Type]): String = boundOpt match {
  case Some(bound) => s" $subOrSuper $bound"
  case None => ""
}
