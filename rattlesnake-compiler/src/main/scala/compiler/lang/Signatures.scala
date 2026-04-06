package compiler.lang

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.SSA.Scope
import compiler.lang.Field.StableField
import compiler.lang.Formulas.{Formula, IdValue, NamedIdValue, ParamIdValue}
import compiler.lang.Keyword.{Sub, Super}
import compiler.lang.Types.{NamedType, Type}
import compiler.reporting.Position
import compiler.util.{SeqSet, mapVals}

import scala.collection.mutable
import scala.collection.immutable.SeqMap

final case class FunctionSignature(
                                    ownerName: TypeIdentifier,
                                    functionName: FunOrVarId,
                                    typeParams: List[FunctionTypeParamInfo],
                                    paramsInclThis: SeqMap[NamedIdValue, Type],
                                    retType: Type,
                                    sigScope: Scope,
                                    visibility: Visibility,
                                    declPosOpt: Option[Position]
                                  ) {

  val (receiverVal: IdValue, receiverType: Type) = paramsInclThis.head
  
  def paramsWithoutThis: Iterable[(NamedIdValue, Type)] = paramsInclThis.tail
  
  def substitute(newOwnerName: TypeIdentifier, typesSubst: Map[TypeIdentifier, Type]): FunctionSignature = FunctionSignature(
    newOwnerName,
    functionName,
    typeParams,
    paramsInclThis.mapVals(_.substitute(typesSubst, Map.empty)),
    retType.substitute(typesSubst, Map.empty),
    sigScope,
    visibility,
    declPosOpt
  )

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

  def sigScope: Scope

  def declPosOpt: Option[Position]

  def toType(typesSubst: Map[TypeIdentifier, Type]): NamedType = {
    NamedType(id,
      typeParams.map(tp => typesSubst.getOrElse(tp.tid, NamedType(tp.tid, List.empty, List.empty))),
      params.map(_._2._2).toList
    )
  }

  def varianceOf(tParam: TypeIdentifier): Option[Variance] =
    typeParams.find(_._1 == tParam).map(_._2)
}

final case class TypeAliasSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[TypeTypeParamInfo],
                                     itValue: IdValue,
                                     params: SeqMap[FunOrVarId, (Type, IdValue)],
                                     rhs: Type,
                                     sigScope: Scope,
                                     declPosOpt: Option[Position]
                                   ) extends TypeSignature

sealed trait RuntimeTypeSignature extends TypeSignature {
  override def params: SeqMap[FunOrVarId, (Type, IdValue)] = SeqMap.empty

  def directSupertypes: List[NamedType]
}

sealed trait ConcreteTypeSig extends RuntimeTypeSignature

sealed trait UserInstantiableTypeSig extends ConcreteTypeSig {
  def fields: SeqMap[FunOrVarId, Field]
}

sealed trait AbstractTypeSig extends RuntimeTypeSignature

sealed trait EncapsulatedTypeSig extends RuntimeTypeSignature {
  def functions: Map[FunOrVarId, FunctionSignature]
}

sealed trait UnencapsulatedTypeSig extends RuntimeTypeSignature {
  this: RuntimeTypeSignature =>
  def directSupertypes: List[NamedType]
}

sealed trait TypeParametricTypeSig extends RuntimeTypeSignature {
  this: TypeSignature =>

  def typeParams: List[TypeTypeParamInfo]
}

final case class InterfaceSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[TypeTypeParamInfo],
                                     functions: Map[FunOrVarId, FunctionSignature],
                                     directSupertypes: List[NamedType],
                                     sigScope: Scope,
                                     declPosOpt: Option[Position]
                                   )
  extends RuntimeTypeSignature, AbstractTypeSig, TypeParametricTypeSig, EncapsulatedTypeSig

final case class ClassSignature(
                                 id: TypeIdentifier,
                                 typeParams: List[TypeTypeParamInfo],
                                 fields: SeqMap[FunOrVarId, Field],
                                 functions: Map[FunOrVarId, FunctionSignature],
                                 directSupertypes: List[NamedType],
                                 sigScope: Scope,
                                 declPosOpt: Option[Position]
                               )
  extends RuntimeTypeSignature, ConcreteTypeSig, TypeParametricTypeSig, EncapsulatedTypeSig, UserInstantiableTypeSig

final case class ClassFieldInfo(tpe: Type, isReassignable: Boolean)

final case class ObjectSignature(
                                  id: TypeIdentifier,
                                  functions: Map[FunOrVarId, FunctionSignature],
                                  directSupertypes: List[NamedType],
                                  sigScope: Scope,
                                  declPosOpt: Option[Position]
                                )
  extends RuntimeTypeSignature, AbstractTypeSig, ConcreteTypeSig, EncapsulatedTypeSig {
  override def typeParams: List[TypeTypeParamInfo] = List.empty
}

final case class DatatypeSignature(
                                    id: TypeIdentifier,
                                    typeParams: List[TypeTypeParamInfo],
                                    directSupertypes: List[NamedType],
                                    directSubtypes: SeqSet[TypeIdentifier],
                                    sigScope: Scope,
                                    declPosOpt: Option[Position]
                                  )
  extends RuntimeTypeSignature, AbstractTypeSig, UnencapsulatedTypeSig, TypeParametricTypeSig

final case class RecordSignature(
                                  id: TypeIdentifier,
                                  typeParams: List[TypeTypeParamInfo],
                                  fields: SeqMap[FunOrVarId, StableField],
                                  directSupertypes: List[NamedType],
                                  sigScope: Scope,
                                  declPosOpt: Option[Position]
                                )
  extends RuntimeTypeSignature, ConcreteTypeSig, UnencapsulatedTypeSig, TypeParametricTypeSig, UserInstantiableTypeSig

enum Field {
  case ReassignableField(id: FunOrVarId, tpe: Type)
  case StableField(id: FunOrVarId, tpe: Type, value: IdValue)

  def id: FunOrVarId

  def tpe: Type

  def isStable: Boolean = this match {
    case _: ReassignableField => false
    case _: StableField => true
  }

  override def toString: String = this match {
    case Field.ReassignableField(id, tpe) => s"${Keyword.Var} $id: $tpe"
    case Field.StableField(id, tpe, value) => s"$value: $tpe"
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
