package compiler.lang

import compiler.identifiers.{FunOrVarId, Identifier, TypeIdentifier}
import compiler.irs.ssa.SSA.Scope
import compiler.lang.Field.StableField
import compiler.irs.ssa.Formulas.{Formula, IdValue, NamedIdValue, ParamIdValue}
import compiler.lang.Keyword.{Sub, Super}
import compiler.lang.Purity
import compiler.lang.Types.{NamedType, Type, TypeVariable}
import compiler.reporting.Position
import compiler.util.{SeqSet, mapVals}

import scala.collection.immutable.SeqMap

trait DeclSignature {
  def sigName: Identifier

  def typeParams: List[TypeParamInfo]

  def typeVarsWithDescr: SeqSet[(TypeVariable, String)]

  def declPosOpt: Option[Position]
}

final case class FunctionSignature(
                                    ownerName: TypeIdentifier,
                                    functionName: FunOrVarId,
                                    typeParams: List[FunctionTypeParamInfo],
                                    paramsInclThis: SeqMap[NamedIdValue, Type],
                                    precondOpt: Option[Formula],
                                    retType: Type,
                                    sigScope: Scope,
                                    visibility: Visibility,
                                    purity: Purity,
                                    isMain: Boolean,
                                    declPosOpt: Option[Position],
                                    isSynthetic: Boolean = false
                                  ) extends DeclSignature, ExecutionEnvironment {

  override def sigName: Identifier = functionName

  val (receiverVal: IdValue, receiverType: Type) = paramsInclThis.head

  def ownerAndName: (TypeIdentifier, FunOrVarId) = (ownerName, functionName)

  def paramsWithoutThis: Iterable[(NamedIdValue, Type)] = paramsInclThis.tail

  def isPure: Boolean = purity == Purity.Pure

  def requiresArgsList: Boolean = !isPure || typeParams.nonEmpty || paramsWithoutThis.nonEmpty

  def smtFunctionCode: String =
    functionName.toString ++ "$" ++ paramsWithoutThis.map((param, tpe) => s"${param}_$tpe").mkString("$")

  override def expectedResultType: Type = retType

  override def requiresPurityInBody: Boolean = isPure

  override def root: FunctionSignature = this

  override def typeVarsWithDescr: SeqSet[(TypeVariable, String)] = SeqSet(
    typeParams.flatMap { tp =>
      tp.upperBoundOpt.toList.flatMap(_.allTypeVariables).map(_ -> s"upper bound of type variable ${tp.tid}")
        ++ tp.lowerBoundOpt.toList.flatMap(_.allTypeVariables).map(_ -> s"lower bound of type variable ${tp.tid}")
    } ++ paramsInclThis.flatMap { (idVal, tpe) =>
      tpe.allTypeVariables.map(_ -> s"type of parameter ${idVal.name}")
    } ++ retType.allTypeVariables.map(_ -> s"return type of method $functionName")
  )

  def substitute(newOwnerName: TypeIdentifier, typesSubst: Map[TypeIdentifier, Type]): FunctionSignature = FunctionSignature(
    newOwnerName,
    functionName,
    typeParams,
    paramsInclThis.mapVals(_.substitute(typesSubst, Map.empty)),
    precondOpt,
    retType.substitute(typesSubst, Map.empty),
    sigScope,
    visibility,
    purity,
    isMain,
    declPosOpt
  )

  override def toString: String = {
    val sb = StringBuilder()
    if (isPure) {
      sb.append(Purity.Pure).append(" ")
    }
    if (isMain) {
      sb.append(Keyword.Main).append(" ")
    }
    sb.append(visibility).append(" ").append(ownerName).append(".").append(functionName)
    printListIfNonEmpty(typeParams, "[", "]", sb)
    printListIfNonEmpty(paramsInclThis, "(", "", sb) { case (param, tpe) => s"$param: $tpe" }
    precondOpt.foreach { precond =>
      sb.append(s"${Keyword.Where} ").append(precond)
    }
    sb.append(")")
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

sealed trait TypeSignature extends DeclSignature {
  def id: TypeIdentifier

  def typeParams: List[TypeTypeParamInfo]

  def params: SeqMap[FunOrVarId, (Type, IdValue)]

  def directSupertypes: List[NamedType]

  def sigScope: Scope

  override def sigName: Identifier = id

  override def typeVarsWithDescr: SeqSet[(TypeVariable, String)] = SeqSet(
    typeParams.flatMap { tp =>
      tp.upperBoundOpt.toList.flatMap(_.allTypeVariables).map(_ -> s"upper bound of type variable ${tp.tid}")
        ++ tp.lowerBoundOpt.toList.flatMap(_.allTypeVariables).map(_ -> s"lower bound of type variable ${tp.tid}")
    } ++ params.flatMap { case (paramId, (tpe, _)) =>
      tpe.allTypeVariables.map(_ -> s"type of parameter $paramId")
    } ++ directSupertypes.flatMap(st => st.allTypeVariables.map(_ -> s"supertype $st of $id"))
  )

  def toType(typesSubst: scala.collection.Map[TypeIdentifier, Type], paramsSubst: scala.collection.Map[IdValue, Formula] = Map.empty): NamedType = {
    NamedType(id,
      typeParams.map(tp => typesSubst.getOrElse(tp.tid, NamedType(tp.tid, List.empty, List.empty))),
      params.map {
        case (paramId, (paramType, paramVal)) => paramsSubst.getOrElse(paramVal, paramVal)
      }.toList
    )
  }

  def varianceOf(tParam: TypeIdentifier): Option[Variance] =
    typeParams.find(_._1 == tParam).map(_._2)
}

final case class TypeAliasSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[TypeTypeParamInfo],
                                     params: SeqMap[FunOrVarId, (Type, IdValue)],
                                     rhs: Type,
                                     sigScope: Scope,
                                     declPosOpt: Option[Position]
                                   ) extends TypeSignature {
  override def directSupertypes: List[NamedType] = List.empty
}

sealed trait RuntimeTypeSignature extends TypeSignature {
  override def params: SeqMap[FunOrVarId, (Type, IdValue)] = SeqMap.empty

  def fields: SeqMap[FunOrVarId, Field]

  def stableFields: SeqMap[FunOrVarId, StableField] = {
    val stableFieldsB = SeqMap.newBuilder[FunOrVarId, StableField]
    fields.foreach {
      case (id, fld: StableField) =>
        stableFieldsB.addOne(id, fld)
      case _ => ()
    }
    stableFieldsB.result()
  }

  def functions: Map[FunOrVarId, FunctionSignature]

  def directSupertypes: List[NamedType]
}

sealed trait ConcreteTypeSig extends RuntimeTypeSignature

sealed trait UserInstantiableTypeSig extends ConcreteTypeSig

sealed trait AbstractTypeSig extends RuntimeTypeSignature {
  override def fields: SeqMap[FunOrVarId, Field] = SeqMap.empty
}

sealed trait EncapsulatedTypeSig extends RuntimeTypeSignature

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
                                    functions: Map[FunOrVarId, FunctionSignature],
                                    directSupertypes: List[NamedType],
                                    directSubtypes: SeqSet[TypeIdentifier],
                                    sigScope: Scope,
                                    declPosOpt: Option[Position]
                                  )
  extends RuntimeTypeSignature, AbstractTypeSig, UnencapsulatedTypeSig, TypeParametricTypeSig {
  override def fields: SeqMap[FunOrVarId, Field] = SeqMap.empty
}

final case class RecordSignature(
                                  id: TypeIdentifier,
                                  typeParams: List[TypeTypeParamInfo],
                                  fields: SeqMap[FunOrVarId, StableField],
                                  functions: Map[FunOrVarId, FunctionSignature],
                                  directSupertypes: List[NamedType],
                                  sigScope: Scope,
                                  declPosOpt: Option[Position]
                                )
  extends RuntimeTypeSignature, ConcreteTypeSig, UnencapsulatedTypeSig, TypeParametricTypeSig, UserInstantiableTypeSig

enum Field {
  case ReassignableField(id: FunOrVarId, tpe: Type)
  case StableField(id: FunOrVarId, tpe: Type, value: ParamIdValue, isPublishedAsMethod: Boolean)

  def id: FunOrVarId

  def tpe: Type

  def isStable: Boolean = this match {
    case _: ReassignableField => false
    case _: StableField => true
  }

  def hasPublicSyntheticAccessor: Boolean = this match {
    case Field.ReassignableField(id, tpe) => false
    case Field.StableField(id, tpe, value, isPublishedAsMethod) => isPublishedAsMethod
  }

  override def toString: String = this match {
    case Field.ReassignableField(id, tpe) => s"${Keyword.Var} $id: $tpe"
    case Field.StableField(id, tpe, value, isPublished) =>
      val maybePublic = if isPublished then s"${Visibility.Public} " else ""
      s"$maybePublic$value: $tpe"
  }
}

sealed trait TypeParamInfo {
  val tid: TypeIdentifier
  val upperBoundOpt: Option[Type]
  val lowerBoundOpt: Option[Type]

  def varianceOpt: Option[Variance]
}

final case class TypeTypeParamInfo(tid: TypeIdentifier, variance: Variance, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type]) extends TypeParamInfo {
  override def varianceOpt: Option[Variance] = Some(variance)

  override def toString: String =
    s"${varianceDescr(variance)}$tid${boundDescr(Sub, upperBoundOpt)}${boundDescr(Super, lowerBoundOpt)}"
}

final case class FunctionTypeParamInfo(tid: TypeIdentifier, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type]) extends TypeParamInfo {
  override def varianceOpt: Option[Variance] = None

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
