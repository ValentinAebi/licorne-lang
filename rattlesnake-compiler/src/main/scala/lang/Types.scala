package lang

import identifiers.TypeIdentifier
import lang.Types.PrimitiveType.{IntType, NothingType}
import lang.Values.*
import symbolic.FormulaSimplifier

import java.util.Objects
import java.util.concurrent.atomic.AtomicLong


object Types {

  private val itForHashAndEquals = new IdValue {
    override def completeDescr: String = "it$hash"

    override def sourceLevelDescrOrDefault: String = "it"
  }

  sealed trait Type {
    def baseType: BaseType
  }

  final case class RefinedType private(baseType: NominalType, itValue: IdValue, predicate: Formula) extends Type {

    override def equals(other: Any): Boolean = other match {
      case RefinedType(otherBaseType, otherItValue, otherPredicate) =>
        baseType == otherBaseType && (
          (itValue == otherItValue && predicate == otherPredicate) ||
            predicate == otherPredicate.substitute(Map.empty, Map(otherItValue -> itValue)))
      case _ => false
    }

    override def hashCode(): Int = Objects.hash(baseType, predicate.substitute(Map.empty, Map(itValue -> itForHashAndEquals)))

    def maybeAsRange: (Option[IntRange], Option[Formula]) = {
      if (baseType == IntType) {
        val minsB = Set.newBuilder[Formula]
        val maxsB = Set.newBuilder[Formula]
        val othersB = List.newBuilder[Formula]

        def traverse(formula: Formula): Unit = formula match {
          case And(lhs, rhs) =>
            traverse(lhs)
            traverse(rhs)
          case LessOrEq(low, `itValue`) =>
            minsB.addOne(low)
          case LessOrEq(`itValue`, up) =>
            maxsB.addOne(up)
          case LessThan(lb, `itValue`) =>
            minsB.addOne(Plus(lb, IntConstant(1)))
          case LessThan(`itValue`, up) =>
            maxsB.addOne(Minus(up, IntConstant(1)))
          case other =>
            othersB.addOne(other)
        }

        traverse(predicate)
        val mins = minsB.result()
        val maxs = maxsB.result()
        val others = othersB.result()
        val rangeOpt =
          if mins.nonEmpty || maxs.nonEmpty then Some(IntRange(mins, maxs))
          else None
        val restOpt =
          if others.nonEmpty then Some(others.reduceLeft(And(_, _)))
          else None
        (rangeOpt, restOpt)
      } else {
        (None, Some(predicate))
      }
    }

    override def toString: String = {

      given (IdValue => Option[Type]) = _ => None
      
      maybeAsRange match {
        case (Some(range), Some(pred)) =>
          val formulaSimplifier = new FormulaSimplifier
          s"$range with ${formulaSimplifier.formulaToStringSimplified(pred)}"
        case (Some(range), None) =>
          range.toString
        case (None, Some(pred)) =>
          val formulaSimplifier = new FormulaSimplifier
          s"$baseType with ${formulaSimplifier.formulaToStringSimplified(pred)}"
        case (None, None) =>
          baseType.toString
      }
    }
  }

  object RefinedType {
    def apply(baseType: NominalType, itValue: IdValue, predicate: Formula): Type =
      baseType match {
        case NothingType => NothingType
        case _ => new RefinedType(baseType, itValue, predicate)
      }
  }

  final case class IntRange(lowerBounds: Set[Formula], upperBounds: Set[Formula]) {
    override def toString: String = {
      
      val formulaSimplifier = FormulaSimplifier()

      def boundsRepr(bounds: List[Formula], minOrMax: String): String = bounds match {
        case Nil => ""
        case List(bound) =>
          formulaSimplifier.formulaToStringSimplified(bound)
        case bounds => minOrMax ++ bounds.map(formulaSimplifier.formulaToStringSimplified).mkString("(", ",", ")")
      }

      s"[${boundsRepr(lowerBounds.toList, "max")},${boundsRepr(upperBounds.toList, "min")}]"
    }
  }

  final case class UnionType(types: Set[Type]) extends Type {
    override def baseType: BaseType = BaseUnionType(types.map(_.baseType))

    override def toString: String = types.mkString(" | ")
  }

  final case class BaseUnionType(types: Set[BaseType]) extends BaseType {
    override def toString: String = types.mkString(" | ")
  }

  sealed trait BaseType extends Type {
    override def baseType: BaseType = this
  }

  sealed trait NominalType extends BaseType

  enum PrimitiveType(val str: String) extends NominalType {
    case IntType extends PrimitiveType("Int")
    case DoubleType extends PrimitiveType("Double")
    case CharType extends PrimitiveType("Char")
    case BoolType extends PrimitiveType("Bool")
    case StringType extends PrimitiveType("String")

    case NullType extends PrimitiveType("Null")
    case AnyType extends PrimitiveType("Any")
    case UnitType extends PrimitiveType("Unit")
    case NothingType extends PrimitiveType("Nothing")

    override def toString: String = str
  }

  def primTypeFor(name: TypeIdentifier): Option[PrimitiveType] = {
    PrimitiveType.values.find(_.str == name.stringId)
  }

  final case class NamedType(typeName: TypeIdentifier, typeArgs: List[Type], args: List[Formula]) extends NominalType {

    def isSimpleName: Boolean = typeArgs.isEmpty && args.isEmpty

    override def toString: String = {
      val typeParamsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      val paramsDescr = if args.isEmpty then "" else args.mkString("(", ",", ")")
      typeName.toString + typeParamsDescr + paramsDescr
    }
  }

  final case class ClosureType(params: List[Type], result: Type) extends BaseType {
    override def toString: String = s"(${params.mkString(", ")}) -> $result"
  }

  private val typeVarUidGen = new AtomicLong()

  final class TypeVariable private(name: String, val upperBoundOpt: Option[Type], val lowerBoundOpt: Option[Type]) extends BaseType {
    private val uid = typeVarUidGen.incrementAndGet()
    private var actualTypeOpt = Option.empty[Type]

    def resolve(tpe: Type): Unit = {
      if (isResolved) {
        throw IllegalStateException("type variable was already resolved")
      }
      val actualTpe = goUpPath(tpe)
      if (actualTpe != this) {
        actualTypeOpt = Some(actualTpe)
      }
    }

    def actualTypeIfResolved: Option[Type] = actualTypeOpt.map(goUpPath)

    def isResolved: Boolean = actualTypeIfResolved.isDefined

    def substitutedIfResolved: Type = actualTypeIfResolved.getOrElse(this)

    override def toString: String = name

    private def goUpPath(tpe: Type): Type = tpe match {
      case tVar: TypeVariable => tVar.actualTypeOpt match {
        case Some(actualType) =>
          val repr = goUpPath(actualType)
          tVar.actualTypeOpt = Some(repr)
          repr
        case None => tpe
      }
      case _ => tpe
    }
  }

  object TypeVariable {
    def apply(name: String, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type])(tvRegistrator: TypeVariable => Unit): TypeVariable = {
      val tv = new TypeVariable(name, upperBoundOpt, lowerBoundOpt)
      tvRegistrator(tv)
      tv
    }
  }

  extension (tpe: Type) {

    def substitute(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Type = tpe match {
      case RefinedType(baseTypeRaw, itValueRaw, predicateRaw) =>
        baseTypeRaw.substitute(typesSubst, valsSubst) match {
          case RefinedType(baseTypeSubst, itValueSubst, predicateSubst) =>
            RefinedType(baseTypeSubst, itValueRaw, And(
              predicateRaw.substitute(typesSubst, valsSubst),
              predicateSubst.substitute(typesSubst, valsSubst ++ Map(itValueSubst -> itValueRaw))
            ))
          case baseTypeSubst: NominalType =>
            RefinedType(baseTypeSubst, itValueRaw, predicateRaw.substitute(typesSubst, valsSubst))
          case closureType: ClosureType => closureType
          case _: (UnionType | BaseUnionType | TypeVariable) => throw new AssertionError(s"unexpected ${tpe.getClass.getSimpleName}")
        }
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, Nil, Nil) if typesSubst.contains(typeName) =>
        typesSubst.apply(typeName)
      case NamedType(typeName, typeArgs, args) =>
        NamedType(typeName, typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(typesSubst, valsSubst)))
      case tVar: TypeVariable => tVar
      case UnionType(types) => UnionType(types.map(_.substitute(typesSubst, valsSubst)))
      case BaseUnionType(originalBaseTypes) =>
        val substTypes = originalBaseTypes.map(_.substitute(typesSubst, valsSubst))
        if substTypes.forall(_.isInstanceOf[BaseType])
        then BaseUnionType(substTypes.map(_.asInstanceOf[BaseType]))
        else UnionType(substTypes)
      case ClosureType(params, result) =>
        ClosureType(params.map(_.substitute(typesSubst, valsSubst)), result.substitute(typesSubst, valsSubst))
    }

    def withTypeVarsExpanded: Type = tpe match {
      case RefinedType(baseType, itValue, predicate) =>
        baseType.withTypeVarsExpanded.baseType match {
          case nominalType: NominalType => RefinedType(nominalType, itValue, predicate)
          case otherType => otherType
        }
      case UnionType(types) => UnionType(types.map(_.withTypeVarsExpanded))
      case BaseUnionType(types) =>
        BaseUnionType(types.map(_.withTypeVarsExpanded.baseType))
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, typeArgs, args) => NamedType(typeName, typeArgs.map(_.withTypeVarsExpanded), args)
      case ClosureType(params, result) => ClosureType(params.map(_.withTypeVarsExpanded), result.withTypeVarsExpanded)
      case variable: TypeVariable => variable.substitutedIfResolved
    }

  }

  def join(types: Type*): Type = join(types.toSet)

  def join(typesRaw: Set[Type]): Type = {
    val nonNothingTypes = typesRaw.filterNot(_.baseType == NothingType)
    nonNothingTypes.size match {
      case 0 => NothingType
      case 1 => nonNothingTypes.head
      case _ => UnionType(nonNothingTypes)
    }
  }

}
