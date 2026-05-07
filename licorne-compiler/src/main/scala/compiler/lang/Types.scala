package compiler.lang

import compiler.identifiers.{Identifier, ItId, TypeIdentifier}
import compiler.irs.ssa.SSA.Scope
import compiler.irs.ssa.Formulas.*
import compiler.lang.Types.PrimitiveType.{AnyType, IntType, NothingType}
import compiler.reporting.Position
import compiler.smt.Simplifier
import compiler.typing.contexts.{ResolutionContext, TypeParamsContext}
import compiler.util.SeqSet
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

import java.util.concurrent.atomic.AtomicLong
import scala.collection
import scala.util.boundary


object Types {

  sealed trait Type {
    def formulaDependencies: List[Formula]
  }

  sealed trait NominalType extends Type

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

    override def formulaDependencies: List[Formula] = List.empty

    override def toString: String = str
  }

  def primTypeFor(name: TypeIdentifier): Option[PrimitiveType] = {
    PrimitiveType.values.find(_.str == name.stringId)
  }

  final case class NamedType(typeName: TypeIdentifier, typeArgs: List[Type], args: List[Formula]) extends NominalType {

    def isSimpleName: Boolean = typeArgs.isEmpty && args.isEmpty

    override def formulaDependencies: List[Formula] = typeArgs.flatMap(_.formulaDependencies) ++ args

    override def toString: String = {
      val typeParamsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      val paramsDescr = if args.isEmpty then "" else args.mkString("(", ",", ")")
      typeName.toString + typeParamsDescr + paramsDescr
    }
  }

  final case class ClosureType(params: List[Type], result: Type, enforcedPure: Boolean) extends Type {
    override def formulaDependencies: List[Formula] = params.flatMap(_.formulaDependencies) ++ result.formulaDependencies

    override def toString: String =
      (if enforcedPure then s"${Keyword.Pure} " else "") ++ s"${Keyword.Fn} (${params.mkString(",")}) -> $result"
  }

  final case class UnionType private(types: SeqSet[Type]) extends Type {
    override def formulaDependencies: List[Formula] = types.flatMap(_.formulaDependencies).toList

    override def toString: String = types.mkString(" | ")
  }

  object UnionType {

    def apply(types: SeqSet[Type]): Type = {
      val flattenedTypes = types.flatMap {
        case UnionType(types) => types
        case tpe => List(tpe)
      }
      flattenedTypes.size match {
        case 0 => NothingType
        case 1 => flattenedTypes.head
        case 2 => new UnionType(flattenedTypes)
      }
    }

    def apply(types: Iterable[Type]): Type =
      apply(SeqSet(types))

    def apply(types: Type*): Type =
      apply(SeqSet(types))
  }

  final case class IntersectionType private(types: SeqSet[Type]) extends Type {
    override def formulaDependencies: List[Formula] = types.flatMap(_.formulaDependencies).toList

    override def toString: String = types.mkString(" & ")
  }

  object IntersectionType {

    def apply(types: SeqSet[Type]): Type = {
      val flattenedTypes = types.flatMap {
        case IntersectionType(types) => types
        case tpe => List(tpe)
      }
      flattenedTypes.size match {
        case 0 => AnyType
        case 1 => flattenedTypes.head
        case _ => new IntersectionType(flattenedTypes)
      }
    }

    def apply(types: Iterable[Type]): Type =
      apply(SeqSet(types))

    def apply(types: Type*): Type =
      apply(SeqSet(types))
  }

  final case class RefinedType(baseType: Type, itVal: IdValue, predicateScope: Scope, predicate: Formula) extends Type {
    override def formulaDependencies: List[Formula] = baseType.formulaDependencies :+ predicate

    def flattenedRefinement: RefinedType = {

      def flattenPred(refinedType: RefinedType): (Type, Formula) = {
        val RefinedType(baseType, itVal, predicateScope, predicate) = refinedType
        baseType match {
          case inner@RefinedType(innerBase, innerIt, innerScope, innerPredicate) =>
            val (base, prevPred) = flattenPred(inner)
            val mergedPred = LogicalAnd(
              prevPred.substitute(Map(innerIt -> itVal)),
              predicate
            )
            (base, mergedPred)
          case _ => (baseType, predicate)
        }
      }

      val (base, pred) = flattenPred(this)
      RefinedType(base, itVal, predicateScope, pred)
    }

    override def toString: String = s"$baseType ${Keyword.With} $predicate"
  }

  final case class IntRangeType(lowerBoundOpt: Option[Formula], upperBoundOpt: Option[Formula]) extends Type {
    override def formulaDependencies: List[Formula] = lowerBoundOpt.toList ++ upperBoundOpt

    override def toString: String = {
      def boundDescr(bound: Option[Formula]): String = bound.map(_.toString).getOrElse("")

      s"[${boundDescr(lowerBoundOpt)},${boundDescr(upperBoundOpt)}]"
    }
  }

  object IntRangeType {

    def singleton(elem: Formula): IntRangeType =
      IntRangeType(Some(elem), Some(elem))

    def singleton(elem: Int): IntRangeType =
      singleton(IntConst(elem))

    def ofLowerBound(lb: Formula): IntRangeType =
      IntRangeType(Some(lb), None)

    def ofUpperBound(ub: Formula): IntRangeType =
      IntRangeType(None, Some(ub))

    def apply(from: Formula, to: Formula): IntRangeType =
      IntRangeType(Some(from), Some(to))

    def apply(from: Int, to: Formula): IntRangeType =
      IntRangeType(IntConst(from), to)

    def apply(from: Formula, to: Int): IntRangeType =
      IntRangeType(from, IntConst(to))

    def apply(from: Int, to: Int): IntRangeType =
      IntRangeType(IntConst(from), IntConst(to))

    val strictlyPositive: IntRangeType = ofLowerBound(IntConst(1))
    val nonNegative: IntRangeType = ofLowerBound(IntConst(0))
    val nonPositive: IntRangeType = ofUpperBound(IntConst(0))
    val strictlyNegative: IntRangeType = ofUpperBound(IntConst(-1))

  }

  /**
   * @param nullatedType the type wrapped by this NullableType
   *                     (name is intentionally confusing to discourage premature assumptions on its meaning)
   */
  final case class NullableType private(nullatedType: Type) extends Type {
    override def formulaDependencies: List[Formula] = nullatedType.formulaDependencies

    override def toString: String = nullatedType match {
      case nullatedType: RefinedType => s"($nullatedType)?"
      case nullatedType => s"$nullatedType?"
    }
  }

  object NullableType {
    def apply(nullatedType: Type): NullableType = nullatedType match {
      case nullableType: NullableType => nullableType
      case nonNullType => new NullableType(nonNullType)
    }
  }

  private val typeVarUidGen = new AtomicLong(-1)

  final class TypeVariable private(val id: Identifier, val upperBoundOpt: Option[Type], val lowerBoundOpt: Option[Type], val instantiationPosOpt: Option[Position]) extends Type {
    private val uid = typeVarUidGen.incrementAndGet()
    private var actualTypeOpt = Option.empty[Type]
    private var lockedFlag = false

    private def setActualType(tpe: Type): Unit = {
      actualTypeOpt = Some(tpe match {
        case IntRangeType(Some(lb), Some(ub)) if lb == ub => IntType
        case tpe => tpe
      })
    }

    override def formulaDependencies: List[Formula] = List.empty

    def resolve(tpe: Type): Unit = {
      if (isResolved) {
        throw IllegalStateException("type variable was already resolved")
      }
      val actualTpe = goUpPath(tpe)
      if (actualTpe != this) {
        setActualType(actualTpe)
      }
    }

    def remapIfNotLocked(tpe: Type): Unit = {
      if (!isResolved) {
        throw IllegalStateException("cannot remap an unresolved type variable")
      }
      if (!lockedFlag) {
        val actualTpe = goUpPath(tpe)
        if (actualTpe != this) {
          setActualType(actualTpe)
        }
      }
    }

    def lock(): Unit = {
      lockedFlag = true
    }

    def actualTypeIfResolved: Option[Type] = actualTypeOpt.map(goUpPath)

    def isResolved: Boolean = actualTypeIfResolved.isDefined

    def substitutedIfResolved: Type = actualTypeIfResolved.getOrElse(this)

    override def toString: String =
      if isResolved then actualTypeIfResolved.get.toString else s"?$id"

    private def goUpPath(tpe: Type): Type = tpe match {
      case tVar: TypeVariable => tVar.actualTypeOpt match {
        case Some(actualType) =>
          val repr = goUpPath(actualType)
          tVar.setActualType(repr)
          repr
        case None => tpe
      }
      case _ => tpe
    }
  }

  object TypeVariable {
    def apply(id: Identifier, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type], instantiationPosOpt: Option[Position])(tvRegistrator: TypeVariable => Unit): TypeVariable = {
      val tv = new TypeVariable(id, upperBoundOpt, lowerBoundOpt, instantiationPosOpt)
      tvRegistrator(tv)
      tv
    }
  }

  extension (tpe: Type) def substitute(typesSubst: collection.Map[TypeIdentifier, Type], valsSubst: collection.Map[IdValue, Formula]): Type = tpe match {
    case primitiveType: PrimitiveType => primitiveType
    case NamedType(typeName, Nil, Nil) if typesSubst.contains(typeName) =>
      typesSubst.apply(typeName)
    case NamedType(typeName, typeArgs, args) =>
      NamedType(typeName, typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(valsSubst)))
    case tVar: TypeVariable => tVar
    case ClosureType(params, result, enforcedPure) =>
      ClosureType(params.map(_.substitute(typesSubst, valsSubst)), result.substitute(typesSubst, valsSubst), enforcedPure)
    case UnionType(types) =>
      UnionType(types.map(_.substitute(typesSubst, valsSubst)))
    case IntersectionType(types) =>
      IntersectionType(types.map(_.substitute(typesSubst, valsSubst)))
    case RefinedType(baseType, itVal, scope, predicate) =>
      RefinedType(baseType.substitute(typesSubst, valsSubst), itVal, scope, predicate.substitute(valsSubst.filter(_._1 != itVal)))
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      IntRangeType(
        lowerBoundOpt.map(_.substitute(valsSubst)),
        upperBoundOpt.map(_.substitute(valsSubst))
      )
    case NullableType(nullatedType) =>
      NullableType(nullatedType.substitute(typesSubst, valsSubst))
  }

  extension (tpe: Type) def withTypeVarsExpanded: Type = tpe match {
    case primitiveType: PrimitiveType => primitiveType
    case NamedType(typeName, typeArgs, args) => NamedType(typeName, typeArgs.map(_.withTypeVarsExpanded), args)
    case ClosureType(params, result, enforcedPure) =>
      ClosureType(params.map(_.withTypeVarsExpanded), result.withTypeVarsExpanded, enforcedPure)
    case variable: TypeVariable => variable.substitutedIfResolved
    case UnionType(types) =>
      UnionType(types.map(_.withTypeVarsExpanded))
    case IntersectionType(types) =>
      IntersectionType(types.map(_.withTypeVarsExpanded))
    case RefinedType(baseType, itVal, scope, predicate) =>
      RefinedType(baseType.withTypeVarsExpanded, itVal, scope, predicate)
    case range: IntRangeType => range
    case NullableType(nullatedType) =>
      NullableType(nullatedType.withTypeVarsExpanded)
  }

  extension (tpe: Type) def filtered(assignmentTarget: Formula, currScopeAndProxyStoreOpt: Option[(Scope, ProxyStore)])
                                    (using globalValsCtx: GlobalValuesContext, resolutionCtx: ResolutionContext, simplifier: Simplifier, typeParamsCtx: TypeParamsContext): Type = tpe match {
    case primitiveType: PrimitiveType => primitiveType
    case NamedType(typeName, typeArgs, args) =>
      val newTypeArgs = typeArgs.map(_.filtered(assignmentTarget, currScopeAndProxyStoreOpt))
      NamedType(typeName, newTypeArgs, args)
    case ClosureType(params, result, enforcedPure) =>
      ClosureType(params.map(_.filtered(assignmentTarget, currScopeAndProxyStoreOpt)), result.filtered(assignmentTarget, currScopeAndProxyStoreOpt), enforcedPure)
    case UnionType(types) =>
      UnionType(types.map(_.filtered(assignmentTarget, currScopeAndProxyStoreOpt)))
    case IntersectionType(types) =>
      IntersectionType(types.map(_.filtered(assignmentTarget, currScopeAndProxyStoreOpt)))
    case RefinedType(baseType, oldItVal, oldScope, predicate) =>

      def filterPred(predicate: Formula): List[Formula] = predicate match {
        case LogicalAnd(lhs, rhs) =>
          filterPred(lhs) ++ filterPred(rhs)
        case predicate if assignmentTarget.typeCanMention(predicate) => List(predicate)
        case _ => List.empty
      }

      filterPred(predicate) match {
        case Nil => baseType
        case conjuncts =>
          val newScopeRoot = assignmentTarget.idValsDependencies.map(_.definingScope).maxByOption(_.depth).getOrElse(globalValsCtx.globalScope)
          val newScope = Scope.nestedInsideNodeOpt(newScopeRoot, None)
          val newItVal = newScope.newParam(ItId, currScopeAndProxyStoreOpt.flatMap(_._1.getPosition))
          conjuncts.reduce(LogicalAnd(_, _))
            .substitute(Map(oldItVal -> newItVal))
            .filteredAsCondition(assignmentTarget) match {
            case Some(newPredicate) => RefinedType(baseType.filtered(assignmentTarget, currScopeAndProxyStoreOpt), oldItVal, newScope, newPredicate)
            case None => baseType
          }
      }
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      val newLb = expandBound(lowerBoundOpt, assignmentTarget, _.lowerBoundOpt, currScopeAndProxyStoreOpt)
      val newUb = expandBound(upperBoundOpt, assignmentTarget, _.upperBoundOpt, currScopeAndProxyStoreOpt)
      IntRangeType(newLb, newUb)
    case NullableType(nullatedType) =>
      NullableType(nullatedType.filtered(assignmentTarget, currScopeAndProxyStoreOpt))
    case tv: TypeVariable => tv
  }

  extension (tpe: Type) def filtered(assignmentTargetOpt: Option[Formula], currScopeAndProxyStoreOpt: Option[(Scope, ProxyStore)])
                                    (using resolutionCtx: ResolutionContext, simplifier: Simplifier, typeParamsCtx: TypeParamsContext, globalValsCtx: GlobalValuesContext): Type =
    assignmentTargetOpt match {
      case Some(assignmentTarget) =>
        tpe.filtered(assignmentTarget, currScopeAndProxyStoreOpt)
      case None => tpe
    }

  extension (formula: Formula) def filteredAsCondition(assignmentTarget: Formula): Option[Formula] = formula match {
    case LogicalAnd(lhs, rhs) =>
      (lhs.filteredAsCondition(assignmentTarget), rhs.filteredAsCondition(assignmentTarget)) match {
        case (Some(l), Some(r)) => Some(LogicalAnd(l, r))
        case (someL@Some(_), None) => someL
        case (None, someR@Some(_)) => someR
        case (None, None) => None
      }
    case formula => Option.when(assignmentTarget.typeCanMention(formula))(formula)
  }

  extension (tpe: Type) def ignoreRangesShallow: Type = tpe match {
    case IntRangeType(_, _) => IntType
    case tpe => tpe
  }

  extension (tpe: Type) def ignoreNullabilityShallow: Type = tpe match {
    case NullableType(nullatedType) => nullatedType
    case tpe => tpe
  }

  extension (tpe: Type) def asRefinedType(itVal: IdValue, scope: Scope): RefinedType = tpe match {
    case refinedType: RefinedType => refinedType
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      val predicateParts = lowerBoundOpt.map(LessOrEq(_, itVal)) ++ upperBoundOpt.map(LessOrEq(itVal, _))
      val predicate = if predicateParts.isEmpty then BoolConst(true) else predicateParts.reduce[Formula](LogicalAnd(_, _))
      RefinedType(IntType, itVal, scope, predicate)
    case tpe => RefinedType(tpe, itVal, scope, BoolConst(true))
  }
  
  extension (tpe: Type) def withTypeVarsSubstituted: Option[Type] = {
    
    def substAll(ls: Iterable[Type]): Option[List[Type]] = boundary {
      val resB = List.newBuilder[Type]
      for (t <- ls) {
        t.withTypeVarsSubstituted match {
          case Some(t) =>
            resB.addOne(t)
          case None =>
            boundary.break(None)
        }
      }
      Some(resB.result())
    }
    
    tpe match {
      case primitiveType: PrimitiveType => Some(primitiveType)
      case NamedType(typeName, typeArgs, args) =>
        for {
          typeArgs <- substAll(typeArgs)
        } yield NamedType(typeName, typeArgs, args)
      case ClosureType(params, result, enforcedPure) =>
        for {
          params <- substAll(params)
          result <- result.withTypeVarsSubstituted
        } yield ClosureType(params, result, enforcedPure)
      case UnionType(types) =>
        for {
          types <- substAll(types)
        } yield UnionType(types)
      case IntersectionType(types) =>
        for {
          types <- substAll(types)
        } yield IntersectionType(types)
      case RefinedType(baseType, itVal, predicateScope, predicate) =>
        for {
          baseType <- baseType.withTypeVarsSubstituted
        } yield RefinedType(baseType, itVal, predicateScope, predicate)
      case rangeType: IntRangeType => Some(rangeType)
      case NullableType(nullatedType) =>
        for {
          nullatedType <- nullatedType.withTypeVarsSubstituted
        } yield NullableType(nullatedType)
      case tv: TypeVariable => tv.actualTypeIfResolved
    }
  }

  private def expandBound(boundOpt: Option[Formula], assignmentTarget: Formula, expansionFunc: IntRangeType => Option[Formula], currScopeAndProxyStoreOpt: Option[(Scope, ProxyStore)])(using simplifier: Simplifier): Option[Formula] = boundOpt match {
    case None => None
    case sb@Some(bound) if bound.idValsDependencies.forall(assignmentTarget.typeCanMention) => sb
    case Some(bound) =>
      currScopeAndProxyStoreOpt match {
        case Some(currScope, proxyStore) =>
          currScope.currentTypeOf(bound, saveSmartcastsInIR = false)(using proxyStore) match {
            case range: IntRangeType =>
              expandBound(expansionFunc(range), assignmentTarget, expansionFunc, currScopeAndProxyStoreOpt)
            case _ => None
          }
        case None => None
      }
  }

}
