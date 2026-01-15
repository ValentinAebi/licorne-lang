package compiler.irs

import compiler.reporting.Position
import identifiers.*
import lang.*
import lang.Types.*
import lang.Types.PrimitiveType.*


object Asts {

  sealed abstract class Ast {
    // Positions are propagated by the TreeParser
    // Each AST is assigned the position of its leftmost token (by the map method of TreeParser)
    private val position = new OptionalAttribute[Position]
    private val desugaringSource = new OptionalAttribute[Ast]

    def withDesugaringSource(desugaringSource: Ast): this.type = {
      setDesugaringSource(desugaringSource)
      position.setOpt(desugaringSource.getPosition)
      this
    }

    def originalAst: Ast = desugaringSource.getOpt match {
      case Some(source) => source.originalAst
      case None => this
    }

    def setPosition(pos: Position): this.type = {
      position.set(pos)
      this
    }

    def setPosition(posOpt: Option[Position]): this.type = {
      position.setOpt(posOpt)
      this
    }

    export position.getOpt as getPosition

    export desugaringSource.set as setDesugaringSource
    export desugaringSource.getOpt as getDesugaringSource

    // FIXME check all implementations of children
    def children: List[Ast]

    final def preorderWalk(f: PartialFunction[Ast, Unit]): Unit =
      preorderWalkImpl(f.lift)

    private def preorderWalkImpl(f: Ast => Option[Unit]): Unit = {
      f.apply(this)
      children.foreach(_.preorderWalkImpl(f))
    }
  }

  sealed abstract class Statement extends Ast

  sealed abstract class Expr extends Statement

  /**
   * Code source (most of the time a file)
   */
  final case class Source(defs: List[TopLevelDef]) extends Ast {
    private var name: String = "<missing name>"

    override def children: List[Ast] = defs

    def setName(name: String): Source = {
      this.name = name
      this
    }

    def getName: String = name
  }

  /**
   * Block (scope):
   * {{{
   *   {
   *    ...
   *   }
   * }}}
   */
  final case class Block(stats: List[Statement]) extends Statement {
    override def children: List[Ast] = stats
  }

  sealed abstract class TopLevelDef extends Ast {
    def id: TypeIdentifier
    def typeParams: List[TypeParam]
  }

  sealed trait TypeDefTree extends TopLevelDef {
    def description: String

    def directSupertypes: List[NamedTypeTree]
  }

  sealed trait EncapsulatedTypeDefTree extends TypeDefTree {
    def functions: List[FunDef]
  }

  sealed trait UnencapsulatedTypeDefTree extends TypeDefTree

  final case class InterfaceDef(
                                 id: TypeIdentifier,
                                 typeParams: List[TypeParam],
                                 functions: List[FunDef],
                                 directSupertypes: List[NamedTypeTree]
                               ) extends EncapsulatedTypeDefTree {
    override def description: String = s"interface $id"

    override def children: List[Ast] = typeParams ++ functions
  }

  final case class ObjectDef(
                              id: TypeIdentifier,
                              importedObjects: List[TypeIdentifier],
                              functions: List[FunDef],
                              directSupertypes: List[NamedTypeTree]
                            ) extends EncapsulatedTypeDefTree {
    override def description: String = s"object $id"

    override def typeParams: List[TypeParam] = Nil

    override def children: List[Ast] = functions
  }

  final case class ClassDef(
                             id: TypeIdentifier,
                             typeParams: List[TypeParam],
                             params: List[ClassParam],
                             functions: List[FunDef],
                             directSupertypes: List[NamedTypeTree]
                           ) extends EncapsulatedTypeDefTree {
    override def description: String = s"class $id"

    override def children: List[Ast] = typeParams ++ params ++ functions
  }

  final case class DataTypeDef(
                                id: TypeIdentifier,
                                typeParams: List[TypeParam],
                                directSupertypes: List[NamedTypeTree]
                              ) extends UnencapsulatedTypeDefTree {
    override def description: String = s"datatype $id"

    override def children: List[Ast] = typeParams
  }

  final case class RecordDef(
                              id: TypeIdentifier,
                              typeParams: List[TypeParam],
                              fields: List[RecordParam],
                              directSupertypes: List[NamedTypeTree]
                            ) extends UnencapsulatedTypeDefTree {
    override def description: String = s"record $id"

    override def children: List[Ast] = typeParams ++ fields ++ directSupertypes
  }

  final case class FunDef(id: FunOrVarId, typeParams: List[TypeIdentifier], params: List[FunctionParam], optRetType: Option[TypeTree], bodyOpt: Option[Block],
                          visibility: Visibility, isMain: Boolean) extends Ast {
    override def children: List[Ast] = params ++ optRetType.toList ++ bodyOpt
  }

  final case class TypeAliasDef(id: TypeIdentifier, typeParams: List[TypeParam], params: List[TypeAliasParam], rhs: TypeTree) extends TopLevelDef {
    override def children: List[Ast] = params :+ rhs
  }
  
  sealed trait Param extends Ast

  sealed trait ClassParam extends Param

  sealed trait FunctionParam extends Param {
    val paramId: FunOrVarId
    val paramTypeTreeOpt: Option[TypeTree]
  }

  sealed trait RecordParam extends Param {
    val paramId: FunOrVarId
    val paramTypeTree: TypeTree
  }

  sealed trait TypeAliasParam extends Param {
    val paramId: FunOrVarId
    val paramTypeTree: TypeTree
  }

  sealed trait NonThisFunctionParam extends FunctionParam {
    val paramTypeTree: TypeTree
    override val paramTypeTreeOpt: Option[TypeTree] = Some(paramTypeTree)
  }

  final case class VarParam(paramId: FunOrVarId, paramTypeTree: TypeTree) extends ClassParam, NonThisFunctionParam {
    override def children: List[Ast] = List(paramTypeTree)
  }

  final case class SimpleParam(paramId: FunOrVarId, paramTypeTree: TypeTree) extends ClassParam, RecordParam, NonThisFunctionParam, TypeAliasParam {
    override def children: List[Ast] = List(paramTypeTree)
  }

  final case class ThisParam(paramTypeTreeOpt: Option[TypeTree]) extends FunctionParam {
    override val paramId: FunOrVarId = ThisId

    override def children: List[Ast] = paramTypeTreeOpt.toList
  }

  final case class ObjectImport(objectId: TypeIdentifier) extends ClassParam {
    override def children: List[Ast] = Nil
  }

  final case class TypeParam(id: TypeIdentifier, variance: Variance) extends Ast {
    override def children: List[Ast] = Nil
  }

  final case class LocalDef(
                             localName: FunOrVarId,
                             optTypeAnnot: Option[TypeTree],
                             rhsOpt: Option[Expr],
                             reassigStatus: ReassigPermission
                           ) extends Statement {
    override def children: List[Ast] = optTypeAnnot.toList ++ rhsOpt
  }

  sealed abstract class FormulaExpr extends Expr

  sealed abstract class NonFormulaExpr extends Expr

  sealed abstract class Literal extends FormulaExpr {
    final override def children: List[Ast] = Nil
  }

  sealed trait NumericLiteral extends Literal

  sealed trait NonNumericLiteral extends Literal

  /**
   * Integer literal
   */
  final case class IntLit(value: Int) extends NumericLiteral

  /**
   * Double literal
   */
  final case class DoubleLit(value: Double) extends NumericLiteral

  final case class UnitLit() extends NonNumericLiteral

  /**
   * Char literal
   */
  final case class CharLit(value: Char) extends NonNumericLiteral

  /**
   * Bool (boolean) literal
   */
  final case class BoolLit(value: Boolean) extends NonNumericLiteral

  /**
   * String literal
   */
  final case class StringLit(value: String) extends NonNumericLiteral

  /**
   * Occurrence of a variable (`val`, `var`, function parameter, etc.)
   */
  final case class VariableRef(name: FunOrVarId) extends FormulaExpr {
    override def children: List[Ast] = Nil
  }

  final case class ThisRef() extends FormulaExpr {
    override def children: List[Ast] = Nil
  }

  final case class ItRef() extends FormulaExpr {
    override def children: List[Ast] = Nil
  }

  final case class ObjectRef(objectName: TypeIdentifier) extends FormulaExpr {
    override def children: List[Ast] = Nil
  }

  final case class TypeAscription(expr: Expr, tpe: TypeTree) extends NonFormulaExpr {
    override def children: List[Ast] = List(expr, tpe)
  }

  /**
   * Function call: `callee(args)`
   */
  final case class Call(callee: Expr, typeArgs: List[TypeTree], args: List[Expr]) extends FormulaExpr {
    override def children: List[Ast] = callee :: typeArgs ++ args
  }

  final case class RecordOrClassInstantiation(typeId: TypeIdentifier, typeArgs: List[TypeTree], initializers: List[FieldInitializer]) extends NonFormulaExpr {
    override def children: List[Ast] = typeArgs ++ initializers
  }

  sealed abstract class FieldInitializer extends Ast {
    val fieldName: FunOrVarId
  }

  final case class FullFieldInitializer(fieldName: FunOrVarId, rhs: Expr) extends FieldInitializer {
    override def children: List[Ast] = List(rhs)
  }

  final case class ShorthandFieldInitializer(fieldName: FunOrVarId) extends FieldInitializer {
    override def children: List[Ast] = Nil
  }

  final case class UnaryOp(operator: Operator, operand: Expr) extends FormulaExpr {
    override def children: List[Ast] = List(operand)
  }

  final case class BinaryOp(lhs: Expr, operator: Operator, rhs: Expr) extends FormulaExpr {
    override def children: List[Ast] = List(lhs, rhs)
  }

  final case class Select(lhs: Expr, selected: FunOrVarId) extends FormulaExpr {
    override def children: List[Ast] = List(lhs)
  }
  
  final case class ClosureDef(params: List[(FunOrVarId, Option[TypeTree])], body: Block) extends NonFormulaExpr {
    override def children: List[Ast] = params.flatMap(_._2) :+ body
  }

  sealed abstract class Assignment extends Statement {
    def rhs: Expr

    def lhs: Expr
  }

  final case class VarAssig(lhs: Expr, rhs: Expr) extends Assignment {
    override def children: List[Ast] = List(lhs, rhs)
  }

  object VarAssig {

    def apply(lhs: Expr, typeAnnotOpt: Option[TypeTree], rhs: Expr): VarAssig = {
      val newLhs = typeAnnotOpt match {
        case Some(tpe) => TypeAscription(lhs, tpe).setPosition(lhs.getPosition)
        case None => lhs
      }
      new VarAssig(newLhs, rhs)
    }

    def unapply(assig: VarAssig): (Expr, Option[TypeTree], Expr) = {
      assig.lhs match {
        case TypeAscription(expr, tpe) => (expr, Some(tpe), assig.rhs)
        case _ => (assig.lhs, None, assig.rhs)
      }
    }

  }

  /**
   * In-place mutation, e.g. `x += 1`
   *
   * @param op the operator <b>without =</b>, e.g. `+` for a `+=` statement
   */
  final case class VarModif(lhs: Expr, rhs: Expr, op: Operator) extends Assignment {
    override def children: List[Ast] = List(lhs, rhs)
  }

  object VarModif {
    def unapply(varModif: VarModif): (Expr, Option[TypeTree], Expr, Operator) = {
      varModif.lhs match {
        case TypeAscription(expr, tpe) => (expr, Some(tpe), varModif.rhs, varModif.op)
        case _ => (varModif.lhs, None, varModif.rhs, varModif.op)
      }
    }
  }

  /**
   * If-then-else:
   * {{{
   *   if cond {
   *     thenBr
   *   } else {
   *     elseBr
   *   }
   * }}}
   */
  final case class IfThenElse(cond: Expr, thenBr: Statement, elseBrOpt: Option[Statement]) extends Statement with Conditional {
    override def children: List[Ast] = List(cond, thenBr) ++ elseBrOpt
  }

  /**
   * Ternary operator:
   * {{{
   *   when cond then thenBr else elseBr
   * }}}
   */
  final case class Ternary(cond: Expr, thenBr: Expr, elseBr: Expr) extends NonFormulaExpr with Conditional {
    override def children: List[Ast] = List(cond, thenBr, elseBr)

    override def elseBrOpt: Option[Statement] = Some(elseBr)
  }

  sealed abstract class Loop extends Statement

  /**
   * While loop:
   * {{{
   *   while cond {
   *     body stats
   *   }
   * }}}
   */
  final case class WhileLoop(cond: Expr, body: Statement) extends Loop {
    override def children: List[Ast] = List(cond, body)
  }

  /**
   * For loop:
   * {{{
   *   for initStats; cond; stepStats {
   *     body stats
   *   }
   * }}}
   */
  final case class ForLoop(
                            initStats: List[LocalDef | Assignment],
                            cond: Expr,
                            stepStats: List[Assignment],
                            body: Block
                          ) extends Loop {
    override def children: List[Ast] = initStats ++ List(cond) ++ stepStats :+ body
  }

  /**
   * `return` statement, with or without return value
   */
  final case class ReturnStat(optVal: Option[Expr]) extends Statement {
    override def children: List[Ast] = optVal.toList
  }

  /**
   * Cast, e.g. `x as Int`
   */
  final case class Cast(expr: Expr, tpe: BaseTypeTree) extends NonFormulaExpr {
    override def children: List[Ast] = List(expr, tpe)
  }

  /**
   * Type test, e.g. `x is Foo`
   */
  final case class TypeTest(expr: Expr, tpe: BaseTypeTree) extends FormulaExpr {
    override def children: List[Ast] = List(expr, tpe)
  }

  final case class PanicExpr(msg: Expr) extends NonFormulaExpr {
    override def children: List[Ast] = List(msg)
  }

  sealed trait TypeTree extends Ast

  final case class RefinedTypeTree(baseType: RefinableTypeTree, predicate: Expr) extends TypeTree {
    override def children: List[Ast] = List(baseType, predicate)
  }

  sealed trait BaseTypeTree extends TypeTree
  sealed trait RefinableTypeTree extends BaseTypeTree

  final case class PrimitiveTypeTree(primitiveType: PrimitiveType) extends RefinableTypeTree {
    override def children: List[Ast] = Nil
  }

  final case class NamedTypeTree(name: TypeIdentifier, typeArgs: List[TypeTree], args: List[Expr]) extends RefinableTypeTree {
    override def children: List[Ast] = typeArgs ++ args
  }
  
  final case class ClosureTypeTree(paramTypes: List[TypeTree], resultType: TypeTree) extends BaseTypeTree {
    override def children: List[Ast] = paramTypes :+ resultType
  }

  sealed abstract class CaptureSetTree extends Ast

  final case class ExplicitCaptureSetTree(capturedExpressions: List[Expr]) extends CaptureSetTree {
    override def children: List[Ast] = capturedExpressions
  }

  final case class ImplicitRootCaptureSetTree() extends CaptureSetTree {
    override def children: List[Ast] = Nil
  }

  sealed trait Conditional {
    def cond: Expr

    def thenBr: Statement

    def elseBrOpt: Option[Statement]
  }

  private[Asts] class OptionalAttribute[A] {
    private var valueOpt: Option[A] = None

    def setOpt(valueOpt: Option[A]): Unit = {
      this.valueOpt = valueOpt
    }

    def set(value: A): Unit = {
      setOpt(Some(value))
    }

    def getOpt: Option[A] = valueOpt

    override def toString: String = valueOpt.getOrElse("<empty>").toString
  }

}
