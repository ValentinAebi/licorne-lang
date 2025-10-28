package compiler.irs

import compiler.reporting.Position
import identifiers.*
import lang.*
import lang.Types.*
import lang.Types.PrimitiveTypeShape.*

import scala.annotation.targetName

// TODO check lists of children (all node types)

object Asts {

  sealed abstract class Ast {
    // Positions are propagated by the TreeParser
    // Each AST is assigned the position of its leftmost token (by the map method of TreeParser)
    private val positionMemo = new OptionalAttribute[Position]

    export positionMemo.setOpt as setPosition
    export positionMemo.set as setPosition
    export positionMemo.getOpt as getPosition

    // TODO test all implementations of children
    def children: List[Ast]
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

  sealed abstract class TopLevelDef extends Ast

  sealed trait TypeDefTree extends TopLevelDef {
    def id: TypeIdentifier

    def directSupertypes: Seq[TypeShapeTree]
  }

  final case class InterfaceDef(
                                 id: TypeIdentifier,
                                 typeParams: List[TypeParam],
                                 functions: List[FunDef],
                                 directSupertypes: List[TypeShapeTree]
                               ) extends TypeDefTree {
    override def children: List[Ast] = functions ++ directSupertypes
  }

  final case class PackageDef(
                               id: TypeIdentifier,
                               importedPackages: List[TypeIdentifier],
                               functions: List[FunDef],
                               directSupertypes: List[TypeShapeTree]
                             ) extends TypeDefTree {
    override def children: List[Ast] = functions ++ directSupertypes
  }

  final case class ClassDef(
                             id: TypeIdentifier,
                             typeParams: List[TypeParam],
                             params: List[ClassParam],
                             functions: List[FunDef],
                             directSupertypes: List[TypeShapeTree]
                           ) extends TypeDefTree {
    override def children: List[Ast] = typeParams ++ params ++ functions ++ directSupertypes
  }

  final case class DatatypeDef(
                                id: TypeIdentifier,
                                typeParams: List[TypeParam],
                                directSupertypes: List[TypeShapeTree]
                              ) extends TypeDefTree {
    override def children: List[Ast] = typeParams ++ directSupertypes
  }

  /**
   * Structure (`struct`) or datatype definition
   */
  final case class StructDef(
                              id: TypeIdentifier,
                              typeParams: List[TypeParam],
                              fields: List[StructParam],
                              directSupertypes: List[TypeShapeTree]
                            ) extends TypeDefTree {
    override def children: List[Ast] = typeParams ++ fields ++ directSupertypes
  }

  /**
   * Function definition
   */
  final case class FunDef(id: FunOrVarId, typeParams: List[TypeIdentifier], params: List[FunctionParam], optRetType: Option[TypeTree], bodyOpt: Option[Block],
                          visibility: Visibility, isMain: Boolean) extends Ast {
    override def children: List[Ast] = params ++ optRetType.toList ++ bodyOpt
  }

  final case class TypeAliasDef(typeName: TypeIdentifier, typeParams: List[TypeIdentifier], params: List[TypeAliasParam], rhs: TypeTree) extends TopLevelDef {
    override def children: List[Ast] = params :+ rhs
  }

  sealed trait ClassParam extends Ast

  sealed trait FunctionParam extends Ast {
    val paramId: FunOrVarId
    val paramTypeTree: TypeTree
  }

  sealed trait StructParam extends Ast {
    val paramId: FunOrVarId
    val paramTypeTree: TypeTree
  }

  sealed trait TypeAliasParam extends Ast {
    val paramId: FunOrVarId
    val paramTypeTree: TypeTree
  }

  final case class VarParam(paramId: FunOrVarId, paramTypeTree: TypeTree) extends ClassParam, FunctionParam {
    override def children: List[Ast] = List(paramTypeTree)
  }

  final case class SimpleParam(paramId: FunOrVarId, paramTypeTree: TypeTree) extends ClassParam, StructParam, FunctionParam, TypeAliasParam {
    override def children: List[Ast] = List(paramTypeTree)
  }

  final case class PackageImport(packageId: TypeIdentifier) extends ClassParam {
    override def children: List[Ast] = Nil
  }

  final case class TypeParam(id: TypeIdentifier, variance: Variance) extends Ast {
    override def children: List[Ast] = Nil
  }

  /**
   * `val` or `var` definition
   *
   * @param isReassignable `true` if `var`, `false` if `val`
   */
  final case class LocalDef(
                             localName: FunOrVarId,
                             optTypeAnnot: Option[TypeTree],
                             rhsOpt: Option[Expr],
                             isReassignable: Boolean
                           ) extends Statement {
    val keyword: Keyword = if isReassignable then Keyword.Var else Keyword.Val

    override def children: List[Ast] = optTypeAnnot.toList ++ rhsOpt
  }

  sealed abstract class Literal extends Expr {
    val value: Any

    final override def children: List[Ast] = Nil

    def getTypeShapeOpt: Option[TypeShape]

    final def getTypeShape: TypeShape = {
      getTypeShapeOpt match
        case Some(shape) => shape
        case None => throw new NoSuchElementException(s"type missing in $this")
    }
  }

  sealed trait NumericLiteral extends Literal

  sealed trait NonNumericLiteral extends Literal

  /**
   * Integer literal
   */
  final case class IntLit(value: Int) extends NumericLiteral {
    override def getTypeShapeOpt: Option[TypeShape] = Some(IntType)
  }

  /**
   * Double literal
   */
  final case class DoubleLit(value: Double) extends NumericLiteral {
    override def getTypeShapeOpt: Option[TypeShape] = Some(DoubleType)
  }

  /**
   * Char literal
   */
  final case class CharLit(value: Char) extends NonNumericLiteral {
    override def getTypeShapeOpt: Option[TypeShape] = Some(CharType)
  }

  /**
   * Bool (boolean) literal
   */
  final case class BoolLit(value: Boolean) extends NonNumericLiteral {
    override def getTypeShapeOpt: Option[TypeShape] = Some(BoolType)
  }

  /**
   * String literal
   */
  final case class StringLit(value: String) extends NonNumericLiteral {
    override def getTypeShapeOpt: Option[TypeShape] = Some(StringType)
  }

  /**
   * Occurrence of a variable (`val`, `var`, function parameter, etc.)
   */
  final case class VariableRef(name: FunOrVarId) extends Expr {
    override def children: List[Ast] = Nil
  }

  final case class ThisRef() extends Expr {
    override def children: List[Ast] = Nil
  }

  final case class PackageRef(pkgName: TypeIdentifier) extends Expr {
    override def children: List[Ast] = Nil
  }

  /**
   * Function call: `callee(args)`
   */
  final case class Call(receiverOpt: Option[Expr], funId: FunOrVarId, args: List[Expr], isTailrec: Boolean) extends Expr {
    override def children: List[Ast] = receiverOpt.toList ++ args
  }

  /**
   * Array indexing: `indexed[arg]`
   */
  final case class Indexing(indexed: Expr, arg: Expr) extends Expr {
    override def children: List[Ast] = List(indexed, arg)
  }

  /**
   * Initialization of an (empty) array
   */
  final case class ArrayInit(elemType: TypeTree, size: Expr) extends Expr {
    override def children: List[Ast] = List(elemType, size)
  }

  /**
   * Initialization of an array that contains all the elements in `arrayElems` (in order)
   */
  final case class FilledArrayInit(arrayElems: List[Expr]) extends Expr {
    override def children: List[Ast] = arrayElems
  }

  final case class StructOrModuleInstantiation(typeId: TypeIdentifier, args: List[Expr]) extends Expr {
    override def children: List[Ast] = args
  }

  /**
   * Unary operator
   */
  final case class UnaryOp(operator: Operator, operand: Expr) extends Expr {
    override def children: List[Ast] = List(operand)
  }

  /**
   * Binary operator
   */
  final case class BinaryOp(lhs: Expr, operator: Operator, rhs: Expr) extends Expr {
    override def children: List[Ast] = List(lhs, rhs)
  }

  /**
   * Access to a struct field: `lhs.select`
   */
  final case class Select(lhs: Expr, selected: FunOrVarId) extends Expr {
    override def children: List[Ast] = List(lhs)
  }

  sealed abstract class Assignment extends Statement {
    def rhs: Expr

    def lhs: Expr
  }

  /**
   * Assignment of a value to a variable (or struct field, or in an array): `lhs = rhs`
   */
  final case class VarAssig(lhs: Expr, rhs: Expr) extends Assignment {
    override def children: List[Ast] = List(lhs, rhs)
  }

  /**
   * In-place mutation of a variable (or struct field, or in an array), e.g. `x += 1`
   *
   * @param op the operator <b>without =</b>, e.g. `+` in a `+=` expression
   */
  final case class VarModif(lhs: Expr, rhs: Expr, op: Operator) extends Assignment {
    override def children: List[Ast] = List(lhs, rhs)
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
  final case class Ternary(cond: Expr, thenBr: Expr, elseBr: Expr) extends Expr with Conditional {
    override def children: List[Ast] = List(cond, thenBr, elseBr)

    override def elseBrOpt: Option[Statement] = Some(elseBr)
  }

  /**
   * While loop:
   * {{{
   *   while cond {
   *     body stats
   *   }
   * }}}
   */
  final case class WhileLoop(cond: Expr, body: Statement) extends Statement {
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
                          ) extends Statement {
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
  final case class Cast(expr: Expr, tpe: TypeShapeTree) extends Expr {
    override def children: List[Ast] = List(expr, tpe)
  }

  /**
   * Type test, e.g. `x is Foo`
   */
  final case class TypeTest(expr: Expr, tpe: TypeShapeTree) extends Expr {
    override def children: List[Ast] = List(expr, tpe)
  }

  /**
   * `panic` statement
   */
  final case class PanicStat(msg: Expr) extends Statement {
    override def children: List[Ast] = List(msg)
  }

  /**
   * Node generated by lowering
   *
   * @param stats statements to be executed before [[expr]]
   * @param expr  the expression to be executed after [[stats]]. Its return value will be the return value of the whole Sequence
   */
  final case class Sequence(stats: List[Statement], expr: Expr) extends Expr {
    override def children: List[Ast] = stats :+ expr
  }

  sealed trait TypeTree extends Ast {
    def withRefinement(predicate: Expr): RefinedTypeTree = RefinedTypeTree(this, predicate)
  }

  final case class RefinedTypeTree(baseType: TypeTree, predicate: Expr) extends TypeTree {
    override def children: List[Ast] = List(baseType, predicate)
  }

  final case class CapturingTypeTree(typeShapeTree: TypeShapeTree, captureDescr: CaptureSetTree) extends TypeTree {
    override def children: List[Ast] = List(typeShapeTree, captureDescr)
  }

  sealed trait TypeShapeTree extends TypeTree {

    @targetName("capturing") infix def ^(capDescr: CaptureSetTree): CapturingTypeTree =
      CapturingTypeTree(this, capDescr)

    @targetName("maybeCapturing") infix def ^(capDescrOpt: Option[CaptureSetTree]): TypeTree =
      capDescrOpt.map { capDescr =>
        this ^ capDescr
      }.getOrElse(this)

  }

  final case class PrimitiveTypeShapeTree(primitiveType: PrimitiveTypeShape) extends TypeShapeTree {
    override def children: List[Ast] = Nil
  }

  final case class NamedTypeShapeTree(name: TypeIdentifier, typeParams: List[TypeTree], params: List[Expr]) extends TypeShapeTree {
    override def children: List[Ast] = typeParams
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
