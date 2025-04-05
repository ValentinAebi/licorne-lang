package compiler.irs

import compiler.reporting.Position
import identifiers.*
import lang.*
import lang.CaptureDescriptors.*
import lang.Types.*
import lang.Types.PrimitiveTypeShape.*

import scala.annotation.targetName

object Asts {

  sealed abstract class Ast {
    // Positions are propagated by the TreeParser
    // Each AST is assigned the position of its leftmost token (by the map method of TreeParser)
    private val positionMemo = new Memo[Position]
    
    export positionMemo.setOpt as setPosition
    export positionMemo.set as setPosition
    export positionMemo.getOpt as getPosition

    def children: List[Ast]

    final def collect[T](f: Ast => T): List[T] = {
      f(this) :: children.flatMap(_.collect(f))
    }

    /**
     * Crashes the compiler if at least 1 expression in the AST has no type (i.e. `expr.getTypeOpt.isEmpty`)
     */
    final def assertAllTypesAreSet(): Unit = {
      collect {
        case expr: Expr => assert(expr.getTypeOpt.isDefined, s"no type set for $expr")
        case _ => ()
      }
    }
  }

  sealed abstract class Statement extends Ast

  sealed abstract class Expr extends Statement {
    private val typeMemo = new Memo[Type]

    /**
     * Set the type that has been inferred for this expression
     *
     * WARNING: since subclasses are allowed to override [[getTypeOpt]], setting a type might have no effect
     */
    def setTypeOpt(tpe: Option[Type]): Expr = {
      typeMemo.setOpt(tpe)
      this
    }

    /**
     * See [[setTypeOpt]]
     */
    final def setType(tpe: Type): Expr = {
      setTypeOpt(Some(tpe))
    }

    /**
     * @return the type that has been inferred for this expression
     *
     *         WARNING: might be overriden by subclasses if they are able to infer their type from the types of their children
     */
    def getTypeOpt: Option[Type] = typeMemo.getOpt

    /**
     * See [[getTypeOpt]]
     */
    def getType: Type = {
      getTypeOpt match
        case Some(tpe) => tpe
        case None => throw new NoSuchElementException(s"type missing in $this")
    }
    
    def getTypeShape: TypeShape = getType.shape

  }

  /**
   * Code source (most of the time a file)
   */
  final case class Source(defs: List[TopLevelDef], languageMode: LanguageMode) extends Ast {
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
    def name: TypeIdentifier

    def directSupertypes: Seq[TypeIdentifier]

    def isAbstract: Boolean
  }

  sealed trait ModuleOrPackageDefTree extends TypeDefTree {
    def functions: List[FunDef]

    def isPackage: Boolean
  }

  final case class PackageDef(packageName: TypeIdentifier, functions: List[FunDef]) extends ModuleOrPackageDefTree {
    override def name: TypeIdentifier = packageName

    override def directSupertypes: Seq[TypeIdentifier] = Nil

    override def isAbstract: Boolean = false

    override def children: List[Ast] = functions

    override def isPackage: Boolean = true
  }

  final case class ModuleDef(
                              moduleName: TypeIdentifier,
                              imports: List[Import],
                              functions: List[FunDef]
                            ) extends ModuleOrPackageDefTree {
    override def name: TypeIdentifier = moduleName

    override def directSupertypes: Seq[TypeIdentifier] = Nil

    override def isAbstract: Boolean = false

    override def children: List[Ast] = imports ++ functions

    override def isPackage: Boolean = false
  }

  sealed trait Import extends Ast

  final case class ParamImport(paramId: FunOrVarId, paramType: TypeTree) extends Import {
    override def children: List[Ast] = List(paramType)
  }

  final case class PackageImport(packageId: TypeIdentifier, isMarked: Boolean) extends Import {
    override def children: List[Ast] = Nil
  }

  final case class DeviceImport(device: Device) extends Import {
    override def children: List[Ast] = Nil
  }


  /**
   * Structure (`struct`) or datatype definition
   */
  final case class StructDef(
                              structName: TypeIdentifier,
                              isShallowMutable: Boolean,
                              fields: List[Param],
                              directSupertypes: Seq[TypeIdentifier],
                              isAbstract: Boolean
                            ) extends TypeDefTree {
    override def name: TypeIdentifier = structName

    override def children: List[Ast] = fields
  }

  /**
   * Function definition
   */
  final case class FunDef(funName: FunOrVarId, params: List[Param], optRetType: Option[TypeTree], body: Block,
                          visibility: Visibility, isMain: Boolean) extends Ast {
    private val signatureMemo = new Memo[FunctionSignature]
    
    export signatureMemo.setOpt as setSignatureOpt
    export signatureMemo.set as setSignature
    export signatureMemo.getOpt as getSignatureOpt

    override def children: List[Ast] = params ++ optRetType.toList :+ body
  }

  /**
   * Parameter of a function or field of a struct
   */
  final case class Param(
                          paramNameOpt: Option[FunOrVarId],
                          tpe: TypeTree,
                          isReassignable: Boolean
                        ) extends Ast {
    override def children: List[Ast] = List(tpe)
  }

  /**
   * Constant definition
   */
  final case class ConstDef(constName: FunOrVarId, tpeOpt: Option[TypeTree], value: Literal) extends TopLevelDef {
    override def children: List[Ast] = tpeOpt.toList :+ value
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

    private val varTypeMemo = new Memo[Type]
    
    export varTypeMemo.setOpt as setVarTypeOpt
    export varTypeMemo.set as setVarType
    export varTypeMemo.getOpt as getVarTypeOpt

    val keyword: Keyword = if isReassignable then Keyword.Var else Keyword.Val

    override def children: List[Ast] = optTypeAnnot.toList ++ rhsOpt
  }

  sealed abstract class Literal extends Expr {
    val value: Any

    final override def children: List[Ast] = Nil

    override def getTypeOpt: Option[Type]

    final override def getType: Type = {
      getTypeOpt match
        case Some(tpe) => tpe
        case None => throw new NoSuchElementException(s"type missing in $this")
    }
    
    def freshCopyWithoutPos: Literal
  }

  sealed trait NumericLiteral extends Literal

  sealed trait NonNumericLiteral extends Literal

  /**
   * Integer literal
   */
  final case class IntLit(value: Int) extends NumericLiteral {
    override def getTypeOpt: Option[TypeShape] = Some(IntType)
    
    override def freshCopyWithoutPos: Literal = IntLit(value)
  }

  /**
   * Double literal
   */
  final case class DoubleLit(value: Double) extends NumericLiteral {
    override def getTypeOpt: Option[TypeShape] = Some(DoubleType)

    override def freshCopyWithoutPos: Literal = DoubleLit(value)
  }

  /**
   * Char literal
   */
  final case class CharLit(value: Char) extends NonNumericLiteral {
    override def getTypeOpt: Option[TypeShape] = Some(CharType)

    override def freshCopyWithoutPos: Literal = CharLit(value)
  }

  /**
   * Bool (boolean) literal
   */
  final case class BoolLit(value: Boolean) extends NonNumericLiteral {
    override def getTypeOpt: Option[TypeShape] = Some(BoolType)

    override def freshCopyWithoutPos: Literal = BoolLit(value)
  }

  /**
   * String literal
   */
  final case class StringLit(value: String) extends NonNumericLiteral {
    override def getTypeOpt: Option[TypeShape] = Some(StringType)

    override def freshCopyWithoutPos: Literal = StringLit(value)
  }

  final case class RegionCreation() extends Expr {
    override def children: List[Ast] = Nil

    override def getTypeOpt: Option[Type] = Some(RegionType ^ CaptureSet.singletonOfRoot)
  }

  /**
   * Occurrence of a variable (`val`, `var`, function parameter, etc.)
   */
  final case class VariableRef(name: FunOrVarId) extends Expr {
    private var _isRefToConst: Boolean = false
    
    def markAsRefToConst(): Unit = {
      _isRefToConst = true
    }
    
    def isRefToConst: Boolean = _isRefToConst
    
    override def children: List[Ast] = Nil
  }

  final case class MeRef() extends Expr {
    override def children: List[Ast] = Nil
  }

  final case class PackageRef(pkgName: TypeIdentifier) extends Expr {
    override def children: List[Ast] = Nil
  }

  final case class DeviceRef(device: Device) extends Expr {
    override def children: List[Ast] = Nil
  }

  /**
   * Function call: `callee(args)`
   */
  final case class Call(receiverOpt: Option[Expr], function: FunOrVarId, args: List[Expr], isTailrec: Boolean) extends Expr {
    private val signatureMemo = new Memo[FunctionSignature]
    private val meTypeMemo = new Memo[Type]
    
    export signatureMemo.setOpt as setResolvedSigOpt
    export signatureMemo.set as setResolvedSig
    export signatureMemo.getOpt as getSignatureOpt
    export meTypeMemo.set as cacheMeType
    export meTypeMemo.getOpt as getMeTypeOpt

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
  final case class ArrayInit(regionOpt: Option[Expr], elemType: TypeTree, size: Expr) extends Expr {
    override def children: List[Ast] = regionOpt.toList ++ List(elemType, size)
  }

  /**
   * Initialization of an array that contains all the elements in `arrayElems` (in order)
   */
  final case class FilledArrayInit(arrayElems: List[Expr], regionOpt: Option[Expr]) extends Expr {
    override def children: List[Ast] = arrayElems ++ regionOpt
  }

  final case class StructOrModuleInstantiation(regionOpt: Option[Expr], typeId: TypeIdentifier, args: List[Expr]) extends Expr {
    override def children: List[Ast] = regionOpt.toList ++ args
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
  final case class BinaryOp(lhs: Expr, operator: Operator, rhs: Expr) extends Expr with SmartCastsAware {

    override def cond: Expr = lhs

    override def thenBr: Statement = rhs

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
    private var unfeasibleElseFlag: Boolean = false
    
    def elseIsUnfeasible: Boolean = unfeasibleElseFlag
    
    def markUnfeasibleElse(): Unit = {
      unfeasibleElseFlag = true
    }
    
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
  final case class Cast(expr: Expr, tpe: CastTargetTypeShapeTree) extends Expr {
    private var _isTransparentCast: Boolean = false

    def isTransparentCast: Boolean = _isTransparentCast

    def markTransparent(): Unit = {
      _isTransparentCast = true
    }

    override def children: List[Ast] = List(expr, tpe)
  }

  /**
   * Type test, e.g. `x is Foo`
   */
  final case class TypeTest(expr: Expr, tpe: CastTargetTypeShapeTree) extends Expr {
    override def children: List[Ast] = List(expr, tpe)
  }

  /**
   * `panic` statement
   */
  final case class PanicStat(msg: Expr) extends Statement {
    override def children: List[Ast] = List(msg)
  }
  
  final case class RestrictedStat(captureSet: ExplicitCaptureSetTree, body: Block) extends Statement {
    override def children: List[Ast] = List(captureSet, body)
  }

  final case class EnclosedStat(captureSet: ExplicitCaptureSetTree, body: Block) extends Statement {
    override def children: List[Ast] = List(captureSet, body)
  }

  /**
   * Node generated by lowering
   *
   * @param stats statements to be executed before [[expr]]
   * @param expr  the expression to be executed after [[stats]]. Its return value will be the return value of the whole Sequence
   */
  final case class Sequence(stats: List[Statement], expr: Expr) extends Expr {
    override def children: List[Ast] = stats :+ expr

    override def getTypeOpt: Option[Type] = expr.getTypeOpt
  }

  sealed trait TypeTree extends Ast {
    def getResolvedTypeOpt: Option[Type]
    def getResolvedType: Type = getResolvedTypeOpt.get
  }
  
  final case class CapturingTypeTree(
                                      typeShapeTree: TypeShapeTree,
                                      captureDescr: CaptureDescrTree
                                    ) extends TypeTree {
    def getResolvedTypeOpt: Option[Type] = {
      for {
        shape <- typeShapeTree.getResolvedTypeOpt
        capDescr <- captureDescr.getResolvedDescrOpt
      } yield CapturingType(shape, capDescr)
    }

    override def children: List[Ast] = List(typeShapeTree, captureDescr)
  }
  
  final case class WrapperTypeTree(tpe: Type) extends TypeTree {
    override def getResolvedTypeOpt: Option[Type] = Some(tpe)

    override def children: List[Ast] = Nil
  }
  
  sealed trait TypeShapeTree extends TypeTree {
    
    @targetName("capturing") infix def ^(capDescr: CaptureDescrTree): CapturingTypeTree =
      CapturingTypeTree(this, capDescr)
      
    @targetName("maybeCapturing") infix def ^(capDescrOpt: Option[CaptureDescrTree]): TypeTree =
      capDescrOpt.map { capDescr =>
        this ^ capDescr
      }.getOrElse(this)
    
    override def getResolvedTypeOpt: Option[TypeShape]
    
  }
  
  sealed abstract class CastTargetTypeShapeTree extends TypeShapeTree {
    override def getResolvedTypeOpt: Option[CastTargetTypeShape]
  }

  final case class PrimitiveTypeShapeTree(primitiveType: PrimitiveTypeShape) extends CastTargetTypeShapeTree {
    override def getResolvedTypeOpt: Option[CastTargetTypeShape] = Some(primitiveType)

    override def children: List[Ast] = Nil
  }

  final case class NamedTypeShapeTree(name: TypeIdentifier) extends CastTargetTypeShapeTree {
    override def getResolvedTypeOpt: Option[CastTargetTypeShape] = Some(NamedTypeShape(name))

    override def children: List[Ast] = Nil
  }

  final case class ArrayTypeShapeTree(elemType: TypeTree) extends TypeShapeTree {
    override def getResolvedTypeOpt: Option[TypeShape] = {
      elemType.getResolvedTypeOpt.map(ArrayTypeShape(_))
    }

    override def children: List[Ast] = List(elemType)
  }

  sealed abstract class CaptureDescrTree extends Ast {
    private val descrMemo = new Memo[CaptureDescriptor]
    
    export descrMemo.setOpt as setResolvedDescrOpt
    export descrMemo.set as setResolvedDescr
    export descrMemo.getOpt as getResolvedDescrOpt
  }

  final case class ExplicitCaptureSetTree(capturedExpressions: List[Expr]) extends CaptureDescrTree {
    override def children: List[Ast] = capturedExpressions
  }

  final case class ImplicitRootCaptureSetTree() extends CaptureDescrTree {
    override def children: List[Ast] = Nil
  }

  final case class MarkTree() extends CaptureDescrTree {
    override def children: List[Ast] = Nil
  }

  trait SmartCastsAware extends Ast {
    private var smartCasts: Map[FunOrVarId, Type] = Map.empty

    def cond: Expr

    def thenBr: Statement

    def setSmartCasts(smartcasts: Map[FunOrVarId, Type]): Unit = {
      this.smartCasts = smartcasts
    }

    def getSmartCasts: Map[FunOrVarId, Type] = smartCasts
  }

  trait Conditional extends SmartCastsAware {
    def cond: Expr

    def thenBr: Statement

    def elseBrOpt: Option[Statement]
  }
  
  private class Memo[A] {
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
