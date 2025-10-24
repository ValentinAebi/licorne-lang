package compiler.lowerer

import compiler.analysisctx.AnalysisContext
import compiler.irs.Asts.*
import compiler.pipeline.CompilerStep
import compiler.reporting.Position
import identifiers.FunOrVarId
import lang.Operator.*
import lang.Types
import lang.Types.*
import lang.Types.PrimitiveTypeShape.*

// TODO propagate constants and evaluate constant expressions
/**
 * Lowering replaces (this list may not be complete):
 *  - `x > y` ---> `!(x <= y)`
 *  - `x >= y ---> !(x < y)`
 *  - `x != y` ---> `!(x == y)`
 *  - `x += y` ---> `x = x + y`
 *  - `for` ---> `while`
 *  - `!x` ---> `when x then false else true`
 *  - `x && y` ---> `when x then y else false`
 *  - `x || y` ---> `when x then true else y`
 *  - `[x_1, ... , x_n]` ---> `val $0 = arr Int[n]; $0[0] = x_1; ... ; $0[n-1] = x_n; $0`
 *  - references to constants ---> their value
 *
 * Simple optimizations:
 *  - `when true then x else y` ---> `x` (same for false and for if)
 *  - `when x then true else false` ---> `x`
 */
final class Lowerer extends CompilerStep[(List[Source], AnalysisContext), (List[Source], AnalysisContext)] {
  private val uniqueIdGenerator = new UniqueIdGenerator()

  override def apply(input: (List[Source], AnalysisContext)): (List[Source], AnalysisContext) = {
    val (sources, analysisContext) = input
    given LoweringContext = createCtx(sources)
    val loweredSources = sources.map(lower)
    loweredSources.foreach(_.assertAllTypesAreSet())
    (loweredSources, analysisContext)
  }

  private def createCtx(sources: List[Source]): LoweringContext = {
    val constantsBuilder = Map.newBuilder[FunOrVarId, Literal]
    for src <- sources do {
      src.defs.foreach {
        case ConstDef(constName, tpeOpt, value) => constantsBuilder.addOne(constName -> value)
        case _ => ()
      }
    }
    LoweringContext(constantsBuilder.result())
  }

  private def lower(src: Source)(using LoweringContext): Source = propagatePosition(src.getPosition) {
    Source(src.defs.filterNot(_.isInstanceOf[ConstDef]).map(lower)).setName(src.getName)
  }

  private def lower(block: Block)(using LoweringContext): Block = propagatePosition(block.getPosition) {
    Block(block.stats.map(lower))
  }

  private def lower(funDef: FunDef)(using LoweringContext): FunDef = propagatePosition(funDef.getPosition) {
    val loweredFunDef = FunDef(
      funDef.funName,
      funDef.params.map(lower),
      funDef.optRetType,
      lower(funDef.body),
      funDef.visibility,
      isMain = funDef.isMain
    )
    loweredFunDef.setSignatureOpt(funDef.getSignatureOpt)
    loweredFunDef
  }

  private def lower(structDef: StructDef)(using LoweringContext): StructDef = propagatePosition(structDef.getPosition) {
    StructDef(
      structDef.structName,
      structDef.fields.map(lower),
      structDef.directSupertypes,
      structDef.isAbstract
    )
  }
  
  private def lower(moduleDef: ModuleDef)(using LoweringContext): ModuleDef = propagatePosition(moduleDef.getPosition) {
    ModuleDef(
      moduleDef.moduleName,
      moduleDef.imports.map(lower),
      moduleDef.functions.map(lower)
    )
  }
  
  private def lower(packageDef: PackageDef)(using LoweringContext): PackageDef = propagatePosition(packageDef.getPosition) {
    PackageDef(
      packageDef.packageName,
      packageDef.functions.map(lower)
    )
  }

  private def lower(param: Param)(using LoweringContext): Param = Param(
    param.paramNameOpt,
    lower(param.tpe),
    param.isReassignable
  )

  private def lower(imp: Import)(using LoweringContext): Import = imp match {
    case ParamImport(paramId, paramType) =>
      ParamImport(paramId, lower(paramType))
    case packageImport: PackageImport => packageImport
    case deviceImport: DeviceImport => deviceImport
  }

  private def lower(localDef: LocalDef)(using LoweringContext): LocalDef = propagatePosition(localDef.getPosition) {
    val loweredLocal = LocalDef(localDef.localName, localDef.optTypeAnnot.map(lower), localDef.rhsOpt.map(lower),
      localDef.isReassignable)
    loweredLocal.setVarTypeOpt(localDef.getVarTypeOpt)
    loweredLocal
  }

  private def lower(varAssig: VarAssig)(using LoweringContext): VarAssig = propagatePosition(varAssig.getPosition) {
    VarAssig(lower(varAssig.lhs), lower(varAssig.rhs))
  }

  private def lower(varModif: VarModif)(using LoweringContext): VarAssig = propagatePosition(varModif.getPosition) {
    val VarModif(lhs, rhs, op) = varModif
    val loweredLhs = lower(lhs)
    val loweredRhs = lower(rhs)
    VarAssig(loweredLhs, BinaryOp(loweredLhs, op, loweredRhs).setType(lhs.getType))
  }

  private def lower(ifThenElse: IfThenElse)(using LoweringContext): Statement = propagatePosition(ifThenElse.getPosition) {
    val loweredIte = IfThenElse(
      lower(ifThenElse.cond),
      lower(ifThenElse.thenBr),
      ifThenElse.elseBrOpt.map(lower).orElse {
        if ifThenElse.elseIsUnfeasible
        then Some(PanicStat(StringLit("incomplete pattern match (should never happen, compiler error)")))
        else None
      }
    )
    loweredIte.setSmartCasts(ifThenElse.getSmartCasts)
    loweredIte match {
      case IfThenElse(BoolLit(true), loweredThenBr, _) =>
        loweredThenBr
      case IfThenElse(BoolLit(false), _, loweredElseBrOpt) =>
        loweredElseBrOpt.getOrElse(Block(List.empty))
      case _ => loweredIte
    }
  }

  private def lower(whileLoop: WhileLoop)(using LoweringContext): WhileLoop = propagatePosition(whileLoop.getPosition) {
    WhileLoop(lower(whileLoop.cond), lower(whileLoop.body))
  }

  private def lower(forLoop: ForLoop)(using LoweringContext): Block = propagatePosition(forLoop.getPosition) {
    val body = Block(
      forLoop.body.stats ++ forLoop.stepStats
    )
    val stats: List[Statement] = forLoop.initStats :+ WhileLoop(forLoop.cond, body)
    lower(Block(stats))
  }

  private def lower(returnStat: ReturnStat)(using LoweringContext): ReturnStat = propagatePosition(returnStat.getPosition) {
    ReturnStat(returnStat.optVal.map(lower))
  }

  private def lower(panicStat: PanicStat)(using LoweringContext): PanicStat = propagatePosition(panicStat.getPosition) {
    PanicStat(lower(panicStat.msg))
  }

  private def lower(expr: Expr)(using ctx: LoweringContext): Expr = propagatePosition(expr.getPosition) {
    val lowered = expr match {
      case literal: Literal => literal
      case varRef@VariableRef(name) if varRef.isRefToConst => ctx.literalFor(name)
      case varRef: VariableRef => varRef
      case meRef: MeRef => meRef
      case packageRef: PackageRef => packageRef
      case deviceRef: DeviceRef => deviceRef
      case call: Call => lower(call)
      case indexing: Indexing => Indexing(lower(indexing.indexed), lower(indexing.arg))
      case arrayInit: ArrayInit => ArrayInit(lower(arrayInit.elemType), lower(arrayInit.size))
      case instantiation: StructOrModuleInstantiation =>
        StructOrModuleInstantiation(instantiation.typeId, instantiation.args.map(lower))
      
      // [x_1, ... , x_n] ---> explicit assignments
      case filledArrayInit@FilledArrayInit(arrayElems) =>
        val arrayType = filledArrayInit.getType
        val arrayShape = arrayType.shape.asInstanceOf[ArrayTypeShape]
        val elemType = arrayShape.elemType
        val arrValId = uniqueIdGenerator.next()
        val arrValRef = VariableRef(arrValId).setType(arrayType)
        val arrInit = ArrayInit(WrapperTypeTree(elemType), IntLit(arrayElems.size)).setType(arrayType)
        val arrayValDefinition = LocalDef(arrValId, Some(WrapperTypeTree(arrayType)), Some(arrInit), isReassignable = false)
        arrayValDefinition.setVarType(arrayType)
        val arrElemAssigStats = arrayElems.map(lower).zipWithIndex.map {
          (elem, idx) => VarAssig(Indexing(arrValRef, IntLit(idx)).setType(UndefinedTypeShape), elem)
        }
        Sequence(arrayValDefinition :: arrElemAssigStats, arrValRef)
        
      case UnaryOp(operator, operand) =>
        val loweredOperand = lower(operand)
        operator match {
          case ExclamationMark => Ternary(loweredOperand, BoolLit(false), BoolLit(true))
          case _ => UnaryOp(operator, loweredOperand)
        }
        
      case binaryOp: BinaryOp => {
        val loweredLhs = lower(binaryOp.lhs)
        val loweredRhs = lower(binaryOp.rhs)
        binaryOp.operator match {
          
          // x > y ---> !(x <= y)
          case GreaterThan =>
            lower(negatedBool(BinaryOp(loweredLhs, LessOrEq, loweredRhs)))

          // x >= y ---> !(x < y)
          case GreaterOrEq =>
            lower(negatedBool(BinaryOp(loweredLhs, LessThan, loweredRhs)))
          
          // x != y ---> !(x == y)
          case Inequality =>
            lower(negatedBool(BinaryOp(loweredLhs, Equality, loweredRhs)))
            
          // x && y ---> when x then y else false
          case And =>
            val ternary = Ternary(loweredLhs, loweredRhs, BoolLit(false))
            ternary.setSmartCasts(binaryOp.getSmartCasts)
            lower(ternary)
          
          // x || y ---> when x then true else y
          case Or =>
            lower(Ternary(loweredLhs, BoolLit(true), loweredRhs))
          
          // nothing to lower at top-level, only perform recursive calls
          case _ => BinaryOp(loweredLhs, binaryOp.operator, loweredRhs)
        }
      }
      case select: Select => Select(lower(select.lhs), select.selected)

      // need to treat separately the case where one of the branches does not return (o.w. Java ASM crashes)
      case ternary@Ternary(cond, thenBr, elseBr) if thenBr.getType == NothingType || elseBr.getType == NothingType => {
        val valName = uniqueIdGenerator.next()
        if (thenBr.getType == NothingType){
          val ifStat = IfThenElse(cond, thenBr, None)
          ifStat.setSmartCasts(ternary.getSmartCasts)
          lower(Sequence(List(ifStat), elseBr))
        } else {
          val ifStat = IfThenElse(UnaryOp(ExclamationMark, cond).setType(BoolType), elseBr, None)
          lower(Sequence(List(ifStat), thenBr))
        }
      }
      case ternary@Ternary(cond, initThenBr, initElseBr) =>
        val loweredTernary = Ternary(lower(cond), lower(initThenBr), lower(initElseBr))
        loweredTernary.setSmartCasts(ternary.getSmartCasts)
        loweredTernary match {
          case Ternary(BoolLit(constCond), loweredThenBr, loweredElseBr) =>
            if constCond then loweredThenBr else loweredElseBr
          case Ternary(loweredCond, BoolLit(true), BoolLit(false)) => loweredCond
          case _ => loweredTernary
        }
      case Cast(expr, tpe) => Cast(lower(expr), tpe)
      case TypeTest(expr, tpe) => TypeTest(lower(expr), tpe)
      case Sequence(stats, expr) => Sequence(stats.map(lower), lower(expr))
    }
    lowered.setTypeOpt(expr.getTypeOpt)
  }

  private def lower(call: Call)(using LoweringContext): Call = propagatePosition(call.getPosition){
    val loweredReceiver =
      call.receiverOpt.map(lower)
        .getOrElse(MeRef().setTypeOpt(call.getMeTypeOpt))
    val loweredCall = Call(Some(loweredReceiver), call.function, call.args.map(lower), call.isTailrec)
    loweredCall.setResolvedSigOpt(call.getSignatureOpt)
    loweredCall.setTypeOpt(call.getTypeOpt)
    loweredCall
  }

  private def lower(statement: Statement)(using LoweringContext): Statement = propagatePosition(statement.getPosition) {
    // call appropriate method for each type of statement
    statement match
      case expr: Expr => lower(expr)
      case block: Block => lower(block)
      case localDef: LocalDef => lower(localDef)
      case varAssig: VarAssig => lower(varAssig)
      case varModif: VarModif => lower(varModif)
      case ifThenElse: IfThenElse => lower(ifThenElse)
      case whileLoop: WhileLoop => lower(whileLoop)
      case forLoop: ForLoop => lower(forLoop)
      case returnStat: ReturnStat => lower(returnStat)
      case panicStat: PanicStat => lower(panicStat)
  }

  private def lower(topLevelDef: TopLevelDef)(using LoweringContext): TopLevelDef = propagatePosition(topLevelDef.getPosition) {
    topLevelDef match
      case moduleDef: ModuleDef => lower(moduleDef)
      case packageDef: PackageDef => lower(packageDef)
      case structDef: StructDef => lower(structDef)
      case constDef: ConstDef => throw AssertionError("unexpected constant in lowering")
  }
  
  private def lower(tpe: TypeTree)(using LoweringContext): TypeTree = tpe match {
    case CapturingTypeTree(typeShapeTree, captureDescr) =>
      CapturingTypeTree(lower(typeShapeTree), lower(captureDescr))
    case shape: TypeShapeTree => lower(shape)
    case wrapperTypeTree: WrapperTypeTree => wrapperTypeTree
  }
  
  private def lower(shape: TypeShapeTree)(using LoweringContext): TypeShapeTree = shape match {
    case shape: CastTargetTypeShapeTree => shape
    case ArrayTypeShapeTree(elemType) =>
      ArrayTypeShapeTree(lower(elemType))
  }
  
  private def lower(captureSetTree: ExplicitCaptureSetTree)(using LoweringContext): ExplicitCaptureSetTree = propagatePosition(captureSetTree.getPosition) {
    val lowered = ExplicitCaptureSetTree(captureSetTree.capturedExpressions.map(lower))
    lowered.setResolvedDescrOpt(captureSetTree.getResolvedDescrOpt)
    lowered
  }

  private def lower(captureDescrTree: CaptureSetTree)(using LoweringContext): CaptureSetTree = propagatePosition(captureDescrTree.getPosition) {
    val loweredCapDescr = captureDescrTree match {
      case ExplicitCaptureSetTree(capturedExpressions) =>
        ExplicitCaptureSetTree(capturedExpressions.map(lower))
      case implicitRootCaptureSetTree: ImplicitRootCaptureSetTree => implicitRootCaptureSetTree
    }
    loweredCapDescr.setResolvedDescrOpt(captureDescrTree.getResolvedDescrOpt)
    loweredCapDescr
  }

  private def negatedBool(expr: Expr): Expr = UnaryOp(ExclamationMark, expr.setType(BoolType)).setType(BoolType)

  private def propagatePosition[A <: Ast](pos: Option[Position], maxDepth: Int = 2)(ast: A): A = {
    if (maxDepth > 0 && ast.getPosition.isEmpty){
      ast.setPosition(pos)
      for (child <- ast.children){
        propagatePosition(pos, maxDepth - 1)(child)
      }
    }
    ast
  }

}
