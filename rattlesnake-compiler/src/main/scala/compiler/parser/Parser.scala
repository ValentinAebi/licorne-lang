package compiler.parser

import compiler.identifiers.{NormalFunOrVarId, NormalTypeId}
import compiler.irs.Asts.*
import compiler.irs.Tokens.*
import compiler.parser.ParseTree.^:
import compiler.parser.TreeParsers.{opt, opt as :::, *}
import compiler.pipeline.CompilationStep.Parsing
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.lang.{Keyword, Operator, Operators, Purity, ReassigPermission, Types, Variance, Visibility}
import compiler.lang.Types.PrimitiveType.IntType
import compiler.lang.Operator.*
import compiler.lang.Keyword.*
import compiler.lang.Types.PrimitiveType

import scala.compiletime.uninitialized

final class Parser(errorReporter: ErrorReporter) extends CompilerStep[(List[PositionedToken], String), Source] {
  private implicit val implErrorReporter: ErrorReporter = errorReporter
  private var ll1Iterator: LL1Iterator = uninitialized

  private type P[X] = AnyTreeParser[X]

  // ---------- Syntax primitives -----------------------------------------------------------------------

  private def op(operators: Operator*) = treeParser(operators.mkString(" or ")) {
    case OperatorToken(operator) if operators.contains(operator) => operator
  }

  private def kw(keywords: Keyword*) = treeParser(keywords.mkString(" or ")) {
    case KeywordToken(keyword) if keywords.contains(keyword) => keyword
  }

  private val lowName = treeParser("a..z") {
    case FirstLowercaseIdentifierToken(strValue) => NormalFunOrVarId(strValue)
  }

  private val highName = treeParser("A..Z") {
    case FirstUppercaseIdentifierToken(strValue) => NormalTypeId(strValue)
  }

  private val numericLiteralValue: FinalTreeParser[NumericLiteral] = treeParser("int or double") {
    case IntLitToken(value) => IntLit(value)
    case DoubleLitToken(value) => DoubleLit(value)
  }

  private val nonNumericLiteralValue: FinalTreeParser[NonNumericLiteral] = treeParser("bool or char or string") {
    case UnitLitToken => UnitLit()
    case BoolLitToken(value) => BoolLit(value)
    case CharLitToken(value) => CharLit(value)
    case StringLitToken(value) => StringLit(value)
  }

  private val literalValue: FinalTreeParser[Literal] = {
    numericLiteralValue OR nonNumericLiteralValue
  } setName "literalValue"

  private val endOfFile = treeParser("end of file") {
    case EndOfFileToken => ()
  }

  private val assig = op(Assig).ignored
  private val openParenth = op(OpeningParenthesis).ignored
  private val closeParenth = op(ClosingParenthesis).ignored
  private val openBrace = op(OpeningBrace).ignored
  private val closeBrace = op(ClosingBrace).ignored
  private val openBracket = op(OpeningBracket).ignored
  private val closeBracket = op(ClosingBracket).ignored
  private val comma = op(Comma).ignored
  private val dot = op(Dot).ignored
  private val colon = op(Colon).ignored
  private val semicolon = op(Semicolon).ignored
  private val maybeSemicolon = opt(op(Semicolon)).ignored
  private val -> = (op(Minus) ::: op(GreaterThan)).ignored

  private val unaryOperator = op(Minus, ExclamationMark)
  private val assignmentOperator = op(PlusEq, MinusEq, TimesEq, DivEq, ModuloEq, Assig)

  // ---------- Syntax description -----------------------------------------------------------------------

  private lazy val source: FinalTreeParser[Source] = {
    repeat(topLevelDef ::: opt(op(Semicolon)).ignored) ::: endOfFile.ignored map (defs => Source(defs))
  } setName "source"

  private lazy val topLevelDef: P[TopLevelDef] = interfaceDef OR objectDef OR classDef OR datatypeDef OR recordDef OR typeAliasDef

  private lazy val interfaceDef: P[InterfaceDef] = {
    kw(Interface).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt ::: supertypesListOpt ::: methodsListOpt map {
      case id ^: typeParams ^: supertypes ^: functions =>
        InterfaceDef(id, typeParams, functions, supertypes)
    }
  } setName "interfaceDef"

  private lazy val classDef: P[ClassDef] = {
    kw(Class).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(classParamTree, comma) ::: closeParenth)
      ::: supertypesListOpt ::: methodsListOpt map {
      case moduleName ^: typeParams ^: paramsOpt ^: supertypes ^: functions =>
        ClassDef(moduleName, typeParams, paramsOpt.getOrElse(Nil), functions, supertypes)
    }
  } setName "classDef"

  private lazy val objectDef: P[ObjectDef] = {
    kw(Object).ignored ::: highName ::: supertypesListOpt ::: methodsListOpt map {
      case objectName ^: supertypes ^: functions =>
        ObjectDef(objectName, functions, supertypes)
    }
  } setName "objectDef"

  private lazy val datatypeDef = {
    kw(Datatype).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt ::: supertypesListOpt map {
      case id ^: typeParams ^: supertypes => DataTypeDef(id, typeParams, supertypes)
    }
  } setName "datatypeDef"

  private lazy val recordDef = {
    kw(Record).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(recordOrTypeAliasParam, comma) ::: closeParenth) ::: supertypesListOpt map {
      case name ^: typeParams ^: fieldsOpt ^: supertypes =>
        RecordDef(name, typeParams, fieldsOpt.getOrElse(Nil), supertypes)
    }
  } setName "recordDef"

  private lazy val typeAliasDef: P[TypeAliasDef] = {
    kw(Typealias).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(recordOrTypeAliasParam, comma) ::: closeParenth)
      ::: assig ::: typeTree map {
      case typeName ^: typeParams ^: paramsOpt ^: rhs => TypeAliasDef(typeName, typeParams, paramsOpt.getOrElse(List.empty), rhs)
    }
  } setName "typeAliasDef"

  private lazy val funDef = {

    def isUnitType(typeTree: TypeTree): Boolean = typeTree match {
      case PrimitiveTypeTree(PrimitiveType.UnitType) => true
      case _ => false
    }

    opt(kw(Pure)) ::: opt(kw(Main, Private)) ::: kw(Fn).ignored ::: lowName ::: typeParamsWithoutVarianceListOpt
      ::: openParenth ::: repeatWithSep(funParamTree, comma) ::: opt(op(VerticalBar).ignored ::: expr) ::: closeParenth
      ::: opt(-> ::: typeTree) ::: opt(block OR assig ::: expr) map {
      case optPure ^: optModif ^: funName ^: typeParams ^: params ^: optPrecond ^: optRetType ^: bodyOptRaw =>
        val bodyOptDesugared = bodyOptRaw.map {
          case expr: Expr => Block(List(
            ReturnStat(Some(expr)).withDesugaringSource(expr)
          )).withDesugaringSource(expr)
          case block: Block => block
        }
        if (bodyOptRaw.exists(_.isInstanceOf[Expr]) && optRetType.forall(isUnitType)) {
          errorReporter.report(Err(Parsing, s"single-expression methods are not allowed to return ${PrimitiveType.UnitType}", bodyOptRaw.get.getPosition))
        }
        FunDef(funName, typeParams, params, optRetType, optPrecond, bodyOptDesugared,
          visibility = if optModif.contains(Keyword.Private) then Visibility.Private else Visibility.Public,
          purity = if optPure.isDefined then Purity.Pure else Purity.PossiblyImpure,
          isMain = optModif.contains(Main)
        )
    }
  } setName "funDef"

  private lazy val funParamTree = funOrClassParamTree OR thisParam
  
  private lazy val classParamTree = funOrClassParamTree OR publicParam

  private lazy val funOrClassParamTree: P[FunctionParam & ClassParam] = recursive {
    opt(kw(Var)) ::: lowName ::: colon ::: typeTree map {
      case Some(_) ^: name ^: tpe => VarParam(name, tpe)
      case None ^: name ^: tpe => SimpleParam(name, tpe)
    }
  } setName "funOrClassParamTree"

  private lazy val thisParam: P[ThisParam] = {
    kw(This).ignored ::: opt(colon ::: typeTree) map {
      case tpeOpt => ThisParam(tpeOpt)
    }
  } setName "thisParam"
  
  private lazy val publicParam: P[PublicParam] = {
    kw(Public).ignored ::: lowName ::: colon ::: typeTree map {
      case id ^: tpe => PublicParam(id, tpe)
    }
  } setName "publicParam"

  private lazy val recordOrTypeAliasParam: P[RecordParam & TypeAliasParam] = recursive {
    lowName ::: colon ::: typeTree map {
      case name ^: tpe => SimpleParam(name, tpe)
    }
  } setName "recordOrTypeAliasParam"

  private lazy val methodsListOpt = {
    opt(openBrace ::: repeat(funDef ::: maybeSemicolon) ::: closeBrace) map {
      case None => List.empty
      case Some(methods) => methods
    }
  } setName "methodsListOpt"

  private lazy val supertypesListOpt = {
    opt(colon ::: repeatWithSepNonZero(nominalTypeTree, comma)) map {
      case None => List.empty
      case Some(allSupertypes) =>
        allSupertypes.flatMap {
          case primitiveTypeTree: PrimitiveTypeTree =>
            errorReporter.report(Err(Parsing, "subclassing a primitive type is forbidden", primitiveTypeTree.getPosition))
            None
          case namedTypeTree@NamedTypeTree(name, typeArgs, args) if args.nonEmpty =>
            errorReporter.report(Err(Parsing, "supertypes cannot take value arguments", namedTypeTree.getPosition))
            None
          case namedTypeTree: NamedTypeTree => Some(namedTypeTree)
        }
    }
  } setName "supertypesListOpt"

  private lazy val possiblyNegativeNumericLiteralValue: FinalTreeParser[NumericLiteral] = {
    (numericLiteralValue OR (op(Minus) ::: numericLiteralValue)) map {
      case _ ^: IntLit(value) => IntLit(-value)
      case _ ^: DoubleLit(value) => DoubleLit(-value)
      case lit: NumericLiteral => lit
    }
  } setName "possiblyNegativeNumericLiteralValue"

  private lazy val constExprLiteralValue = {
    possiblyNegativeNumericLiteralValue OR nonNumericLiteralValue
  } setName "constExprLiteralValue"

  private lazy val closureType = kw(Fn).ignored ::: openParenth ::: repeatWithSep(typeTree, comma) ::: closeParenth ::: -> ::: typeTree map {
    case paramTypes ^: resultType => ClosureTypeTree(paramTypes, resultType)
  } setName "closureType"

  private lazy val intRangeType = openBracket ::: opt(expr) ::: comma ::: opt(expr) ::: op(ClosingBracket).ignored map {
    case lowOpt ^: highOpt => IntRangeTypeTree(lowOpt, highOpt)
  } setName "intRangeType"

  private lazy val typeTree: P[TypeTree] = recursive {
    nominalTypeTree OR closureType OR intRangeType OR (openParenth ::: typeTree ::: closeParenth)
  } setName "typeTree"

  private lazy val typeArgsListOpt = opt(openBracket ::: repeatWithSep(typeTree, comma) ::: closeBracket)

  private lazy val nominalTypeTree: P[NominalTypeTree] = recursive {
    highName ::: typeArgsListOpt ::: opt(openParenth ::: repeatWithSepNonZero(expr, comma) ::: closeParenth) map {
      case baseTypeName ^: typeArgsOpt ^: paramsOpt =>
        val primTypeOpt = Types.primTypeFor(baseTypeName).map(PrimitiveTypeTree(_))
        if (primTypeOpt.isDefined && typeArgsOpt.exists(_.nonEmpty)) {
          errorReporter.report(Err(Parsing, "primitive types cannot take type parameters", typeArgsOpt.get.head.getPosition))
        }
        primTypeOpt.getOrElse(NamedTypeTree(baseTypeName, typeArgsOpt.getOrElse(Nil), paramsOpt.getOrElse(Nil)))
    }
  } setName "refinableTypeTree"

  private lazy val block: P[Block] = recursive {
    openBrace ::: repeatWithEnd(stat, semicolon) ::: closeBrace map {
      stats => Block(stats)
    }
  } setName "block"

  private lazy val exprOrAssig = recursive {
    expr ::: opt(assignmentOperator ::: expr) map {
      case singleExpr ^: None => singleExpr
      case lhs ^: Some(Assig ^: rhs) => VarAssig(lhs, rhs)
      case lhs ^: Some(op ^: rhs) => VarModif(lhs, rhs, Operators.assigOperators.apply(op))
    }
  } setName "exprOrAssig"

  private lazy val assignmentStat = recursive {
    expr ::: assignmentOperator ::: expr map {
      case lhs ^: Assig ^: rhs => VarAssig(lhs, rhs)
      case lhs ^: operator ^: rhs => VarModif(lhs, rhs, Operators.assigOperators.apply(operator))
    }
  } setName "assignmentStat"

  private lazy val expr: P[Expr] = recursive {
    simpleExpr OR ternary OR closure
  } setName "expr"

  private lazy val simpleExpr: P[Expr] = recursive {
    BinaryOperatorsParser.buildFrom(Operator.operatorsByPriorityDecreasing, binopArg)
  } setName "simpleExpr"

  private lazy val noBinopExpr = recursive {
    opt(unaryOperator) ::: selectOrIndexingChain map {
      case Some(Minus) ^: IntLit(value) => IntLit(-value)
      case Some(Minus) ^: DoubleLit(value) => DoubleLit(-value)
      case Some(unOp) ^: operand => UnaryOp(unOp, operand)
      case None ^: simpleExpr => simpleExpr
    }
  } setName "noBinopExpr"

  private lazy val binopArg = recursive {
    ((noBinopExpr OR recordOrModuleInstantiation OR panicExpr) ::: opt((kw(As) OR kw(Is)) ::: typeTree)) map {
      case expression ^: None => expression
      case expression ^: Some(As ^: tp) => Cast(expression, tp)
      case expression ^: Some(Is ^: tp) => TypeTest(expression, tp)
      case _ => assert(false)
    }
  } setName "binopArg"

  private lazy val parenthArgsList = recursive {
    openParenth ::: repeatWithSep(expr, comma) ::: closeParenth
  } setName "parenthArgsList"

  private lazy val typeParamsWithoutVarianceListOpt = {
    opt(openBracket ::: repeatWithSepNonZero(typeParamWithoutVariance, comma) ::: closeBracket) map (_.getOrElse(List.empty))
  } setName "typeParamsWithoutVarianceListOpt"

  // TODO allow union and intersection types as bounds?
  private lazy val typeParamWithoutVariance = highName ::: opt(kw(Sub).ignored ::: typeTree) ::: opt(kw(Super).ignored ::: typeTree) map {
    case id ^: upperBoundOpt ^: lowerBoundOpt =>
      TypeParamWithoutVariance(id, upperBoundOpt, lowerBoundOpt)
  } setName "typeParamWithoutVariance"

  private lazy val typeParamsPossiblyWithVarianceListOpt = {
    opt(openBracket ::: repeatWithSepNonZero(typeParamPossiblyWithVariance, comma) ::: closeBracket) map (_.getOrElse(List.empty))
  } setName "typeParamsPossiblyWithVarianceListOpt"

  private lazy val typeParamPossiblyWithVariance = opt(op(Plus, Minus)) ::: highName ::: opt(kw(Sub).ignored ::: typeTree) ::: opt(kw(Super).ignored ::: typeTree) map {
    case varianceSymbolOpt ^: typeParamName ^: upperBoundOpt ^: lowerBoundOpt =>
      val variance = varianceSymbolOpt match {
        case Some(Plus) => Variance.Covariant
        case Some(Minus) => Variance.Contravariant
        case Some(_) => assert(false)
        case None => Variance.Invariant
      }
      TypeParamWithVariance(typeParamName, variance, upperBoundOpt, lowerBoundOpt)
  } setName "typeParamPossiblyWithVariance"

  private lazy val thisRef = kw(This) map (_ => ThisRef())

  private lazy val itRef = kw(It) map (_ => ItRef())

  private lazy val objectRef = highName map (ObjectRef(_))

  private lazy val varRef = lowName map (name => VariableRef(name)) setName "varRef"

  private lazy val atomicExpr: P[Expr] = recursive {
    varRef OR thisRef OR itRef OR objectRef OR literalValue OR parenthesizedExpr
  } setName "atomicExpr"

  private lazy val selectOrIndexingChain = recursive {
    atomicExpr ::: repeat(dot ::: lowName) ::: opt(typeArgsListOpt ::: parenthArgsList) ::: opt(colon ::: typeTree) map {
      case atExpr ^: selects ^: argsListOpt ^: typeAnnotOpt =>
        val afterSelectsFolding = selects.foldLeft(atExpr)(Select(_, _))
        val afterArgsAddition = argsListOpt match {
          case Some(typeArgsOpt ^: args) =>
            Call(afterSelectsFolding, typeArgsOpt.getOrElse(List.empty), args)
          case None => afterSelectsFolding
        }
        typeAnnotOpt match {
          case Some(tpe) => TypeAscription(afterArgsAddition, tpe)
          case None => afterArgsAddition
        }
    }
  } setName "selectOrIndexingChain"

  private lazy val closure = recursive {
    kw(Fn).ignored ::: openParenth ::: repeatWithSep(lowName ::: opt(colon ::: typeTree), comma) ::: closeParenth ::: -> ::: (expr OR block) map {
      case params ^: (body: Block) =>
        ClosureDef(params.toPairs, body)
      case params ^: (expr: Expr) =>
        ClosureDef(params.toPairs, Block(List(ReturnStat(Some(expr)))))
    }
  } setName "closure"

  private lazy val parenthesizedExpr = recursive {
    openParenth ::: expr ::: closeParenth
  } setName "parenthesizedExpr"

  private lazy val recordOrModuleInstantiation = recursive {
    kw(New).ignored ::: highName ::: typeArgsListOpt ::: openParenth ::: repeatWithSep(fieldInitializer, comma) ::: closeParenth map {
      case tid ^: tArgs ^: initializers => RecordOrClassInstantiation(tid, tArgs.getOrElse(List.empty), initializers)
    }
  } setName "recordOrModuleInstantiation"

  private lazy val fieldInitializer = recursive {
    lowName ::: opt(assig ::: expr) map {
      case fieldName ^: Some(rhs) => FullFieldInitializer(fieldName, rhs)
      case fieldName ^: None => ShorthandFieldInitializer(fieldName)
    }
  } setName "fieldInitializer"

  private lazy val stat: P[Statement] = {
    exprOrAssig OR valDef OR varDef OR whileLoop OR forLoop OR ifThenElse OR returnStat
  } setName "stat"

  private lazy val valDef = {
    kw(Val).ignored ::: lowName ::: opt(colon ::: typeTree) ::: opt(assig ::: expr) map {
      case valName ^: optType ^: rhsOpt => LocalDef(valName, optType, rhsOpt, ReassigPermission.Val)
    }
  } setName "valDef"

  private lazy val varDef = {
    kw(Var).ignored ::: lowName ::: opt(colon ::: typeTree) ::: opt(assig ::: expr) map {
      case varName ^: optType ^: rhsOpt => LocalDef(varName, optType, rhsOpt, ReassigPermission.Var)
    }
  } setName "varDef"

  private lazy val whileLoop = recursive {
    kw(While).ignored ::: expr ::: block map {
      case cond ^: body => WhileLoop(cond, body)
    }
  } setName "whileLoop"

  private lazy val forLoop = recursive {
    kw(For).ignored ::: repeatWithSep(valDef OR varDef OR assignmentStat, comma) ::: semicolon
      ::: expr ::: semicolon ::: repeatWithSep(assignmentStat, comma) ::: block map {
      case initStats ^: cond ^: stepStats ^: body => ForLoop(initStats, cond, stepStats, body)
    }
  } setName "forLoop"

  private lazy val ifThenElse: P[IfThenElse] = recursive {
    kw(If).ignored ::: expr ::: block ::: opt(kw(Else).ignored ::: (ifThenElse OR block)) map {
      case cond ^: thenBr ^: optElse => IfThenElse(cond, thenBr, optElse)
    }
  } setName "ifThenElse"

  private lazy val ternary = recursive {
    kw(When).ignored ::: expr ::: kw(Then).ignored ::: expr ::: kw(Else).ignored ::: expr map {
      case cond ^: thenBr ^: elseBr => Ternary(cond, thenBr, elseBr)
    }
  } setName "ternary"

  private lazy val returnStat = {
    kw(Return).ignored ::: opt(expr) map (optRetVal => ReturnStat(optRetVal))
  } setName "returnStat"

  private lazy val panicExpr = {
    kw(Panic).ignored ::: expr map PanicExpr.apply
  } setName "panicExpr"

  extension [L, R](params: List[L ^: R]) private def toPairs: List[(L, R)] = {
    params.map { case id ^: tpe => (id, tpe) }
  }


  override def apply(input: (List[PositionedToken], String)): Source = {
    val (positionedTokens, srcName) = input
    if (positionedTokens.isEmpty) {
      Source(List.empty)
    } else {
      ll1Iterator = LL1Iterator.from(positionedTokens)
      source.extract(ll1Iterator) match {
        case Some(source) =>
          errorReporter.displayAndTerminateIfErrors()
          source.setName(srcName)
        case None => errorReporter.displayErrorsAndTerminate()
      }
    }
  }

}
