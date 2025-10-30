package compiler.parser

import compiler.irs.Asts.*
import compiler.irs.Tokens.*
import compiler.parser.ParseTree.^:
import compiler.parser.TreeParsers.{opt, opt as :::, *}
import compiler.pipeline.CompilationStep.Parsing
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter, Fatal}
import compiler.reporting.{Errors, Position}
import identifiers.*
import lang.*
import lang.Keyword.*
import lang.Operator.*

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
  private val doubleEqual = op(Equality).ignored
  private val openParenth = op(OpeningParenthesis).ignored
  private val closeParenth = op(ClosingParenthesis).ignored
  private val openBrace = op(OpeningBrace).ignored
  private val closeBrace = op(ClosingBrace).ignored
  private val openBracket = op(OpeningBracket).ignored
  private val closeBracket = op(ClosingBracket).ignored
  private val openChevron = op(LessThan).ignored
  private val closeChevron = op(GreaterThan).ignored
  private val comma = op(Comma).ignored
  private val dot = op(Dot).ignored
  private val colon = op(Colon).ignored
  private val doubleColon = colon ::: colon
  private val maybeSemicolon = opt(op(Semicolon)).ignored
  private val -> = (op(Minus) ::: op(GreaterThan)).ignored
  private val `=>` = (op(Assig) ::: op(GreaterThan)).ignored
  private val lessThan = op(LessThan).ignored
  private val greaterThan = op(GreaterThan).ignored
  private val at = op(At).ignored

  private val unaryOperator = op(Minus, ExclamationMark, Len)
  private val assignmentOperator = op(PlusEq, MinusEq, TimesEq, DivEq, ModuloEq, Assig)

  private val semicolon = op(Semicolon).ignored

  // ---------- Syntax description -----------------------------------------------------------------------

  private lazy val source: FinalTreeParser[Source] = {
    repeat(topLevelDef ::: opt(op(Semicolon)).ignored) ::: endOfFile.ignored map (defs => Source(defs))
  } setName "source"

  private lazy val topLevelDef: P[TopLevelDef] = interfaceDef OR objectDef OR classDef OR datatypeDef OR structDef OR typeAliasDef

  private lazy val interfaceDef: P[InterfaceDef] = {
    kw(Interface).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt ::: complexSuperTypesListOpt ::: methodsListOpt map {
      case id ^: typeParams ^: supertypes ^: functions =>
        InterfaceDef(id, typeParams, functions, supertypes)
    }
  } setName "interfaceDef"

  private lazy val classDef: P[ClassDef] = {
    kw(Class).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(classParamTree, comma) ::: closeParenth)
      ::: complexSuperTypesListOpt ::: methodsListOpt map {
      case moduleName ^: typeParams ^: paramsOpt ^: supertypes ^: functions =>
        ClassDef(moduleName, typeParams, paramsOpt.getOrElse(Nil), functions, supertypes)
    }
  } setName "classDef"

  private lazy val objectDef: P[ObjectDef] = {
    kw(Object).ignored ::: highName
      ::: opt(openParenth ::: repeatWithSep(highName, comma) ::: closeParenth)
      ::: complexSuperTypesListOpt ::: methodsListOpt map {
      case objectName ^: importedPackagesOpt ^: supertypes ^: functions =>
        ObjectDef(objectName, importedPackagesOpt.getOrElse(Nil), functions, supertypes)
    }
  } setName "objectDef"

  private lazy val datatypeDef = {
    kw(Datatype).ignored ::: highName ::: simpleSuperTypesListOpt ::: typeParamsPossiblyWithVarianceListOpt map {
      case id ^: supertypes ^: typeParams => DatatypeDef(id, typeParams, supertypes)
    }
  } setName "datatypeDef"

  private lazy val structDef = {
    kw(Struct).ignored ::: highName ::: simpleSuperTypesListOpt ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openBrace ::: repeatWithSep(structOrTypeAliasParam, comma) ::: closeBrace) map {
      case name ^: supertypes ^: typeParams ^: fieldsOpt =>
        StructDef(name, typeParams, fieldsOpt.getOrElse(Nil), supertypes)
    }
  } setName "structDef"

  private lazy val typeAliasDef: P[TypeAliasDef] = {
    kw(Typealias).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(structOrTypeAliasParam, comma) ::: closeParenth)
      ::: assig ::: typeTree map {
      case typeName ^: typeParams ^: paramsOpt ^: rhs => TypeAliasDef(typeName, typeParams, paramsOpt.getOrElse(List.empty), rhs)
    }
  } setName "typeAliasDef"

  private lazy val funDef = {
    opt(kw(Main, Private)) ::: kw(Fn).ignored ::: lowName ::: typeParamsWithoutVarianceListOpt
      ::: openParenth ::: repeatWithSep(funOrClassParam, comma) ::: closeParenth
      ::: opt(-> ::: typeTree) ::: opt(block) map {
      case optModif ^: funName ^: typeParams ^: params ^: optRetType ^: bodyOpt =>
        FunDef(funName, typeParams, params, optRetType, bodyOpt,
          visibility = if optModif.contains(Keyword.Private) then Visibility.Private else Visibility.Public,
          isMain = optModif.contains(Main)
        )
    }
  } setName "funDef"

  private lazy val packageImport = {
    kw(Object).ignored ::: highName map (ObjectImport(_))
  } setName "packageImport"

  private lazy val classParamTree = funOrClassParam OR packageImport

  private lazy val funOrClassParam: P[FunctionParam & ClassParam] = recursive {
    opt(kw(Var)) ::: lowName ::: colon ::: typeTree map {
      case Some(_) ^: name ^: tpe => VarParam(name, tpe)
      case None ^: name ^: tpe => SimpleParam(name, tpe)
    }
  } setName "funOrClassParam"

  private lazy val structOrTypeAliasParam: P[StructParam & TypeAliasParam] = recursive {
    lowName ::: colon ::: typeTree map {
      case name ^: tpe => SimpleParam(name, tpe)
    }
  } setName "structOrTypeAliasParam"

  private lazy val methodsListOpt = {
    opt(openBrace ::: repeat(funDef ::: maybeSemicolon) ::: closeBrace) map {
      case None => List.empty
      case Some(methods) => methods
    }
  } setName "methodsListOpt"

  private lazy val complexSuperTypesListOpt = {
    opt(colon ::: repeatWithSepNonZero(primOrNamedShape, comma)) map {
      case None => List.empty
      case Some(supertypes) => supertypes
    }
  } setName "complexSuperTypesListOpt"
  
  private lazy val simpleSuperTypesListOpt = {
    opt(colon ::: repeatWithSepNonZero(highName, comma)) map {
      case None => List.empty
      case Some(supertypes) => supertypes
    }
  } setName "simpleSuperTypesListOpt"

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

  private lazy val noParenthType = recursive {
    primOrNamedType ::: opt(kw(With).ignored ::: expr) map {
      case baseType ^: predicateOpt => predicateOpt match {
        case Some(predicate) => RefinedTypeTree(baseType, predicate)
        case None => baseType
      }
    }
  } setName "noParenthType"

  private lazy val typeTree: P[TypeTree] = recursive {
    noParenthType OR (openParenth ::: typeTree ::: closeParenth)
  } setName "typeTree"

  private lazy val varRef = lowName map (VariableRef(_))

  private lazy val path = recursive {
    (thisRef OR varRef) ::: repeat(dot ::: lowName) map {
      case root ^: selects => selects.foldLeft[Expr](root)(Select(_, _))
    }
  } setName "path"

  private lazy val capturableExpr = recursive {
    objectRef OR path
  } setName "capturableExpr"

  private lazy val hatAndImplicitRootCap = recursive {
    op(Hat) map (_ => ImplicitRootCaptureSetTree())
  } setName "hatAndImplicitRootCap"

  private lazy val explicitCaptureSetTree = recursive {
    openBrace ::: repeatWithSep(expr, comma) ::: closeBrace map {
      case expressions => ExplicitCaptureSetTree(expressions)
    }
  } setName "explicitCaptureSetTree"

  private lazy val hatAndExplicitCaptureSetTree = recursive {
    op(HatOpenBrace) ::: repeatWithSep(expr, comma) ::: closeBrace map {
      case _ ^: expressions => ExplicitCaptureSetTree(expressions)
    }
  } setName "hatAndExplicitCaptureSetTree"

  private lazy val hatAndCaptureDescr: P[CaptureSetTree] = recursive {
    hatAndImplicitRootCap OR hatAndExplicitCaptureSetTree
  } setName "hatAndCaptureDescr"

  private lazy val primOrNamedShape: AnyTreeParser[TypeShapeTree] = recursive {
    highName ::: opt(openChevron ::: repeatWithSep(typeTree, comma) ::: closeChevron)
      ::: opt(openParenth ::: repeatWithSepNonZero(expr, comma) ::: closeParenth) map {
      case baseTypeName ^: typeParamsOpt ^: paramsOpt =>
        val primTypeOpt = Types.primTypeFor(baseTypeName).map(PrimitiveTypeShapeTree(_))
        if (primTypeOpt.isDefined && typeParamsOpt.exists(_.nonEmpty)) {
          errorReporter.push(Err(Parsing, "primitive types cannot take type parameters", typeParamsOpt.get.head.getPosition))
        }
        primTypeOpt.getOrElse(NamedTypeShapeTree(baseTypeName, typeParamsOpt.getOrElse(Nil), paramsOpt.getOrElse(Nil)))
    }
  } setName "primOrNamedShape"

  private lazy val primOrNamedType = primOrNamedShape ::: opt(hatAndCaptureDescr) map {
    case shape ^: cdOpt => shape ^ cdOpt
  } setName "primOrNamedType"

  private lazy val block = recursive {
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
    noTernaryExpr OR ternary
  } setName "expr"

  private lazy val noTernaryExpr: P[Expr] = recursive {
    BinaryOperatorsParser.buildFrom(Operator.operatorsByPriorityDecreasing, binopArg)
  } setName "noTernaryExpr"

  private lazy val noBinopExpr = recursive {
    opt(unaryOperator) ::: selectOrIndexingChain map {
      case Some(Minus) ^: IntLit(value) => IntLit(-value)
      case Some(Minus) ^: DoubleLit(value) => DoubleLit(-value)
      case Some(unOp) ^: operand => UnaryOp(unOp, operand)
      case None ^: simpleExpr => simpleExpr
    }
  } setName "noBinopExpr"

  private lazy val binopArg = recursive {
    (noBinopExpr OR structOrModuleInstantiation)
      ::: opt((kw(As) OR kw(Is)) ::: primOrNamedShape
    ) map {
      case expression ^: None => expression
      case expression ^: Some(As ^: tp) => Cast(expression, tp)
      case expression ^: Some(Is ^: tp) => TypeTest(expression, tp)
      case _ => assert(false)
    }
  } setName "binopArg"

  private lazy val parenthArgsList = recursive {
    openParenth ::: repeatWithSep(expr, comma) ::: closeParenth
  } setName "parenthArgsList"

  private lazy val typeParamsWithoutVarianceListOpt = recursive {
    opt(openChevron ::: repeatWithSepNonZero(highName, comma) ::: closeChevron) map (_.getOrElse(List.empty))
  } setName "typeParamsWithoutVarianceListOpt"

  private lazy val typeParamsPossiblyWithVarianceListOpt = recursive {
    opt(openChevron ::: repeatWithSepNonZero(typeParam, comma) ::: closeChevron) map (_.getOrElse(List.empty))
  } setName "typeParamsPossiblyWithVarianceListOpt"

  private lazy val typeParam = opt(op(Plus, Minus)) ::: highName map {
    case varianceSymbolOpt ^: typeParamName => TypeParam(typeParamName,
      varianceSymbolOpt match {
        case Some(Plus) => Variance.Covariant
        case Some(Minus) => Variance.Contravariant
        case Some(_) => assert(false)
        case None => Variance.Invariant
      })
  } setName "typeParam"

  private lazy val indexing = recursive {
    openBracket ::: expr ::: closeBracket
  } setName "indexing"

  private lazy val thisRef = kw(This) map (_ => ThisRef())

  private lazy val objectRef = highName map (ObjectRef(_))

  private lazy val varRefOrNonPrefixedCall = lowName ::: opt(opt(op(ExclamationMark)) ::: parenthArgsList) map {
    case name ^: Some(exclMarkOpt ^: args) => Call(None, name, args, exclMarkOpt.isDefined)
    case name ^: None => VariableRef(name)
  } setName "varRefOrNonPrefixedCall"

  private lazy val atomicExpr = recursive {
    varRefOrNonPrefixedCall OR thisRef OR objectRef OR literalValue OR filledArrayInit OR parenthesizedExpr
  } setName "atomicExpr"

  private lazy val selectOrIndexingChain = recursive {
    atomicExpr ::: repeat((dot ::: lowName ::: opt(opt(op(ExclamationMark)) ::: parenthArgsList)) OR indexing) map {
      case atExpr ^: repeated =>
        repeated.foldLeft(atExpr) {
          case (acc, name ^: Some(optExclMark ^: args)) => Call(Some(acc), name, args, optExclMark.isDefined)
          case (acc, name ^: None) => Select(acc, name)
          case (acc, index: Expr) => Indexing(acc, index)
        }
    }
  } setName "selectOrIndexingChain"

  private lazy val parenthesizedExpr = recursive {
    openParenth ::: expr ::: closeParenth
  } setName "parenthesizedExpr"

  private lazy val filledArrayInit = recursive {
    openBracket ::: repeatWithSep(expr, comma) ::: closeBracket map (FilledArrayInit(_))
  } setName "filledArrayInit"

  private lazy val structOrModuleInstantiation = recursive {
    kw(New).ignored ::: highName ::: openBrace ::: repeatWithSep(fieldInitializer, comma) ::: closeBrace map {
      case tid ^: initializers => StructOrClassInstantiation(tid, initializers)
    }
  } setName "structOrModuleInstantiation"
  
  private lazy val fieldInitializer = recursive {
    lowName ::: opt(assig ::: expr) map {
      case fieldName ^: Some(rhs) => FullFieldInitializer(fieldName, rhs)
      case fieldName ^: None => ShorthandFieldInitializer(fieldName)
    }
  } setName "fieldInitializer"

  private lazy val stat: P[Statement] = {
    exprOrAssig OR valDef OR varDef OR whileLoop OR forLoop OR ifThenElse OR
      returnStat OR panicStat
  } setName "stat"

  private lazy val valDef = {
    kw(Val).ignored ::: lowName ::: opt(colon ::: typeTree) ::: opt(assig ::: expr) map {
      case valName ^: optType ^: rhsOpt => LocalDef(valName, optType, rhsOpt, isReassignable = false)
    }
  } setName "valDef"

  private lazy val varDef = {
    kw(Var).ignored ::: lowName ::: opt(colon ::: typeTree) ::: opt(assig ::: expr) map {
      case varName ^: optType ^: rhsOpt => LocalDef(varName, optType, rhsOpt, isReassignable = true)
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

  private lazy val panicStat = {
    kw(Panic).ignored ::: expr map PanicStat.apply
  } setName "panicStat"


  override def apply(input: (List[PositionedToken], String)): Source = {
    val (positionedTokens, srcName) = input
    if (positionedTokens.isEmpty) {
      errorReporter.pushFatal(Fatal(Parsing, "empty source", Some(Position(srcName, 1, 1))))
    } else {
      ll1Iterator = LL1Iterator.from(positionedTokens)
      source.extract(ll1Iterator) match {
        case Some(source) => source.setName(srcName)
        case None => errorReporter.displayErrorsAndTerminate()
      }
    }
  }

}
