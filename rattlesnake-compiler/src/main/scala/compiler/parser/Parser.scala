package compiler.parser

import compiler.irs.Asts.*
import compiler.irs.Tokens.*
import compiler.parser.ParseTree.^:
import compiler.parser.TreeParsers.{opt, opt as :::, *}
import compiler.pipeline.CompilationStep.Parsing
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter}
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
  private val openParenth = op(OpeningParenthesis).ignored
  private val closeParenth = op(ClosingParenthesis).ignored
  private val openBrace = op(OpeningBrace).ignored
  private val closeBrace = op(ClosingBrace).ignored
  private val openBracket = op(OpeningBracket).ignored
  private val closeBracket = op(ClosingBracket).ignored
  private val comma = op(Comma).ignored
  private val dot = op(Dot).ignored
  private val colon = op(Colon).ignored
  private val maybeSemicolon = opt(op(Semicolon)).ignored
  private val -> = (op(Minus) ::: op(GreaterThan)).ignored
  private val apostrophe = op(Apostrophe)

  private val unaryOperator = op(Minus, ExclamationMark)
  private val assignmentOperator = op(PlusEq, MinusEq, TimesEq, DivEq, ModuloEq, Assig)

  private val semicolon = op(Semicolon).ignored

  // ---------- Syntax description -----------------------------------------------------------------------

  private lazy val source: FinalTreeParser[Source] = {
    repeat(topLevelDef ::: opt(op(Semicolon)).ignored) ::: endOfFile.ignored map (defs => Source(defs))
  } setName "source"

  private lazy val topLevelDef: P[TopLevelDef] = interfaceDef OR objectDef OR classDef OR datatypeDef OR structDef OR typeAliasDef

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
    kw(Object).ignored ::: highName
      ::: opt(openParenth ::: repeatWithSep(highName, comma) ::: closeParenth)
      ::: supertypesListOpt ::: methodsListOpt map {
      case objectName ^: importedPackagesOpt ^: supertypes ^: functions =>
        ObjectDef(objectName, importedPackagesOpt.getOrElse(Nil), functions, supertypes)
    }
  } setName "objectDef"

  private lazy val datatypeDef = {
    kw(Datatype).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt ::: supertypesListOpt map {
      case id ^: typeParams ^: supertypes => DataTypeDef(id, typeParams, supertypes)
    }
  } setName "datatypeDef"

  private lazy val structDef = {
    kw(Struct).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt ::: supertypesListOpt
      ::: opt(openBrace ::: repeatWithSep(structOrTypeAliasParam, comma) ::: closeBrace) map {
      case name ^: typeParams ^: supertypes ^: fieldsOpt =>
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
      ::: openParenth ::: repeatWithSep(funParamTree, comma) ::: closeParenth
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

  private lazy val funParamTree = funOrClassParam OR thisParam

  private lazy val funOrClassParam: P[FunctionParam & ClassParam] = recursive {
    opt(kw(Var)) ::: lowName ::: colon ::: typeTree map {
      case Some(_) ^: name ^: tpe => VarParam(name, tpe)
      case None ^: name ^: tpe => SimpleParam(name, tpe)
    }
  } setName "funOrClassParam"

  private lazy val thisParam: P[ThisParam] = {
    kw(This).ignored ::: opt(colon ::: typeTree) map {
      case tpeOpt => ThisParam(tpeOpt)
    }
  } setName "thisParam"

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

  private lazy val supertypesListOpt = {
    opt(colon ::: repeatWithSepNonZero(primOrNamedType, comma)) map {
      case None => List.empty
      case Some(allSupertypes) =>
        allSupertypes.flatMap {
          case primitiveTypeTree: PrimitiveTypeTree =>
            errorReporter.push(Err(Parsing, "subclassing a primitive type is forbidden", primitiveTypeTree.getPosition))
            None
          case namedTypeTree@NamedTypeTree(name, typeArgs, args) if args.nonEmpty =>
            errorReporter.push(Err(Parsing, "supertypes cannot take value arguments", namedTypeTree.getPosition))
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

  private lazy val explicitCaptureSetTree = recursive {
    openBrace ::: repeatWithSep(expr, comma) ::: closeBrace map {
      case expressions => ExplicitCaptureSetTree(expressions)
    }
  } setName "explicitCaptureSetTree"
  
  private lazy val typeArgsListOpt = opt(openBracket ::: repeatWithSep(typeTree, comma) ::: closeBracket)

  private lazy val primOrNamedType: AnyTreeParser[BaseTypeTree] = recursive {
    highName ::: opt(apostrophe) ::: typeArgsListOpt
      ::: opt(openParenth ::: repeatWithSepNonZero(expr, comma) ::: closeParenth) map {
      case baseTypeName ^: apostropheOpt ^: typeParamsOpt ^: paramsOpt =>
        val primTypeOpt = Types.primTypeFor(baseTypeName).map(PrimitiveTypeTree(_))
        if (primTypeOpt.isDefined && typeParamsOpt.exists(_.nonEmpty)) {
          errorReporter.push(Err(Parsing, "primitive types cannot take type parameters", typeParamsOpt.get.head.getPosition))
        }
        primTypeOpt.getOrElse(NamedTypeTree(baseTypeName, typeParamsOpt.getOrElse(Nil), paramsOpt.getOrElse(Nil)))
    }
  } setName "primOrNamedType"

  private lazy val block = recursive {
    openBrace ::: repeatWithEnd(stat, semicolon) ::: closeBrace map {
      stats => Block(stats)
    }
  } setName "block"

  private lazy val exprOrAssig = recursive {
    expr ::: opt(opt(colon ::: typeTree) ::: assignmentOperator ::: expr) map {
      case singleExpr ^: None => singleExpr
      case lhs ^: Some(optTypeAnnot ^: Assig ^: rhs) => VarAssig(lhs, optTypeAnnot, rhs)
      case lhs ^: Some(optTypeAnnot ^: op ^: rhs) => VarModif(lhs, optTypeAnnot, rhs, Operators.assigOperators.apply(op))
    }
  } setName "exprOrAssig"

  private lazy val assignmentStat = recursive {
    expr ::: opt(colon ::: typeTree) ::: assignmentOperator ::: expr map {
      case lhs ^: optTypeAnnot ^: Assig ^: rhs => VarAssig(lhs, optTypeAnnot, rhs)
      case lhs ^: optTypeAnnot ^: operator ^: rhs => VarModif(lhs, optTypeAnnot, rhs, Operators.assigOperators.apply(operator))
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
      ::: opt((kw(As) OR kw(Is)) ::: primOrNamedType
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
    opt(openBracket ::: repeatWithSepNonZero(highName, comma) ::: closeBracket) map (_.getOrElse(List.empty))
  } setName "typeParamsWithoutVarianceListOpt"

  private lazy val typeParamsPossiblyWithVarianceListOpt = recursive {
    opt(openBracket ::: repeatWithSepNonZero(typeParam, comma) ::: closeBracket) map (_.getOrElse(List.empty))
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

  private lazy val thisRef = kw(This) map (_ => ThisRef())

  private lazy val itRef = kw(It) map (_ => ItRef())

  private lazy val objectRef = highName map (ObjectRef(_))

  private lazy val varRefOrNonPrefixedCall = lowName ::: opt(opt(op(ExclamationMark)) ::: parenthArgsList) map {
    case name ^: Some(exclMarkOpt ^: args) => Call(None, name, args, exclMarkOpt.isDefined)
    case name ^: None => VariableRef(name)
  } setName "varRefOrNonPrefixedCall"

  private lazy val atomicExpr = recursive {
    varRefOrNonPrefixedCall OR thisRef OR itRef OR objectRef OR literalValue OR parenthesizedExpr
  } setName "atomicExpr"

  private lazy val selectOrIndexingChain = recursive {
    atomicExpr ::: repeat((dot ::: lowName ::: opt(opt(op(ExclamationMark)) ::: parenthArgsList))) map {
      case atExpr ^: repeated =>
        repeated.foldLeft(atExpr) {
          case (acc, name ^: Some(optExclMark ^: args)) => Call(Some(acc), name, args, optExclMark.isDefined)
          case (acc, name ^: None) => Select(acc, name)
        }
    }
  } setName "selectOrIndexingChain"

  private lazy val parenthesizedExpr = recursive {
    openParenth ::: expr ::: closeParenth
  } setName "parenthesizedExpr"

  private lazy val structOrModuleInstantiation = recursive {
    kw(New).ignored ::: highName ::: typeArgsListOpt ::: openParenth ::: repeatWithSep(fieldInitializer, comma) ::: closeParenth map {
      case tid ^: tArgs ^: initializers => StructOrClassInstantiation(tid, tArgs.getOrElse(List.empty), initializers)
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

  private lazy val panicStat = {
    kw(Panic).ignored ::: expr map PanicStat.apply
  } setName "panicStat"


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
