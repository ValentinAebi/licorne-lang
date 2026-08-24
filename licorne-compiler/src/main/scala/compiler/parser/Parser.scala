package compiler.parser

import compiler.identifiers.{NormalFunOrVarId, TypeIdentifier}
import compiler.irs.asts.Asts.*
import compiler.irs.tokens.Tokens.*
import compiler.parser.ParseTree.^:
import compiler.parser.TreeParsers.*
import compiler.pipeline.CompilationStep.Parsing
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.lang.{Keyword, Operator, Operators, Overridability, Purity, ReassigPermission, Types, Variance, Visibility}
import compiler.lang.Operator.*
import compiler.lang.Keyword.{Import, *}
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
    case FirstLowercaseIdentifierToken(strValue) => strValue
  }

  private val highName = treeParser("A..Z") {
    case FirstUppercaseIdentifierToken(strValue) => strValue
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

  private val nullRef = kw(Null) map {
    _ => NullRef()
  } setName "nullRef"

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
  private val dotDot = op(DotDot).ignored
  private val sharp = op(Sharp).ignored
  private val colon = op(Colon).ignored
  private val semicolon = op(Semicolon).ignored
  private val maybeSemicolon = opt(op(Semicolon)).ignored
  private val -> = (op(Minus) ::: op(GreaterThan)).ignored
  private val doubleExclMark = op(ExclamationMark) ::: op(ExclamationMark)
  private val verticalBar = op(VerticalBar).ignored
  private val ampersand = op(Ampersand).ignored

  private val unaryOperator = op(Minus, ExclamationMark)
  private val assignmentOperator = op(PlusEq, MinusEq, TimesEq, DivEq, ModuloEq, Assig)

  // ---------- Syntax description -----------------------------------------------------------------------

  private lazy val funOrVarId = lowName map (NormalFunOrVarId(_))

  private lazy val possiblyPrefixedTypeNameWithSharp = highName OR (sharp ::: dot ::: repeatWithSepNonZero(lowName, dot) ::: dot ::: highName) map {
    case prefixes ^: actualId =>
      TypeIdentifier(prefixes, actualId)
    case actualId: String =>
      TypeIdentifier(Nil, actualId)
  }

  private lazy val source: FinalTreeParser[Source] = {
    opt(pkgDecl) ::: repeat(importStat) ::: repeat(topLevelDef ::: opt(op(Semicolon)).ignored) ::: endOfFile.ignored map {
      case pkgDeclOpt ^: imports ^: defs => Source(pkgDeclOpt, imports, defs)
    }
  } setName "source"

  private lazy val pkgDecl = kw(Package).ignored ::: repeatWithSep(lowName, dot) ::: semicolon map {
    case nameParts => PackageDecl(nameParts)
  } setName "pkgDecl"

  private lazy val funIdImport = funOrVarId ::: opt(kw(As).ignored ::: funOrVarId) map {
    case funId ^: aliasOpt => (funId, aliasOpt)
  } setName "funIdImport"

  private lazy val importStat = kw(Import).ignored ::: repeat(lowName ::: dot) ::: highName ::: (
    op(Semicolon) OR kw(As).ignored ::: highName ::: semicolon OR dot ::: (funIdImport OR openBrace ::: repeatWithSep(funIdImport, comma) ::: closeBrace OR op(Times)) ::: semicolon
    ) map {
    case prefix ^: importedName ^: Operator.Semicolon =>
      TypeImportStat(TypeIdentifier(prefix, importedName), None)
    case prefix ^: importedName ^: (alias: String) =>
      TypeImportStat(TypeIdentifier(prefix, importedName), Some(alias))
    case prefix ^: importedName ^: (singleImportedFun: (NormalFunOrVarId, Option[NormalFunOrVarId])) =>
      FunctionsImportStat(TypeIdentifier(prefix, importedName), Some(List(singleImportedFun)))
    case prefix ^: importedName ^: (importedFunctions: List[(NormalFunOrVarId, Option[NormalFunOrVarId])]) =>
      FunctionsImportStat(TypeIdentifier(prefix, importedName), Some(importedFunctions))
    case prefix ^: importedName ^: (_: Operator /* this has to be Times (wildcard import) */) =>
      FunctionsImportStat(TypeIdentifier(prefix, importedName), None)
  } setName "importStat"

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
    kw(Datatype).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt ::: supertypesListOpt ::: methodsListOpt map {
      case id ^: typeParams ^: supertypes ^: functions => DataTypeDef(id, typeParams, functions, supertypes)
    }
  } setName "datatypeDef"

  private lazy val recordDef = {
    kw(Record).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(recordOrTypeAliasParam, comma) ::: closeParenth) ::: supertypesListOpt ::: methodsListOpt map {
      case name ^: typeParams ^: fieldsOpt ^: supertypes ^: functions =>
        RecordDef(name, typeParams, fieldsOpt.getOrElse(Nil), functions, supertypes)
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

    opt(kw(Pure)) ::: opt(kw(Main, Private, Open)) ::: kw(Fn).ignored ::: funOrVarId ::: typeParamsWithoutVarianceListOpt
      ::: openParenth ::: repeatWithSep(funParamTree, comma) ::: opt(kw(Where).ignored ::: expr) ::: closeParenth
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
        val overridability = optModif match {
          case Some(Open) => Overridability.Open
          case _ if bodyOptDesugared.isDefined => Overridability.Final
          case _ => Overridability.Abstract
        }
        FunDef(funName, typeParams, params, optRetType, optPrecond, bodyOptDesugared,
          visibility = if optModif.contains(Keyword.Private) then Visibility.Private else Visibility.Public,
          overridability,
          purity = if optPure.isDefined then Purity.Pure else Purity.PossiblyImpure,
          isMain = optModif.contains(Main)
        )
    }
  } setName "funDef"

  private lazy val funParamTree = funOrClassParamTree OR thisParam

  private lazy val classParamTree = funOrClassParamTree OR publicParam

  private lazy val funOrClassParamTree: P[FunctionParam & ClassParam] = recursive {
    opt(kw(Var)) ::: funOrVarId ::: colon ::: typeTree map {
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
    kw(Public).ignored ::: funOrVarId ::: colon ::: typeTree map {
      case id ^: tpe => PublicParam(id, tpe)
    }
  } setName "publicParam"

  private lazy val recordOrTypeAliasParam: P[RecordParam & TypeAliasParam] = recursive {
    funOrVarId ::: colon ::: typeTree map {
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

  private lazy val closureTypeTree = opt(kw(Pure)) ::: kw(Fn).ignored ::: openParenth ::: repeatWithSep(typeTree, comma) ::: closeParenth ::: -> ::: typeTree map {
    case optPure ^: paramTypes ^: resultType => ClosureTypeTree(paramTypes, resultType, optPure.isDefined)
  } setName "closureTypeTree"

  private lazy val intRangeTypeTree = openBracket ::: opt(expr) ::: dotDot ::: opt(opt(op(LessThan)) ::: expr) ::: closeBracket map {
    case lowOpt ^: Some(ltOpt ^: ub) => IntRangeTypeTree(lowOpt, Some(ub), upperIncluded = ltOpt.isEmpty)
    case lowOpt ^: None => IntRangeTypeTree(lowOpt, None, upperIncluded = false)
  } setName "intRangeTypeTree"

  private lazy val typeTree = recursive(unionTypeTree) setName "typeTree"

  private lazy val unionTypeTree: P[TypeTree] = recursive {
    repeatWithSepNonZero(intersectionTypeTree, verticalBar) map {
      case List(singleType) => singleType
      case types => UnionTypeTree(types)
    }
  } setName "unionTypeTree"

  private lazy val intersectionTypeTree: P[TypeTree] = recursive {
    repeatWithSepNonZero(simpleTypeTree, ampersand) map {
      case List(singleType) => singleType
      case types => IntersectionTypeTree(types)
    }
  } setName "typeTree"

  private lazy val simpleTypeTree: P[TypeTree] = recursive {
    typeTreeWithoutPredOrQMark ::: opt(op(QuestionMark) OR kw(With).ignored ::: expr) map {
      case baseType ^: None => baseType
      case baseType ^: Some(_: Operator) => NullableTypeTree(baseType)
      case baseType ^: Some(predicate: Expr) => RefinedTypeTree(baseType, predicate)
    }
  } setName "typeTree"

  private lazy val typeTreeWithoutPredOrQMark: P[TypeTree] = recursive {
    nominalTypeTree OR closureTypeTree OR intRangeTypeTree OR (openParenth ::: typeTree ::: closeParenth)
  } setName "noNullableTypeTree"

  private lazy val typeArgsListOpt = opt(openBracket ::: repeatWithSep(typeTree, comma) ::: closeBracket)

  private lazy val nominalTypeTree: P[NominalTypeTree] = recursive {
    possiblyPrefixedTypeNameWithSharp ::: typeArgsListOpt ::: opt(openParenth ::: repeatWithSepNonZero(expr, comma) ::: closeParenth) map {
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
    BinaryOperatorsParser.buildFrom(Operator.operatorsByDecreasingPrecedence, binopArg)
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
    ((noBinopExpr OR recordOrModuleInstantiation OR panicExpr) ::: opt(((kw(As) OR kw(Is)) ::: typeTree) OR doubleExclMark)) map {
      case expression ^: None => expression
      case expression ^: Some(As ^: (tp: TypeTree)) => Cast(expression, tp)
      case expression ^: Some(Is ^: (tp: TypeTree)) => TypeTest(expression, tp)
      case expression ^: Some((_: Operator) ^: (_: Operator)) => HybridCast(expression)
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

  private lazy val objectRef = possiblyPrefixedTypeNameWithSharp map (ObjectRef(_))

  private lazy val varRef = funOrVarId map (name => VariableRef(name)) setName "varRef"

  private lazy val atomicExpr: P[Expr] = recursive {
    varRef OR thisRef OR itRef OR objectRef OR literalValue OR nullRef OR parenthesizedExpr
  } setName "atomicExpr"

  private lazy val selectOrIndexingChain = recursive {

    def maybeWithTypeAnnot(typeAnnotOpt: Option[TypeTree])(afterSelectsFolding: Expr): Expr = {
      typeAnnotOpt match {
        case Some(tpe) => TypeAscription(afterSelectsFolding, tpe)
        case None => afterSelectsFolding
      }
    }
    
    atomicExpr ::: (typeArgsListOpt ::: parenthArgsList OR repeat(dot ::: funOrVarId ::: opt(typeArgsListOpt ::: parenthArgsList))) ::: opt(colon ::: typeTree) map {
      case atExpr ^: (selects: List[NormalFunOrVarId ^: Option[Option[List[TypeTree]] ^: List[Expr]]]) ^: typeAnnotOpt =>
        maybeWithTypeAnnot(typeAnnotOpt) {
          selects.foldLeft(atExpr) {
            case (rec, id ^: None) => Select(rec, id)
            case (rec, id ^: Some(typeArgsOpt ^: args)) => Call(Select(rec, id), typeArgsOpt.getOrElse(List.empty), args)
          }
        }
      case atExpr ^: (typeArgsOpt ^: args) ^: typeAnnotOpt =>
        maybeWithTypeAnnot(typeAnnotOpt) {
          Call(atExpr, typeArgsOpt.getOrElse(List.empty), args)
        }
    }
  } setName "selectOrIndexingChain"

  private lazy val closure = recursive {
    opt(kw(Pure)) ::: kw(Fn).ignored ::: openParenth ::: repeatWithSep(funOrVarId ::: opt(colon ::: typeTree), comma) ::: closeParenth ::: -> ::: (expr OR block) map {
      case optPure ^: params ^: (body: Block) =>
        ClosureDef(params.toPairs, body, optPure.isDefined)
      case optPure ^: params ^: (expr: Expr) =>
        ClosureDef(params.toPairs, Block(List(ReturnStat(Some(expr)))), optPure.isDefined)
    }
  } setName "closure"

  private lazy val parenthesizedExpr = recursive {
    openParenth ::: expr ::: closeParenth
  } setName "parenthesizedExpr"

  private lazy val recordOrModuleInstantiation = recursive {
    kw(New).ignored ::: possiblyPrefixedTypeNameWithSharp ::: typeArgsListOpt ::: openParenth ::: repeatWithSep(fieldInitializer, comma) ::: closeParenth map {
      case tid ^: tArgs ^: initializers => RecordOrClassInstantiation(tid, tArgs.getOrElse(List.empty), initializers)
    }
  } setName "recordOrModuleInstantiation"

  private lazy val fieldInitializer = recursive {
    funOrVarId ::: opt(assig ::: expr) map {
      case fieldName ^: Some(rhs) => FullFieldInitializer(fieldName, rhs)
      case fieldName ^: None => ShorthandFieldInitializer(fieldName)
    }
  } setName "fieldInitializer"

  private lazy val stat: P[Statement] = {
    exprOrAssig OR valDef OR varDef OR whileLoop OR forLoop OR ifThenElse OR returnStat
  } setName "stat"

  private lazy val valDef = {
    kw(Val).ignored ::: funOrVarId ::: opt(colon ::: typeTree) ::: opt(assig ::: expr) map {
      case valName ^: optType ^: rhsOpt => LocalDef(valName, optType, rhsOpt, ReassigPermission.Val)
    }
  } setName "valDef"

  private lazy val varDef = {
    kw(Var).ignored ::: funOrVarId ::: opt(colon ::: typeTree) ::: opt(assig ::: expr) map {
      case varName ^: optType ^: rhsOpt => LocalDef(varName, optType, rhsOpt, ReassigPermission.Var)
    }
  } setName "varDef"

  private lazy val whileLoop = recursive {
    kw(While).ignored ::: expr ::: block map {
      case cond ^: body => WhileLoop(cond, body)
    }
  } setName "whileLoop"

  private lazy val forLoopHeaderWithoutParenth: P[(List[LocalDef], Expr, List[Assignment])] = {
    repeatWithSep(valDef OR varDef, comma) ::: semicolon ::: expr ::: semicolon ::: repeatWithSep(assignmentStat, comma) map {
      case initStats ^: cond ^: stepStats => (initStats, cond, stepStats)
    }
  } setName "forLoopHeaderWithoutParenth"

  private lazy val forLoop = recursive {
    kw(For).ignored ::: (forLoopHeaderWithoutParenth OR openParenth ::: forLoopHeaderWithoutParenth ::: closeParenth) ::: block map {
      case (initStats, cond, stepStats) ^: body => ForLoop(initStats, cond, stepStats, body)
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
      Source(None, List.empty, List.empty)
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
