package compiler.parser

import compiler.identifiers.{ItId, NormalFunOrVarId, TypeIdentifier}
import compiler.irs.asts.Asts.*
import compiler.irs.tokens.Tokens.*
import compiler.parser.primitives.ParseTree.^:
import compiler.parser.primitives.TreeParsers.*
import compiler.pipeline.CompilationStep.Parsing
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.lang.{FuncVisibility, Keyword, Operator, Operators, Overridability, Purity, ReassigPermission, TypeVisibility, Types, Variance}
import compiler.lang.Operator.*
import compiler.lang.Keyword.*
import compiler.lang.Types.PrimitiveType
import compiler.lang.Types.PrimitiveType.{DoubleType, IntType, UnitType}
import compiler.parser.primitives.{BinaryOperatorsParser, LL1Iterator}

import scala.compiletime.uninitialized

final class Parser(errorReporter: ErrorReporter) extends CompilerStep[(List[PositionedToken], String), Source] {
  private implicit val implErrorReporter: ErrorReporter = errorReporter
  private var ll1Iterator: LL1Iterator = uninitialized

  private type P[X] = AnyTreeParser[X]

  // ---------- Syntax primitives -----------------------------------------------------------------------

  private def op(operators: Operator*) = treeParser(operators.toList.map(op => s"'${op.str}'")) {
    case OperatorToken(operator) if operators.contains(operator) => operator
  }

  private def kw(keywords: Keyword*) = treeParser(keywords.toList.map(kw => s"'${kw.str}'")) {
    case KeywordToken(keyword) if keywords.contains(keyword) => keyword
  }

  private val lowName = treeParser(List("an identifier starting with a lowercase")) {
    case FirstLowercaseIdentifierToken(strValue) => strValue
  }

  private val highName = treeParser(List("an identifier starting with an uppercase")) {
    case FirstUppercaseIdentifierToken(strValue) => strValue
  }

  private val numericLiteralValue: FinalTreeParser[NumericLiteral] = treeParser(List(s"a literal of type $IntType or $DoubleType")) {
    case IntLitToken(value) => IntLit(value)
    case DoubleLitToken(value) => DoubleLit(value)
  }

  private val nonNumericLiteralValue: FinalTreeParser[NonNumericLiteral] = treeParser(List(s"a literal")) {
    case UnitLitToken => UnitLit()
    case BoolLitToken(value) => BoolLit(value)
    case CharLitToken(value) => CharLit(value)
    case StringLitToken(value) => StringLit(value)
  }

  private val literalValue: FinalTreeParser[Literal] = withDescription("a literal") {
    numericLiteralValue OR nonNumericLiteralValue
  }

  private val nullRef = kw(Null) map {
    _ => NullRef()
  }

  private val endl = treeParser(List("the end of the line")) {
    case EndlToken => ()
  }

  private val endOfFile = treeParser(List("the end of the file")) {
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
  private val statementSep = withDescription("statement separator")(op(Semicolon) OR endl).ignored
  private val semicolon = op(Semicolon).ignored
  private val maybeSemicolon = opt(op(Semicolon)).ignored
  private val -> = op(RightArrow).ignored
  private val doubleExclMark = op(ExclamationMark) ::: op(ExclamationMark)
  private val verticalBar = op(VerticalBar).ignored
  private val ampersand = op(Ampersand).ignored

  private val unaryOperator = op(Minus, ExclamationMark)
  private val assignmentOperator = op(PlusEq, MinusEq, TimesEq, DivEq, ModuloEq, PlusPlusEq, Assig)

  // ---------- Syntax description -----------------------------------------------------------------------

  private lazy val funOrVarId = lowName map (NormalFunOrVarId(_))

  private lazy val possiblyPrefixedTypeNameWithSharp = withDescription("a type identifier") {
    highName OR (sharp ::: dot ::: repeatWithSepNonZero(lowName, dot) ::: dot ::: highName) map {
      case prefixes ^: actualId =>
        TypeIdentifier(prefixes, actualId)
      case actualId: String =>
        TypeIdentifier(Nil, actualId)
    }
  }

  private lazy val source: FinalTreeParser[Source] = {
    opt(pkgDecl) ::: repeat(importStat ::: maybeSemicolon) ::: repeat(topLevelDef ::: maybeSemicolon) ::: endOfFile.ignored map {
      case pkgDeclOpt ^: imports ^: defs => Source(pkgDeclOpt, imports, defs)
    }
  }

  private lazy val pkgDecl = withDescription("a package declaration") {
    kw(Package).ignored ::: repeatWithSep(lowName, dot) ::: maybeSemicolon map {
      case nameParts => PackageDecl(nameParts)
    }
  }

  private lazy val funIdImport = funOrVarId ::: opt(kw(As).ignored ::: funOrVarId) map {
    case funId ^: aliasOpt => (funId, aliasOpt)
  }

  private lazy val importStat = withDescription("an import statement") {
    kw(Import).ignored ::: repeat(lowName ::: dot) ::: highName
      ::: opt(kw(As).ignored ::: highName OR dot ::: (funIdImport OR openBrace ::: repeatWithSep(funIdImport, comma) ::: closeBrace OR op(Times))) map {
      case prefix ^: importedName ^: None =>
        TypeImportStat(TypeIdentifier(prefix, importedName), None)
      case prefix ^: importedName ^: Some(alias: String) =>
        TypeImportStat(TypeIdentifier(prefix, importedName), Some(alias))
      case prefix ^: importedName ^: Some(singleImportedFun: (NormalFunOrVarId, Option[NormalFunOrVarId])) =>
        FunctionsImportStat(TypeIdentifier(prefix, importedName), Some(List(singleImportedFun)))
      case prefix ^: importedName ^: Some(importedFunctions: List[(NormalFunOrVarId, Option[NormalFunOrVarId])]) =>
        FunctionsImportStat(TypeIdentifier(prefix, importedName), Some(importedFunctions))
      case prefix ^: importedName ^: Some(_: Operator /* this has to be Times (wildcard import) */) =>
        FunctionsImportStat(TypeIdentifier(prefix, importedName), None)
    }
  }

  private lazy val topLevelDef: P[TopLevelDef] = withDescription("a top level definition") {
    typeVisibilityModifierOpt ::: (interfaceDef OR objectDef OR classDef OR datatypeDef OR recordDef OR typeAliasDef) map {
      case visibility ^: df =>
        df.visibility = visibility
        df
    }
  }

  private lazy val interfaceDef: P[InterfaceDef] = withDescription("an interface declaration") {
    kw(Interface).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt ::: supertypesListOpt ::: methodsListOpt map {
      case id ^: typeParams ^: supertypes ^: functions =>
        InterfaceDef(id, typeParams, functions, supertypes, TypeVisibility.Public)
    }
  }

  private lazy val classDef: P[ClassDef] = withDescription("a class declaration") {
    kw(Class).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(classParamTreeWithOptDefault, comma) ::: closeParenth)
      ::: supertypesListOpt ::: fieldsAndMethodsListOpt map {
      case moduleName ^: typeParams ^: paramsOpt ^: supertypes ^: (encapsulatedFields, functions) =>
        ClassDef(moduleName, typeParams, paramsOpt.getOrElse(Nil), encapsulatedFields, functions, supertypes, TypeVisibility.Public)
    }
  }

  private lazy val objectDef: P[ObjectDef] = withDescription("an object declaration") {
    kw(Object).ignored ::: highName ::: supertypesListOpt ::: methodsListOpt map {
      case objectName ^: supertypes ^: functions =>
        ObjectDef(objectName, functions, supertypes, TypeVisibility.Public)
    }
  }

  private lazy val datatypeDef = withDescription("a datatype declaration") {
    kw(Datatype).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt ::: supertypesListOpt ::: methodsListOpt map {
      case id ^: typeParams ^: supertypes ^: functions => DataTypeDef(id, typeParams, functions, supertypes, TypeVisibility.Public)
    }
  }

  private lazy val recordDef = withDescription("a record declaration") {
    kw(Record).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(recordParamWithOptDefault, comma) ::: closeParenth) ::: supertypesListOpt ::: methodsListOpt map {
      case name ^: typeParams ^: fieldsOpt ^: supertypes ^: functions =>
        RecordDef(name, typeParams, fieldsOpt.getOrElse(Nil), functions, supertypes, TypeVisibility.Public)
    }
  }

  private lazy val typeAliasDef: P[TypeAliasDef] = withDescription("a typealias definition") {
    opt(kw(Opaque)) ::: kw(Typealias).ignored ::: highName ::: typeParamsPossiblyWithVarianceListOpt
      ::: opt(openParenth ::: repeatWithSep(typeAliasParam, comma) ::: closeParenth)
      ::: assig ::: typeTree map {
      case opaqueOpt ^: typeName ^: typeParams ^: paramsOpt ^: rhs => TypeAliasDef(typeName, typeParams, paramsOpt.getOrElse(List.empty), rhs, TypeVisibility.Public, isOpaque = opaqueOpt.isDefined)
    }
  }

  private lazy val encapsulatedFieldDef = withDescription("a field definition") {
    (kw(Val) OR kw(Var)) ::: funOrVarId ::: opt(colon ::: typeTree) ::: assig ::: expr map {
      case valOrVarKw ^: fieldId ^: typeOpt ^: rhs => EncapsulatedFieldDef(fieldId, typeOpt, rhs, isReassignable = valOrVarKw == Var)
    }
  }

  private lazy val typeVisibilityModifierOpt = {
    opt(kw(Private).ignored ::: opt(openParenth ::: repeatWithSep(lowName, dot) ::: closeParenth)) map {
      case Some(Some(pkgParts)) => TypeVisibility.PkgPrivate(pkgParts)
      case Some(None) => TypeVisibility.FilePrivate
      case None => TypeVisibility.Public
    }
  }

  private lazy val funDef = withDescription("a function declaration") {

    def isUnitType(typeTree: TypeTree): Boolean = typeTree match {
      case PrimitiveTypeTree(PrimitiveType.UnitType) => true
      case _ => false
    }

    opt(kw(Private, Open)) ::: opt(kw(Pure)) ::: kw(Fn).ignored ::: funOrVarId ::: typeParamsWithoutVarianceListOpt
      ::: openParenth ::: repeatWithSep(funParamTree, comma) ::: opt(kw(Where).ignored ::: expr) ::: closeParenth
      ::: opt(-> ::: typeTree) ::: opt(block OR assig ::: expr) map {
      case optModif ^: optPure ^: funName ^: typeParams ^: params ^: optPrecond ^: optRetType ^: bodyOptRaw =>
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
          visibility = if optModif.contains(Keyword.Private) then FuncVisibility.Private else FuncVisibility.Public,
          overridability,
          purity = if optPure.isDefined then Purity.Pure else Purity.PossiblyImpure
        )
    }
  }

  private lazy val funParamTree: P[FunctionParam] = withDescription("a function parameter") {
    simpleParamTree OR varParamTree OR thisParam
  }

  private lazy val classParamTreeWithOptDefault: P[(ClassParam, Option[Expr])] = withDescription("a class parameter") {
    (simpleParamTree OR valParamTree OR varParamTree OR publicParam) ::: opt(assig ::: expr) map {
      case paramTree ^: defaultInitOpt => (paramTree, defaultInitOpt)
    }
  }

  private lazy val recordParamTree = withDescription("a record parameter") {
    simpleParamTree OR valParamTree
  }

  private lazy val valParamTree = {
    kw(Val).ignored ::: funOrVarId ::: colon ::: typeTree map {
      case paramName ^: tpe => ValParam(paramName, tpe)
    }
  }

  private lazy val varParamTree = kw(Var).ignored ::: funOrVarId ::: colon ::: typeTree map {
    case paramName ^: tpe => VarParam(paramName, tpe)
  }

  private lazy val simpleParamTree = funOrVarId ::: colon ::: typeTree map {
    case paramName ^: tpe => SimpleParam(paramName, tpe)
  }

  private lazy val thisParam: P[ThisParam] = {
    kw(This).ignored ::: opt(colon ::: typeTree) map {
      case tpeOpt => ThisParam(tpeOpt)
    }
  }

  private lazy val publicParam: P[PublicParam] = {
    kw(Public).ignored ::: opt(kw(Val)) ::: funOrVarId ::: colon ::: typeTree map {
      case optVal ^: id ^: tpe =>
        optVal.foreach { _ =>
          errorReporter.warn(s"$Val after $Public is redundant", tpe.getPosition)(using Parsing)
        }
        PublicParam(id, tpe)
    }
  }

  private lazy val typeAliasParam: P[TypeAliasParam] = withDescription("a typealias parameter") {
    recursive {
      funOrVarId ::: colon ::: typeTree map {
        case name ^: tpe => SimpleParam(name, tpe)
      }
    }
  }

  private lazy val recordParamWithOptDefault: P[(RecordParam, Option[Expr])] = recordParamTree ::: opt(assig ::: expr) map {
    case paramTree ^: defaultOpt => (paramTree, defaultOpt)
  }

  private lazy val methodsListOpt: P[List[FunDef]] = {
    opt(openBrace ::: repeat(funDef ::: maybeSemicolon) ::: closeBrace) map {
      case None => List.empty
      case Some(methods) => methods
    }
  }

  private lazy val fieldsAndMethodsListOpt: P[(List[EncapsulatedFieldDef], List[FunDef])] = {
    opt(openBrace ::: repeatWithEnd(encapsulatedFieldDef, statementSep) ::: repeat(funDef ::: maybeSemicolon) ::: closeBrace) map {
      case None => (List.empty, List.empty)
      case Some(fields ^: methods) => (fields, methods)
    }
  }

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
  }

  private lazy val possiblyNegativeNumericLiteralValue: FinalTreeParser[NumericLiteral] = {
    (numericLiteralValue OR (op(Minus) ::: numericLiteralValue)) map {
      case _ ^: IntLit(value) => IntLit(-value)
      case _ ^: DoubleLit(value) => DoubleLit(-value)
      case lit: NumericLiteral => lit
    }
  }

  private lazy val closureTypeTree = opt(kw(Pure)) ::: kw(Fn).ignored ::: openParenth ::: repeatWithSep(typeTree, comma) ::: closeParenth ::: -> ::: typeTree map {
    case optPure ^: paramTypes ^: resultType => ClosureTypeTree(paramTypes, resultType, optPure.isDefined)
  }

  private lazy val intRangeTypeTree = openBracket ::: opt(expr) ::: dotDot ::: opt(opt(op(LessThan)) ::: expr) ::: closeBracket map {
    case lowOpt ^: Some(ltOpt ^: ub) => IntRangeTypeTree(lowOpt, Some(ub), upperIncluded = ltOpt.isEmpty)
    case lowOpt ^: None => IntRangeTypeTree(lowOpt, None, upperIncluded = false)
  }

  private lazy val typeTree = withDescription("a type") {
    recursive(unionTypeTree)
  }

  private lazy val unionTypeTree: P[TypeTree] = withDescription("a union type") {
    recursive {
      repeatWithSepNonZero(intersectionTypeTree, verticalBar) map {
        case List(singleType) => singleType
        case types => UnionTypeTree(types)
      }
    }
  }

  private lazy val intersectionTypeTree: P[TypeTree] = withDescription("an intersection type") {
    recursive {
      repeatWithSepNonZero(simpleTypeTree OR ternaryTypeTree, ampersand) map {
        case List(singleType) => singleType
        case types => IntersectionTypeTree(types)
      }
    }
  }

  private lazy val ternaryTypeTree: P[TypeTree] = withDescription("a ternary type") {
    recursive {
      kw(When).ignored ::: expr ::: kw(Then).ignored ::: typeTree ::: kw(Else).ignored ::: typeTree map {
        case cond ^: leftType ^: rightType => TernaryTypeTree(cond, leftType, rightType)
      }
    }
  }

  private lazy val simpleTypeTree: P[TypeTree] = withDescription("a simple type") {
    recursive {
      typeTreeWithoutPredOrQMark ::: opt(op(QuestionMark) OR kw(With).ignored ::: expr) map {
        case baseType ^: None => baseType
        case baseType ^: Some(_: Operator) => NullableTypeTree(baseType)
        case baseType ^: Some(predicate: Expr) => RefinedTypeTree(baseType, predicate)
      }
    }
  }

  private lazy val typeTreeWithoutPredOrQMark: P[TypeTree] = withDescription("a base type") {
    recursive {
      nominalTypeTree OR closureTypeTree OR intRangeTypeTree OR (openParenth ::: typeTree ::: closeParenth)
    }
  }

  private lazy val typeArgsListOpt = opt(openBracket ::: repeatWithSep(typeTree, comma) ::: closeBracket)

  private lazy val nominalTypeTree: P[NominalTypeTree] = withDescription("a named type") {
    recursive {
      possiblyPrefixedTypeNameWithSharp ::: typeArgsListOpt ::: opt(openParenth ::: repeatWithSepNonZero(expr, comma) ::: closeParenth) map {
        case baseTypeName ^: typeArgsOpt ^: paramsOpt =>
          val primTypeOpt = Types.primTypeFor(baseTypeName).map(PrimitiveTypeTree(_))
          if (primTypeOpt.isDefined && typeArgsOpt.exists(_.nonEmpty)) {
            errorReporter.report(Err(Parsing, "primitive types cannot take type parameters", typeArgsOpt.get.head.getPosition))
          }
          primTypeOpt.getOrElse(NamedTypeTree(baseTypeName, typeArgsOpt.getOrElse(Nil), paramsOpt.getOrElse(Nil)))
      }
    }
  }

  private lazy val block: P[Block] = withDescription("a block") {
    recursive {
      openBrace ::: repeatWithEnd(stat, statementSep) ::: closeBrace map {
        stats => Block(stats)
      }
    }
  }

  private lazy val exprOrAssig = withDescription("an expression or an assignment") {
    recursive {
      expr ::: opt(assignmentOperator ::: expr) map {
        case singleExpr ^: None => singleExpr
        case lhs ^: Some(Assig ^: rhs) => VarAssig(lhs, rhs)
        case lhs ^: Some(op ^: rhs) => VarModif(lhs, rhs, Operators.assigOperators.apply(op))
      }
    }
  }

  private lazy val assignmentStat = withDescription("an assignment") {
    recursive {
      expr ::: assignmentOperator ::: expr map {
        case lhs ^: Assig ^: rhs => VarAssig(lhs, rhs)
        case lhs ^: operator ^: rhs => VarModif(lhs, rhs, Operators.assigOperators.apply(operator))
      }
    }
  }

  private lazy val expr: P[Expr] = withDescription("an expression") {
    recursive {
      simpleExpr OR ternary OR regularClosure OR shorthandClosure
    }
  }

  private lazy val simpleExpr: P[Expr] = {
    recursive {
      BinaryOperatorsParser.buildFrom(Operator.operatorsByDecreasingPrecedence, binopArg)
    }
  }

  private lazy val noBinopExpr = recursive {
    opt(unaryOperator) ::: selectOrIndexingChain map {
      case Some(Minus) ^: IntLit(value) => IntLit(-value)
      case Some(Minus) ^: DoubleLit(value) => DoubleLit(-value)
      case Some(unOp) ^: operand => UnaryOp(unOp, operand)
      case None ^: simpleExpr => simpleExpr
    }
  }

  private lazy val binopArg = recursive {
    ((noBinopExpr OR recordOrModuleInstantiation OR panicExpr) ::: opt(((kw(As) OR kw(Is)) ::: typeTree) OR doubleExclMark)) map {
      case expression ^: None => expression
      case expression ^: Some(As ^: (tp: TypeTree)) => Cast(expression, tp)
      case expression ^: Some(Is ^: (tp: TypeTree)) => TypeTest(expression, tp)
      case expression ^: Some((_: Operator) ^: (_: Operator)) => HybridCast(expression)
      case _ => assert(false)
    }
  }

  private lazy val parenthArgsList = withDescription("a parenthesized list of arguments") {
    recursive {
      openParenth ::: repeatWithSep(expr, comma) ::: closeParenth
    }
  }

  private lazy val typeParamsWithoutVarianceListOpt = {
    opt(openBracket ::: repeatWithSepNonZero(typeParamWithoutVariance, comma) ::: closeBracket) map (_.getOrElse(List.empty))
  }

  // TODO allow union and intersection types as bounds?
  private lazy val typeParamWithoutVariance = highName ::: opt(kw(Sub).ignored ::: typeTree) ::: opt(kw(Super).ignored ::: typeTree) map {
    case id ^: upperBoundOpt ^: lowerBoundOpt =>
      TypeParamWithoutVariance(id, upperBoundOpt, lowerBoundOpt)
  }

  private lazy val typeParamsPossiblyWithVarianceListOpt = {
    opt(openBracket ::: repeatWithSepNonZero(typeParamPossiblyWithVariance, comma) ::: closeBracket) map (_.getOrElse(List.empty))
  }

  private lazy val typeParamPossiblyWithVariance = opt(op(Plus, Minus)) ::: highName ::: opt(kw(Sub).ignored ::: typeTree) ::: opt(kw(Super).ignored ::: typeTree) map {
    case varianceSymbolOpt ^: typeParamName ^: upperBoundOpt ^: lowerBoundOpt =>
      val variance = varianceSymbolOpt match {
        case Some(Plus) => Variance.Covariant
        case Some(Minus) => Variance.Contravariant
        case Some(_) => assert(false)
        case None => Variance.Invariant
      }
      TypeParamWithVariance(typeParamName, variance, upperBoundOpt, lowerBoundOpt)
  }

  private lazy val thisRef = kw(This) map (_ => ThisRef())

  private lazy val itRef = kw(It) map (_ => ItRef())

  private lazy val objectRef = possiblyPrefixedTypeNameWithSharp map (ObjectRef(_))

  private lazy val varRef = funOrVarId map (name => VariableRef(name))

  private lazy val atomicExpr: P[Expr] = recursive {
    varRef OR thisRef OR itRef OR objectRef OR literalValue OR nullRef OR parenthesizedExpr
  }

  private lazy val selectOrIndexingChain = recursive {

    def maybeWithTypeAnnot(typeAnnotOpt: Option[TypeTree])(afterSelectsFolding: Expr): Expr = {
      typeAnnotOpt match {
        case Some(tpe) => TypeAscription(afterSelectsFolding, tpe)
        case None => afterSelectsFolding
      }
    }

    atomicExpr ::: (typeArgsListOpt ::: parenthArgsList OR repeat(dot ::: funOrVarId ::: opt(typeArgsListOpt ::: (parenthArgsList OR shorthandClosure.map(List(_)))))) ::: opt(colon ::: typeTree) map {
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
  }

  private lazy val regularClosure = withDescription("a closure") {
    recursive {
      opt(kw(Pure)) ::: kw(Fn).ignored ::: openParenth ::: repeatWithSep(funOrVarId ::: opt(colon ::: typeTree), comma) ::: closeParenth ::: -> ::: (expr OR block) map {
        case optPure ^: params ^: (body: Block) =>
          ClosureDef(params.toPairs, body, optPure.isDefined)
        case optPure ^: params ^: (expr: Expr) =>
          ClosureDef(params.toPairs, mkSimpleClosureBody(expr), optPure.isDefined)
      }
    }
  }

  private lazy val shorthandClosure: P[ClosureDef] = withDescription("a shorthand closure") {
    recursive {
      verticalBar ::: expr ::: verticalBar map { expr =>
        ClosureDef(List(ItId -> None), mkSimpleClosureBody(expr), declaredPure = false)
      }
    }
  }

  private def mkSimpleClosureBody(expr: Expr): Block =
    Block(List(ReturnStat(Some(expr)).withDesugaringSource(expr))).withDesugaringSource(expr)

  private lazy val parenthesizedExpr = recursive {
    openParenth ::: expr ::: closeParenth
  }

  private lazy val recordOrModuleInstantiation = withDescription("an instantiation") {
    recursive {
      kw(New).ignored ::: possiblyPrefixedTypeNameWithSharp ::: typeArgsListOpt ::: openParenth ::: repeatWithSep(fieldInitializer, comma) ::: closeParenth map {
        case tid ^: tArgs ^: initializers => RecordOrClassInstantiation(tid, tArgs.getOrElse(List.empty), initializers)
      }
    }
  }

  private lazy val fieldInitializer = withDescription("a field initializer") {
    recursive {
      expr ::: opt(assig ::: expr) map {
        case initExpr ^: None => ShorthandFieldInitializer(initExpr)
        case VariableRef(fldId) ^: Some(initExpr) => FullFieldInitializer(fldId, initExpr)
        case malformedLabelExpr ^: Some(initExpr) =>
          errorReporter.reportError("malformed initializer", malformedLabelExpr.getPosition)(using Parsing)
          ShorthandFieldInitializer(initExpr)
      }
    }
  }

  private lazy val stat: P[Statement] = withDescription("a statement") {
    exprOrAssig OR valDef OR varDef OR whileLoop OR forLoop OR ifThenElse OR returnStat
  }

  private lazy val valDef = withDescription("a value declaration") {
    kw(Val).ignored ::: funOrVarId ::: opt(colon ::: typeTree) ::: opt(assig ::: expr) map {
      case valName ^: optType ^: rhsOpt => LocalDef(valName, optType, rhsOpt, ReassigPermission.Val)
    }
  }

  private lazy val varDef = withDescription("a variable declaration") {
    kw(Var).ignored ::: funOrVarId ::: opt(colon ::: typeTree) ::: opt(assig ::: expr) map {
      case varName ^: optType ^: rhsOpt => LocalDef(varName, optType, rhsOpt, ReassigPermission.Var)
    }
  }

  private lazy val whileLoop = withDescription(s"a $While loop") {
    recursive {
      kw(While).ignored ::: expr ::: block map {
        case cond ^: body => WhileLoop(cond, body)
      }
    }
  }

  private lazy val forLoopHeaderWithoutParenth: P[(List[LocalDef], Expr, List[Assignment])] = {
    repeatWithSep(valDef OR varDef, comma) ::: semicolon ::: expr ::: semicolon ::: repeatWithSep(assignmentStat, comma) map {
      case initStats ^: cond ^: stepStats => (initStats, cond, stepStats)
    }
  }

  private lazy val forLoop = withDescription(s"a $For loop") {
    recursive {
      kw(For).ignored ::: (forLoopHeaderWithoutParenth OR openParenth ::: forLoopHeaderWithoutParenth ::: closeParenth) ::: block map {
        case (initStats, cond, stepStats) ^: body => ForLoop(initStats, cond, stepStats, body)
      }
    }
  }

  private lazy val ifThenElse: P[IfThenElse] = withDescription(s"an $If statement") {
    recursive {
      kw(If).ignored ::: expr ::: block ::: opt(kw(Else).ignored ::: (ifThenElse OR block)) map {
        case cond ^: thenBr ^: optElse => IfThenElse(cond, thenBr, optElse)
      }
    }
  }

  private lazy val ternary = withDescription(s"a $When expression") {
    recursive {
      kw(When).ignored ::: expr ::: kw(Then).ignored ::: expr ::: kw(Else).ignored ::: expr map {
        case cond ^: thenBr ^: elseBr => Ternary(cond, thenBr, elseBr)
      }
    }
  }

  private lazy val returnStat = withDescription(s"a $Return statement") {
    kw(Return).ignored ::: opt(expr) map (optRetVal => ReturnStat(optRetVal))
  }

  private lazy val panicExpr = withDescription(s"a $Panic expression") {
    kw(Panic).ignored ::: expr map PanicExpr.apply
  }

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
