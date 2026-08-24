package compiler.display

import compiler.identifiers.FunOrVarId
import compiler.irs.ssa.SSA.*
import compiler.irs.ssa.{Formulas, IRLevelFormulaPrinter, SSA}
import compiler.irs.ssa.Formulas.{Formula, IdValue, NamedIdValue}
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.*
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Position
import compiler.typing.TypeCandidatesStore
import compiler.valproxies.ProxyStore

import java.util.stream.Collectors

final class SSAPrinter(
                        proxyStore: ProxyStore,
                        typeCandidatesStore: TypeCandidatesStore,
                        indentUnit: String,
                        printTypes: Boolean,
                        commentsAlignmentGranularity: Int = 30
                      ) extends CompilerStep[Program, String] {

  private given ProxyStore = proxyStore

  override def apply(program: Program): String = {
    given Program = program

    given pps: PrettyPrintString = PrettyPrintString(indentUnit)

    for ((_, sig) <- program.typeAliases) {
      printTypeAlias(sig)
      pps.newLine()
    }
    for ((_, sig) <- program.interfaces) {
      printInterface(sig)
      pps.newLine()
    }
    for ((_, sig) <- program.classes) {
      printClass(sig)
      pps.newLine()
    }
    for ((_, sig) <- program.objects) {
      printObject(sig)
      pps.newLine()
    }
    for ((_, sig) <- program.datatypes) {
      printDatatype(sig)
      pps.newLine()
    }
    for ((_, sig) <- program.records) {
      printRecord(sig)
      pps.newLine()
    }

    pps.built
  }

  private def printTypeAlias(typealiasSig: TypeAliasSignature)
                            (using pps: PrettyPrintString, program: Program): Unit = {
    val TypeAliasSignature(id, typeParams, params, rhs, sigScope, declPosOpt) = typealiasSig
    pps.add(s"TYPEALIAS (scope ${sigScope.scopeUid})").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
      .add(mkTypeAliasParamsDescr(params))
      .add(" = ").add(rhs)
      .add(mkPosDescr(declPosOpt))
      .newLine()
  }

  private def printInterface(interfaceSig: InterfaceSignature)
                            (using pps: PrettyPrintString, program: Program): Unit = {
    val InterfaceSignature(id, typeParams, functions, directSupertypes, sigScope, declPosOpt) = interfaceSig
    pps.add(s"INTERFACE (scope ${sigScope.scopeUid})").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
      .add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
    printFunctionsBlockIfNotEmpty(functions, emptyLineBeforeFunc = false)
    pps.newLine()
  }

  private def printClass(classSig: ClassSignature)
                        (using pps: PrettyPrintString, program: Program): Unit = {
    val ClassSignature(id, typeParams, fields, functions, directSupertypes, sigScope, declPosOpt) = classSig
    pps.add(s"CLASS (scope ${sigScope.scopeUid})").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
    printFields(fields)
    pps.add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
    printFunctionsBlockIfNotEmpty(functions, emptyLineBeforeFunc = true)
    pps.newLine()
  }

  private def printObject(objectSig: ObjectSignature)
                         (using pps: PrettyPrintString, program: Program): Unit = {
    val ObjectSignature(id, functions, directSupertypes, sigScope, declPosOpt) = objectSig
    pps.add(s"OBJECT (scope ${sigScope.scopeUid})").addSpace().add(id)
      .add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
    printFunctionsBlockIfNotEmpty(functions, emptyLineBeforeFunc = true)
    pps.newLine()
  }

  private def printDatatype(datatypeSig: DatatypeSignature)
                           (using pps: PrettyPrintString, program: Program): Unit = {
    val DatatypeSignature(id, typeParams, functions, directSupertypes, directSubtypes, sigScope, declPosOpt) = datatypeSig
    pps.add(s"DATATYPE (scope ${sigScope.scopeUid})").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
      .add(mkSuperTypesDescr(directSupertypes))
      .add(" with cases ")
    traverseIterable(directSubtypes.iterator) { subT =>
      pps.add(subT)
    } {
      pps.add(", ")
    }
    pps.add(mkPosDescr(declPosOpt))
    printFunctionsBlockIfNotEmpty(functions, emptyLineBeforeFunc = false)
    pps.newLine()
  }

  private def printRecord(recordSig: RecordSignature)
                         (using pps: PrettyPrintString, program: Program): Unit = {
    val RecordSignature(id, typeParams, fields, functions, directSupertypes, sigScope, declPosOpt) = recordSig
    pps.add(s"RECORD (scope ${sigScope.scopeUid})").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
    printFields(fields)
    pps.add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
    printFunctionsBlockIfNotEmpty(functions, emptyLineBeforeFunc = false)
    pps.newLine()
  }

  private def printFunctionsBlockIfNotEmpty(functions: Map[FunOrVarId, FunctionSignature], emptyLineBeforeFunc: Boolean)
                                           (using pps: PrettyPrintString, program: Program): Unit = {
    if (functions.nonEmpty) {
      pps.addSpace().block {
        traverseIterable(functions.iterator) { (_, funSig) =>
          if (emptyLineBeforeFunc) {
            pps.newLine()
          }
          printFunction(funSig)
        } {
          pps.newLine()
        }
      }
    }
  }

  private def printFunction(funSig: FunctionSignature)
                           (using pps: PrettyPrintString, program: Program): Unit = {
    val FunctionSignature(ownerName, functionName, typeParams, paramsInclThis, precondOpt, retType, funSigScope, visibility, overridability, purity, isMain, declPosOpt, isSynthetic) = funSig
    pps.add(if isMain then "MAIN " else "")
      .add(s"METHOD ($visibility, $overridability, $purity, scope ${funSigScope.scopeUid}) $ownerName::$functionName${mkTypeParamsDescr(typeParams)}${mkFunctionParamsDescr(paramsInclThis, precondOpt)} -> $retType${mkPosDescr(declPosOpt)}")
    program.functions.get(funSig.ownerAndName)
      .flatMap(_.bodyOpt)
      .foreach { funBody =>
        pps.addSpace()
        printScope(funBody)
      }
  }

  private def printScope(scope: Scope)(using pps: PrettyPrintString): Unit = {
    pps.add(s"SCOPE").addSpace().add(scope.scopeUid).addSpace()
    if (scope.instructions.isEmpty) {
      pps.add("{ /* empty */ }")
    } else {
      pps.block {
        traverseIterable(scope.instructions.iterator) { instr =>
          printInstr(instr, scope)
        } {
          pps.newLine()
        }
      }
    }
  }

  private def printFields(fields: Iterable[(FunOrVarId, Field)])
                         (using pps: PrettyPrintString): Unit = {
    fields.size match {
      case 0 => ()
      case 1 =>
        val (_, fld) = fields.head
        pps.add("(").add(fld.toString).add(")")
      case _ =>
        pps.add("(").indentln {
          traverseIterable(fields.iterator) { (_, fld) =>
            pps.add(fld.toString)
          } {
            pps.add(",").newLine()
          }
        }.add(")")
    }
  }

  private def printInstr(instr: Instr, scope: Scope)(using pps: PrettyPrintString): Unit = {
    instr match {
      case SSA.Loop(cond, condVal, body, variables) =>
        pps.add("LOOP").indentln {
          pps.add(s"cond [as ${maybeTyped(condVal, scope)}]: ")
          printScope(cond)
          pps.newLine().add("body: ")
          printScope(body)
          pps.newLine()
          printVarData(variables) {
            case varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal, varDefScope) =>
              s"$varId: ${maybeTyped(beforeLoopVal, scope)} ; (${maybeTyped(condVal, cond)}) { ... ${maybeTyped(bodyLastVal, body)} } " ++ varData.recurDescr
          }
        }
        pps.add("END LOOP")
      case SSA.Disjunction(condVal, thenBr, elseBr, variables) =>
        pps.add("IF [cond = ").add(maybeTyped(condVal, scope)).add("]").indentln {
          pps.add("then: ")
          printScope(thenBr)
          pps.newLine().add("else: ")
          printScope(elseBr)
          pps.newLine()
          printVarData(variables) {
            case varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) =>
              varIdOpt.map(_.toString + ": ").getOrElse("") ++ s"${maybeTyped(joinedVal, scope)} := phi(${maybeTyped(afterThenVal, thenBr)}, ${maybeTyped(afterElseVal, elseBr)})"
          }
        }
        pps.add("END IF")
      case SSA.StaticTypeAssert(assertedValue, tpe) =>
        pps.add(s"TYPE-ASSERT ${maybeTyped(assertedValue, scope)} : $tpe")
      case AssignVal(assigned, src) =>
        pps.add(s"ASSIG ${maybeTyped(assigned, scope)} := $src")
      case AssignIntConst(assigned, src) =>
        pps.add(s"INTC ${maybeTyped(assigned, scope)} := $src")
      case AssignBoolConst(assigned, src) =>
        pps.add(s"BOOLC ${maybeTyped(assigned, scope)} := $src")
      case AssignStringConst(assigned, src) =>
        pps.add(s"STRINGC ${maybeTyped(assigned, scope)} := \"$src\"")
      case NumNeg(assigned, operand) =>
        pps.add(s"NEG ${maybeTyped(assigned, scope)} := -$operand")
      case Add(assigned, lhs, rhs) =>
        pps.add(s"ADD ${maybeTyped(assigned, scope)} := $lhs + $rhs")
      case Sub(assigned, lhs, rhs) =>
        pps.add(s"SUB ${maybeTyped(assigned, scope)} := $lhs - $rhs")
      case Mul(assigned, lhs, rhs) =>
        pps.add(s"MUL ${maybeTyped(assigned, scope)} := $lhs * $rhs")
      case Div(assigned, lhs, rhs) =>
        pps.add(s"DIV ${maybeTyped(assigned, scope)} := $lhs / $rhs")
      case Rem(assigned, lhs, rhs) =>
        pps.add(s"REM ${maybeTyped(assigned, scope)} := $lhs % $rhs")
      case LogicNeg(assigned, operand) =>
        pps.add(s"NOT ${maybeTyped(assigned, scope)} := !$operand")
      case And(assigned, lhs, rhs) =>
        pps.add(s"AND ${maybeTyped(assigned, scope)} := $lhs & $rhs")
      case Or(assigned, lhs, rhs) =>
        pps.add(s"OR ${maybeTyped(assigned, scope)} := $lhs | $rhs")
      case Equal(assigned, lhs, rhs) =>
        pps.add(s"EQ ${maybeTyped(assigned, scope)} := $lhs == $rhs")
      case Leq(assigned, lhs, rhs) =>
        pps.add(s"LEQ ${maybeTyped(assigned, scope)} := $lhs <= $rhs")
      case Lt(assigned, lhs, rhs) =>
        pps.add(s"LT ${maybeTyped(assigned, scope)} := $lhs < $rhs")
      case FieldRead(assigned, owner, field) =>
        pps.add(s"FIELD-RD ${maybeTyped(assigned, scope)} := $owner.$field")
      case HeapVarRead(assigned, heapVar) =>
        pps.add(s"HEAP-VAR-RD $assigned := *{$heapVar}")
      case InvokeFunc(assigned, receiver, func, typeArgs, args) =>
        pps.add(s"INVK-MTH ${maybeTyped(assigned, scope)} := $receiver.$func")
        printTypeArgsList(typeArgs)
        printArgsList(args)
      case InvokeClosure(assigned, callee, _, args) =>
        pps.add(s"INVK-CLOSURE ${maybeTyped(assigned, scope)} := $callee" ++ args.mkString("(", ",", ")"))
      case Instantiate(assigned, classOrRecordName, typeArgs, fieldsInit) =>
        pps.add(s"INSTANTIATE ${maybeTyped(assigned, scope)} := new $classOrRecordName" ++ fieldsInit.map((fldId, rhsVal) => s"$fldId := $rhsVal").mkString("(", ", ", ")"))
        printTypeArgsList(typeArgs)
      case MkClosure(assigned, params, body, declaredPure) =>
        val purityDescr = if declaredPure then " (pure)" else ""
        pps.add(s"MK-CLOSURE$purityDescr ${maybeTyped(assigned, scope)} := ").add(mkFunctionParamsDescr(params, precondOpt = None)).add(" ->").indent {
          pps.add("body: ")
          printScope(body)
        }
      case MkHeapVar(assigned) =>
        pps.add(s"MK-HEAP-VAR $assigned")
      case TypeTest(assigned, testedValue, testedTypeId) =>
        pps.add(s"TYPE-TEST ${maybeTyped(assigned, scope)} := $testedValue is $testedTypeId")
      case Conversion(assigned, inValue, targetType) =>
        pps.add(s"CONVERT ${maybeTyped(assigned, scope)} := $inValue as $targetType")
      case SSA.FieldWrite(owner, field, rhs) =>
        pps.add(s"FIELD-WR $owner.$field := ${maybeTyped(rhs, scope)}")
      case SSA.HeapVarWrite(heapVar, newValue) =>
        pps.add(s"HEAP-VAR-WR *{$heapVar} := ${maybeTyped(newValue, scope)}")
      case SSA.Return(retVal) =>
        pps.add(s"RET ${maybeTyped(retVal, scope)}")
      case SSA.Panic(msg) =>
        pps.add(s"PANIC ${maybeTyped(msg, scope)}")
      case SSA.Cast(inValue, target) =>
        pps.add(s"CAST ${maybeTyped(inValue, scope)} as $target")
      case hybridcast@SSA.HybridCast(inValue) =>
        val targetDescr = if hybridcast.isNonNullAssertion then "non-null" else hybridcast.getTargetRefinement.map(_.toString).getOrElse("<unspecified>")
        pps.add(s"HYBRIDCAST ${maybeTyped(inValue, scope)} to predicate $targetDescr")
      case SSA.Drop(droppedValue) =>
        pps.add(s"DROP ${maybeTyped(droppedValue, scope)}")
      case scope: Scope => printScope(scope)
      case SSA.LocalDecl(localId, tpe) =>
        pps.add(s"DECL-LOCAL $localId : $tpe")
      case SSA.Unreachable() =>
        pps.add("UNREACHABLE")
    }
    instr match {
      case assignInstr: AssigningInstr =>
        maybePrintCandidatesFor(assignInstr.assigned)
      case _ => ()
    }
  }

  private def maybeTyped(formula: Formula, scope: Scope): String = {
    val formulaStr = IRLevelFormulaPrinter.prettyprint(formula)
    val typeOpt = scope.typeOfNoSmartcastIfIdVal(formula).filter(_ => printTypes)
    typeOpt match {
      case Some(tpe) => s"$formulaStr : $tpe"
      case None => formulaStr
    }
  }

  private def maybePrintCandidatesFor(idValue: IdValue)(using pps: PrettyPrintString): Unit = {
    val candidates = typeCandidatesStore.getCandidates(idValue)
    if (candidates.nonEmpty) {
      pps.addAligned(s"// candidates: ", alignmentGranularity = commentsAlignmentGranularity)
      traverseIterable(candidates.iterator) { candidate =>
        pps.add(candidate.toString)
      } {
        pps.add(", ")
      }
    }
  }

  private def printTypeArgsList(typeArgs: List[Type])(using pps: PrettyPrintString): Unit = {
    if (typeArgs.nonEmpty) {
      pps.add("[")
      traverseIterable(typeArgs.iterator) { tArg =>
        pps.add(tArg)
      } {
        pps.add(",")
      }
      pps.add("]")
    }
  }

  private def printArgsList(args: List[IdValue])(using pps: PrettyPrintString): Unit = {
    pps.add("(")
    traverseIterable(args.iterator) { arg =>
      pps.add(arg)
    } {
      pps.add(",")
    }
    pps.add(")")
  }

  private def printVarData[D <: VarData](variables: Iterable[D])(mkString: D => String)(using pps: PrettyPrintString): Unit = {
    pps.add("variables: ")
    if (variables.isEmpty) {
      pps.add("<none>")
    } else {
      pps.indent {
        traverseIterable(variables.iterator) { varData =>
          pps.add(mkString(varData))
        } {
          pps.newLine()
        }
      }
    }
  }

  private def mkTypeParamsDescr(typeParams: Iterable[TypeParamInfo]): String =
    if typeParams.isEmpty then "" else typeParams.mkString("[", ",", "]")

  private def mkTypeAliasParamsDescr(params: Iterable[(FunOrVarId, (Types.Type, Formulas.IdValue))]): String =
    if params.isEmpty then "" else params.map {
      case (paramId, (paramType, paramVal)) =>
        s"$paramVal: $paramType"
    }.mkString("(", ", ", ")")

  private def mkFunctionParamsDescr(params: Iterable[(NamedIdValue, Type)], precondOpt: Option[Formula]): String =
    params.map { (idVal, tpe) =>
      s"$idVal: $tpe"
    }.mkString("(", ", ", "") ++ precondOpt.map(" | " + _).getOrElse("") + ")"

  private def mkSuperTypesDescr(supertypes: List[NamedType]): String =
    if supertypes.isEmpty then "" else s" extends ${supertypes.mkString(", ")}"

  private def mkPosDescr(posOpt: Option[Position]): String = posOpt match {
    case Some(pos) => s" at $pos"
    case None => ""
  }

  private def traverseIterable[T](iter: Iterator[T])(iterableDisplay: T => Unit)(step: => Unit): Unit = {
    while (iter.hasNext) {
      iterableDisplay(iter.next())
      if (iter.hasNext) {
        val _ = step
      }
    }
  }

  private def indent(str: String): String =
    str.lines()
      .map(indentUnit + _)
      .collect(Collectors.joining())

}
