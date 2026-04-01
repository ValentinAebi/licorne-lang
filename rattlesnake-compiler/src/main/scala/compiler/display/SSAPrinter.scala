package compiler.display

import compiler.identifiers.FunOrVarId
import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.lang.Formulas.{Formula, IdValue, NamedIdValue}
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.{ClassSignature, DatatypeSignature, Field, Formulas, FunctionSignature, InterfaceSignature, ObjectSignature, RecordSignature, TypeAliasSignature, TypeParamInfo, Types}
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Position
import compiler.valproxies.ProxyStore

import java.util.stream.Collectors

final class SSAPrinter(proxyStore: ProxyStore, indentUnit: String, printTypes: Boolean) extends CompilerStep[Program, String] {

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
    val TypeAliasSignature(id, typeParams, idValue, params, rhs, sigScope, declPosOpt) = typealiasSig
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
                           (using pps: PrettyPrintString): Unit = {
    val DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, sigScope, declPosOpt) = datatypeSig
    pps.add(s"DATATYPE (scope ${sigScope.scopeUid})").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
      .add(mkSuperTypesDescr(directSupertypes))
      .add(" with cases ")
    traverseIterable(directSubtypes.iterator) { subT =>
      pps.add(subT)
    } {
      pps.add(", ")
    }
    pps.add(mkPosDescr(declPosOpt)).newLine()
  }

  private def printRecord(recordSig: RecordSignature)
                         (using pps: PrettyPrintString): Unit = {
    val RecordSignature(id, typeParams, fields, directSupertypes, sigScope, declPosOpt) = recordSig
    pps.add(s"RECORD (scope ${sigScope.scopeUid})").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
    printFields(fields)
    pps.add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
      .newLine()
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
    val FunctionSignature(ownerName, functionName, typeParams, paramsInclThis, retType, funSigScope, visibility, declPosOpt) = funSig
    pps.add(s"METHOD ($visibility, scope ${funSigScope.scopeUid}) $ownerName::$functionName${mkTypeParamsDescr(typeParams)}${mkFunctionParamsDescr(paramsInclThis)} -> $retType${mkPosDescr(declPosOpt)}")
    program.functions.get(funSig)
      .flatMap(_.bodyOpt)
      .foreach { funBody =>
        pps.addSpace()
        printScope(funBody)
      }
  }

  private def printScope(scope: Scope)(using pps: PrettyPrintString): Unit = {
    pps.add(s"SCOPE").addSpace().add(scope.scopeUid).addSpace()
    val allEntries: Iterable[Instr | (Formula, Type)] = scope.getSmartcasts.toIndexedSeq ++ scope.instructions
    if (allEntries.isEmpty) {
      pps.add("{ /* empty */ }")
    } else {
      pps.block {
        traverseIterable(allEntries.iterator) {
          case (formula, tpe) =>
            pps.add(s"smartcast $formula : $tpe")
          case instr: Instr =>
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

  private def printInstr(instr: Instr, scope: Scope)(using pps: PrettyPrintString): Unit = instr match {
    case SSA.Loop(cond, condVal, body, variables) =>
      pps.add("LOOP").indentln {
        pps.add(s"cond [as ${maybeTyped(condVal, scope)}]: ")
        printScope(cond)
        pps.newLine().add("body: ")
        printScope(body)
        pps.newLine()
        printVarData(variables){
          case varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) =>
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
        printVarData(variables){
          case varData@DisjunctionVarData(varIdOpt, afterThenVal, afterElseVal, joinedVal) =>
            varIdOpt.map(_.toString + ": ").getOrElse("") ++ s"${maybeTyped(joinedVal, scope)} := phi(${maybeTyped(afterThenVal, thenBr)}, ${maybeTyped(afterElseVal, elseBr)})"
        }
      }
      pps.add("END IF")
    case SSA.StaticTypeAssert(value, tpe) =>
      pps.add(s"TYPE-ASSERT ${maybeTyped(value, scope)} : $tpe")
    case SSA.StaticAssert(value) =>
      pps.add(s"ASSERT ${maybeTyped(value, scope)}")
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
    case InvokeFunc(assigned, receiver, func, typeArgs, args) =>
      pps.add(s"INVK-MTH ${maybeTyped(assigned, scope)} := $receiver.$func")
      printTypeArgsList(typeArgs)
      printArgsList(args)
    case InvokeClosure(assigned, callee, args) =>
      pps.add(s"INVK-CLOS ${maybeTyped(assigned, scope)} := $callee")
    case Instantiate(assigned, classOrRecordName, typeArgs) =>
      pps.add(s"INSTANTIATE ${maybeTyped(assigned, scope)} := new $classOrRecordName")
      printTypeArgsList(typeArgs)
    case MkClosure(assigned, params, body) =>
      pps.add(s"MK-CLOS ${maybeTyped(assigned, scope)} := (").add(mkFunctionParamsDescr(params)).add(")").indent {
        pps.add("body: ")
        printScope(body)
      }
    case TypeTest(assigned, testedValue, testedTypeId) =>
      pps.add(s"TYPE-TEST ${maybeTyped(assigned, scope)} := $testedValue is $testedTypeId")
    case Conversion(assigned, inValue, targetType) =>
      pps.add(s"CONVERT ${maybeTyped(assigned, scope)} := $inValue as $targetType")
    case SSA.FieldWrite(owner, field, rhs) =>
      pps.add(s"FIELD-WR $owner.$field := ${maybeTyped(rhs, scope)}")
    case SSA.Return(retVal) =>
      pps.add(s"RET ${maybeTyped(retVal, scope)}")
    case SSA.Panic(msg) =>
      pps.add(s"PANIC ${maybeTyped(msg, scope)}")
    case SSA.Cast(inValue, target) =>
      pps.add(s"CAST ${maybeTyped(inValue, scope)} as $target")
    case SSA.Drop(droppedValue) =>
      pps.add(s"DROP ${maybeTyped(droppedValue, scope)}")
    case SSA.LocalDecl(localId, tpe) =>
      pps.add(s"DECL-LOCAL $localId : $tpe")
    case scope: Scope => printScope(scope)
  }

  private def maybeTyped(formula: Formula, scope: Scope): String =
    if printTypes then s"$formula : ${scope.currentTypeOf(formula)}" else formula.toString

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

  private def mkFunctionParamsDescr(params: Iterable[(NamedIdValue, Type)]): String =
    if params.isEmpty then "()" else params.map { (idVal, tpe) =>
      s"$idVal: $tpe"
    }.mkString("(", ", ", ")")

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
