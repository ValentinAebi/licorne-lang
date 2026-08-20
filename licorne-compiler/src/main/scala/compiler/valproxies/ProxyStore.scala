package compiler.valproxies

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.SSA.Scope
import compiler.irs.ssa.{FieldResolutionTarget, Formulas, InvocationTarget}
import compiler.lang.ClassSignature
import compiler.lang.Types.Type
import compiler.typing.Typer
import compiler.typing.contexts.{DealiasingContext, ResolutionContext}
import compiler.util.asIterableOfType

import scala.collection.mutable


final class ProxyStore {
  private val proxies = mutable.Map.empty[IdValue, Formula]
  private val loopProxies = mutable.Map.empty[IdValue, (beforeLoopVal: IdValue, endOfBodyVal: IdValue)]
  private val fieldAccessorProxies = mutable.Map.empty[TypeIdentifier, mutable.Set[FunOrVarId]]
  private val possiblyImpureClosures = mutable.Map.empty[IdValue, PureClosureValue]
  private val knownTypes = mutable.Map.empty[IdValue, TypeIdentifier]

  def hasProxyFor(idVal: IdValue): Boolean = proxies.contains(idVal)

  def saveProxy(idVal: IdValue, proxyOpt: Option[Formula]): Unit = proxyOpt.foreach { proxy =>
    saveProxy(idVal, proxy)
  }

  def saveProxy(idVal: IdValue, proxy: Formula): Unit = {
    if (proxies.contains(idVal)) {
      throw IllegalStateException(s"proxy already set for value $idVal")
    }
    proxies(idVal) = proxy
  }

  def saveLoopProxy(inCondVal: IdValue, beforeLoopVal: IdValue, endOfBodyVal: IdValue): Unit = {
    loopProxies(inCondVal) = (beforeLoopVal, endOfBodyVal)
  }

  def saveKnownType(idVal: IdValue, tid: TypeIdentifier): Unit = {
    knownTypes(idVal) = tid
  }

  def saveAccessorProxy(classId: TypeIdentifier, fldId: FunOrVarId): Unit = {
    fieldAccessorProxies.getOrElseUpdate(classId, mutable.Set.empty).addOne(fldId)
  }

  def savePossiblyImpureClosure(idVal: IdValue, closure: PureClosureValue): Unit = {
    possiblyImpureClosures.put(idVal, closure)
  }

  def validateClosurePurity(idVal: IdValue): Unit = {
    possiblyImpureClosures.get(idVal).foreach { closure =>
      proxies.put(idVal, closure)
    }
  }

  def accessorProxyFor(fld: FieldResolutionTarget)(using resolCtx: ResolutionContext): Option[InvocationTarget] = Option.when(fld.isResolvedAndPure) {
    fld.getReceiverSigOpt match {
      case Some(classSig: ClassSignature) =>
        for {
          fieldsSet <- fieldAccessorProxies.get(classSig.id)
          if fieldsSet.contains(fld.fieldId)
        } yield {
          val accessorSig = resolCtx.resolveFunSigNoSupertypeLookup(classSig.id, fld.fieldId).forceGetFunSig
          val invkTarget = InvocationTarget(fld.fieldId)
          invkTarget.resolve(classSig, accessorSig, fld.getInstantiatedTypeUnsafe)
          invkTarget
        }
      case _ => None
    }
  }.flatten

  def developDeep(formula: Formula, bypassPurityChecks: Boolean = false, acceptPhis: Boolean = false, allowConjunctsOmission: Boolean = false)(using ResolutionContext): Option[Formula] =
    dev(formula, developLocals = true, bypassPurityChecks, acceptPhis, allowConjunctsOmission)(using expandSelectIfAccessor)

  def developNearest(formula: Formula, bypassPurityChecks: Boolean = false, acceptPhis: Boolean = false, allowConjunctsOmission: Boolean = false)(using ResolutionContext): Option[Formula] =
    dev(formula, developLocals = false, bypassPurityChecks, acceptPhis, allowConjunctsOmission)(using expandSelectIfAccessor)

  def developDeepIgnoreAccessors(formula: Formula, bypassPurityChecks: Boolean = false, acceptPhis: Boolean = false, allowConjunctsOmission: Boolean = false): Option[Formula] =
    dev(formula, developLocals = true, bypassPurityChecks, acceptPhis, allowConjunctsOmission)(using Select(_, _))

  def developNearestIgnoreAccessors(formula: Formula, bypassPurityChecks: Boolean = false, acceptPhis: Boolean = false, allowConjunctsOmission: Boolean = false): Option[Formula] =
    dev(formula, developLocals = false, bypassPurityChecks, acceptPhis, allowConjunctsOmission)(using Select(_, _))

  // TODO memoize
  private def dev(formula: Formula, developLocals: Boolean, bypassPurityChecks: Boolean, acceptPhis: Boolean, allowConjunctsOmission: Boolean)
                 (using handleSelect: (rec: Formula, fld: FieldResolutionTarget) => Formula): Option[Formula] = {
    val stepRes: Option[Formula] = formula match {
      case idValue: (ParamIdValue | UninterpretedConstIdValue) => Some(idValue)
      case idValue: (ValIdValue | VarIdValue) if !developLocals => Some(idValue)
      case idValue: IdValue if proxies.contains(idValue) => Some(proxies.apply(idValue))
      case idValue: IdValue => None
      case cst: ConstFormula => Some(cst)
      case Select(owner, field) if bypassPurityChecks || field.isResolvedAndPure => for {
        owp <- dev(owner, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield handleSelect(owp, field)
      case FunCall(receiver, func, typeArgs, args) if bypassPurityChecks || func.isResolvedAndPure =>
        for {
          rcp <- dev(receiver, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
          argsp <- devAll(args, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        } yield FunCall(rcp, func, typeArgs, argsp)
      case ClosureCall(callee, closureTypingTarget, args) if bypassPurityChecks || closureTypingTarget.isResolvedAndPure =>
        for {
          clp <- dev(callee, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
          argsp <- devAll(args, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        } yield ClosureCall(clp, closureTypingTarget, argsp)
      case pureClosureValue: PureClosureValue => Some(pureClosureValue)
      case Plus(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        rp <- dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield Plus(lp, rp)
      case Neg(operand) => for {
        op <- dev(operand, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield Neg(op)
      case Times(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        rp <- dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield Times(lp, rp)
      case DivBy(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        rp <- dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield DivBy(lp, rp)
      case Modulo(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        rp <- dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield Modulo(lp, rp)
      case LogicalAnd(lhs, rhs) =>
        (dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission), dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)) match {
          case (Some(lp), Some(rp)) => Some(LogicalAnd(lp, rp))
          case (l, None) if allowConjunctsOmission => l
          case (None, r) if allowConjunctsOmission => r
          case _ => None
        }
      case LogicalNot(operand) => for {
        op <- dev(operand, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield LogicalNot(op)
      case LogicalOr(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        rp <- dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield LogicalOr(lp, rp)
      case Equality(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        rp <- dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield Equality(lp, rp)
      case LessOrEq(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        rp <- dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield LessOrEq(lp, rp)
      case LessThan(lhs, rhs) => for {
        lp <- dev(lhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
        rp <- dev(rhs, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield LessThan(lp, rp)
      case TypePredicate(subject, tpe) => for {
        sp <- dev(subject, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      } yield TypePredicate(sp, tpe)
      case Phi(terms) if terms.size == 1 => dev(terms.head, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      case Phi(terms) if acceptPhis =>
        val flattenedTermsOpt = terms.foldRight(Option(List.empty[Formula])) { (curr, accOpt) =>
          for {
            acc <- accOpt
            d <- dev(curr, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
          } yield flattenPhis(d) ++ acc
        }
        flattenedTermsOpt.map(Phi(_))
      case _ => None
    }
    (stepRes match {
      case Some(res) if res == formula => Some(res)
      case Some(res) => dev(res, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission)
      case None => None
    }).orElse {
      Option.when(formula.isInstanceOf[ValIdValue | VarIdValue]) {
        formula
      }
    }
  }

  def findInitializationTypesOf(origin: IdValue): Option[Iterable[TypeIdentifier]] = {
    val typeIds = mutable.HashSet.empty[TypeIdentifier]
    val front = mutable.Queue.empty[IdValue]
    val alreadyExplored = mutable.Set.empty[IdValue]

    def enqueue(idVal: IdValue): Unit = {
      if (alreadyExplored.add(idVal)) {
        front.enqueue(idVal)
      }
    }

    enqueue(origin)
    while (front.nonEmpty) {
      val curr = front.dequeue()
      knownTypes.get(curr) match {
        case Some(tid) =>
          typeIds.add(tid)
        case None =>
          loopProxies.get(curr) match {
            case Some((beforeLoopVal, endOfBodyVal)) =>
              enqueue(beforeLoopVal)
              enqueue(endOfBodyVal)
            case None =>
              proxies.get(curr) match {
                case Some(next: IdValue) if next != curr =>
                  enqueue(next)
                case Some(Phi(terms)) => terms.asIterableOfType[IdValue] match {
                  case Some(terms) =>
                    for (term <- terms) {
                      enqueue(term)
                    }
                  case None =>
                    return None
                }
                case _ =>
                  return None
              }
          }
      }
    }
    Some(typeIds.toList)
  }

  private def expandSelectIfAccessor(owp: Formula, field: FieldResolutionTarget)(using ResolutionContext): Formula = accessorProxyFor(field) match {
    case Some(invkTarget) => FunCall(owp, invkTarget, List.empty, List.empty)
    case None => Select(owp, field)
  }

  private def devAll(ls: List[Formula], developLocals: Boolean, bypassPurityChecks: Boolean, acceptPhis: Boolean, allowConjunctsOmission: Boolean)(using (rec: Formula, fld: FieldResolutionTarget) => Formula): Option[List[Formula]] = {
    ls.foldRight(Option(List.empty[Formula])) {
      case (curr, Some(acc)) => dev(curr, developLocals, bypassPurityChecks, acceptPhis, allowConjunctsOmission).map(_ :: acc)
      case _ => None
    }
  }

  private def flattenPhis(f: Formula): List[Formula] = f match {
    case Phi(terms) =>
      terms.toList.flatMap {
        case Phi(terms) => terms.flatMap(flattenPhis)
        case term => List(term)
      }
    case f => List(f)
  }

  def extractRawBranchingInfos(cond: IdValue, ambientBranchingInfo: BranchingInfo, outerScope: Scope)
                              (using typer: Typer, dealiasingCtx: DealiasingContext, resolCtx: ResolutionContext): (BranchingInfo, BranchingInfo) = {
    val (infoIfTrueNearest, infoIfFalseNearest) =
      developNearest(cond, allowConjunctsOmission = true).map(infosFor(_)(using outerScope))
        .getOrElse((BranchingInfo.empty, BranchingInfo.empty))
    val (infoIfTrueDeep, infoIfFalseDeep) =
      developDeep(cond).map(infosFor(_)(using outerScope))
        .getOrElse((BranchingInfo.empty, BranchingInfo.empty))
    (ambientBranchingInfo ++ infoIfTrueNearest ++ infoIfTrueDeep,
      ambientBranchingInfo ++ infoIfFalseNearest ++ infoIfFalseDeep)
  }

  def rawInfosFor(cond: Formula, outerScope: Scope)(using dealiasingCtx: DealiasingContext): (BranchingInfo, BranchingInfo) =
    infosFor(cond)(using outerScope)

  private def infosFor(cond: Formula)(using outerScope: Scope, dealiasingCtx: DealiasingContext): (BranchingInfo, BranchingInfo) = {
    cond match {
      case LogicalAnd(lhs, rhs) =>
        val (leftTrueInfos, leftFalseInfos) = infosFor(lhs)
        val (rightTrueInfos, rightFalseInfos) = infosFor(rhs)
        (leftTrueInfos ++ rightTrueInfos, BranchingInfo.empty)
      case LogicalOr(lhs, rhs) =>
        val (leftTrueInfos, leftFalseInfos) = infosFor(lhs)
        val (rightTrueInfos, rightFalseInfos) = infosFor(rhs)
        (BranchingInfo.empty, leftFalseInfos ++ rightFalseInfos)
      case LogicalNot(operand) =>
        val (operandTrueInfos, operandFalseInfos) = infosFor(operand)
        (operandFalseInfos, operandTrueInfos)
      // TODO maybe add a reference equality operator? or force overrides of equal to only work on two objects of exact same type
      case eq@Equality(lhs, rhs) =>
        (BranchingInfo.ofAssumption(eq), BranchingInfo.ofAssumption(LogicalNot(eq)))
      case leq@LessOrEq(lhs, rhs) =>
        (BranchingInfo.ofAssumption(leq), BranchingInfo.ofAssumption(LessThan(rhs, lhs)))
      case lt@LessThan(lhs, rhs) =>
        (BranchingInfo.ofAssumption(lt), BranchingInfo.ofAssumption(LessOrEq(rhs, lhs)))
      case TypePredicate(subject, tpe) =>
        (BranchingInfo.ofPositiveSmartcast(subject, tpe), BranchingInfo.ofNegativeSmartcast(subject, tpe))
      case cond => (BranchingInfo.ofAssumption(cond), BranchingInfo.ofAssumption(LogicalNot(cond)))
    }
  }

  override def toString: String = "ProxyStore {\n" ++ proxies.mkString("\n").indent(2) ++ "}"

}
