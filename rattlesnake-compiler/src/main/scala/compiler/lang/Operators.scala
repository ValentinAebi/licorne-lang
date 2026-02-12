package compiler.lang

import Formulas.{Equal, IdValue, IntConstant, Not}
import Operator.*
import Types.PrimitiveType.*
import Types.Type
import compiler.identifiers.{ItId, TypeIdentifier}

import scala.annotation.targetName

object Operators {

  sealed trait OperatorSignature {
    def op: Operator

    def retType: Type
  }

  /**
   * Signature of an unary operator
   */
  final case class UnaryOpSignature(op: Operator, operandType: Type, retType: Type)
    extends OperatorSignature {
    override def toString: String = s"$op: ($operandType) -> $retType"
  }

  /**
   * Signature of a binary operator
   */
  final case class BinaryOpSignature(leftOperandType: Type, op: Operator, rightOperandType: Type, retType: Type)
    extends OperatorSignature {
    override def toString: String = s"$leftOperandType $op $rightOperandType -> $retType"
  }

  private val nzi$it = new IdValue {
    override def completeDescr: String = "nzi$it"

    override def sourceLevelDescrOrDefault: String = completeDescr
  }
  
  private val nonZeroInt = IntType  // FIXME use refinements
  // TODO also NonZeroDouble for / and % on Doubles?

  val unaryOperators: List[UnaryOpSignature] = List(
    UnaryOpSignature(Minus, IntType, IntType),
    UnaryOpSignature(Minus, DoubleType, DoubleType),
    UnaryOpSignature(ExclamationMark, BoolType, BoolType)
  )

  //  ==  and  !=  are treated separately
  val binaryOperators: List[BinaryOpSignature] = List(

    IntType $ Plus $ IntType is IntType,
    DoubleType $ Plus $ DoubleType is DoubleType,
    IntType $ Minus $ IntType is IntType,
    DoubleType $ Minus $ DoubleType is DoubleType,
    IntType $ Times $ IntType is IntType,
    DoubleType $ Times $ DoubleType is DoubleType,
    IntType $ Div $ nonZeroInt is IntType,
    DoubleType $ Div $ DoubleType is DoubleType,
    IntType $ Modulo $ nonZeroInt is IntType,

    IntType $ LessThan $ IntType is BoolType,
    DoubleType $ LessThan $ DoubleType is BoolType,
    IntType $ LessOrEq $ IntType is BoolType,
    DoubleType $ LessOrEq $ DoubleType is BoolType,
    IntType $ GreaterThan $ IntType is BoolType,
    DoubleType $ GreaterThan $ DoubleType is BoolType,
    IntType $ GreaterOrEq $ IntType is BoolType,
    DoubleType $ GreaterOrEq $ DoubleType is BoolType,

    BoolType $ And $ BoolType is BoolType,
    BoolType $ Or $ BoolType is BoolType,

    StringType $ Plus $ StringType is StringType
  )

  val assigOperators: Map[Operator, Operator] = Map(
    PlusEq -> Plus,
    MinusEq -> Minus,
    TimesEq -> Times,
    DivEq -> Div,
    ModuloEq -> Modulo
  )


  // Binop signature DSL implementation --------------------------------------------

  private case class PartialBinop1(leftOperandType: Type, op: Operator) {
    @targetName("andThen") infix def $(rightOperandType: Type): PartialBinop2 = {
      PartialBinop2(leftOperandType, op, rightOperandType)
    }
  }

  private case class PartialBinop2(leftOperandType: Type, op: Operator, rightOperandType: Type) {
    infix def is(retType: Type): BinaryOpSignature = {
      BinaryOpSignature(leftOperandType, op, rightOperandType, retType)
    }
  }

  extension (leftOperandType: Type) {
    @targetName("andThen") private infix def $(op: Operator): PartialBinop1 = {
      PartialBinop1(leftOperandType, op)
    }
  }

}
