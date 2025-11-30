package lang

import identifiers.TypeIdentifier
import lang.Operator.*
import lang.Types.BaseType
import lang.Types.PrimitiveType.*

import scala.annotation.targetName

object Operators {

  // Operators do not work on structs, hence the empty struct mapping
  private given Map[TypeIdentifier, StructSignature] = Map.empty

  sealed trait OperatorSignature {
    def op: Operator

    def retType: BaseType
  }

  /**
   * Signature of an unary operator
   */
  final case class UnaryOpSignature(op: Operator, operandType: BaseType, retType: BaseType)
    extends OperatorSignature

  /**
   * Signature of a binary operator
   */
  final case class BinaryOpSignature(leftOperandType: BaseType, op: Operator, rightOperandType: BaseType, retType: BaseType)
    extends OperatorSignature

  // # is treated separately
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
    IntType $ Div $ IntType is IntType,
    DoubleType $ Div $ DoubleType is DoubleType,
    IntType $ Modulo $ IntType is IntType,

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

  private case class PartialBinop1(leftOperandType: BaseType, op: Operator) {
    @targetName("andThen") infix def $(rightOperandType: BaseType): PartialBinop2 = {
      PartialBinop2(leftOperandType, op, rightOperandType)
    }
  }

  private case class PartialBinop2(leftOperandType: BaseType, op: Operator, rightOperandType: BaseType) {
    infix def is(retType: BaseType): BinaryOpSignature = {
      BinaryOpSignature(leftOperandType, op, rightOperandType, retType)
    }
  }

  extension (leftOperandType: BaseType) {
    @targetName("andThen") private infix def $(op: Operator): PartialBinop1 = {
      PartialBinop1(leftOperandType, op)
    }
  }

}
