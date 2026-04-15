package compiler.typing

import compiler.irs.SSA.Scope
import compiler.lang.Formulas.ParamIdValue
import compiler.lang.{ExecutionEnvironment, FunctionSignature}
import compiler.lang.Types.{Type, TypeVariable}
import compiler.typing.contexts.TypeParamsContext
import compiler.valproxies.BranchingInfo

final case class ClosureInfo(
                              params: List[(ParamIdValue, Type)],
                              body: Scope,
                              retTypeVar: TypeVariable,
                              branchingInfo: BranchingInfo,
                              containingEnvir: ExecutionEnvironment,
                              typeParamsCtx: TypeParamsContext
                            ) extends ExecutionEnvironment {
  private var purityFlag = false
  
  def raisePurityFlag(): Unit = {
    purityFlag = true
  }

  override def expectedResultType: Type = retTypeVar

  override def requiresPurityInBody: Boolean = purityFlag

  override def root: FunctionSignature = containingEnvir.root
}
