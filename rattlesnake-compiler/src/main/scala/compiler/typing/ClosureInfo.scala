package compiler.typing

import compiler.irs.SSA.Scope
import compiler.lang.Formulas.ParamIdValue
import compiler.lang.Types.{Type, TypeVariable}
import compiler.typing.contexts.TypeParamsContext
import compiler.valproxies.BranchingInfo

final case class ClosureInfo(
                              params: List[(ParamIdValue, Type)],
                              body: Scope,
                              retTypeVar: TypeVariable,
                              branchingInfo: BranchingInfo,
                              typeParamsCtx: TypeParamsContext
                            )
