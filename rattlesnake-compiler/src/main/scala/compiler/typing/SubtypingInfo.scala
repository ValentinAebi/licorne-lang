package compiler.typing

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.typing.contexts.SubtypingContext.SupertypesSubst

final case class SubtypingInfo(
                                subtypingGraph: Graph[TypeIdentifier],
                                flattenedSupertypesSubstitutions: SupertypesSubst
                              )
