/-
# Validation probes — the budget at the boundary

`#kind_budget` joins the uncertainty stack to the `Provenance` stack: a `PortBudget`
attaches a term list to one produced port, and the command checks the attachment against
the assembled graph — every term an influencing source, the port produced and at the
stated kind, the assembly acyclic. The probes ride the guarded-chain fixtures of
`Tests/Core/KindIncidence.lean`, whose conditional port has exactly one influencing
source (`halvedInDomain/q` — the guard's bound `lo` gates the case but feeds no
occurrence, so influence correctly excludes it). The acceptance pin budgets that
source; the empty budget pins the `unbudgeted source(s)` line — the report names what
a model is not propagating rather than omitting it; and each hygiene check has a
refusal probe.
-/
import PropertyKindCalculus.Uncertainty.BoundaryBudget
import PropertyKindCalculus.Tests.Core.KindIncidence

namespace PropertyKindCalculus.Tests.BoundaryBudget

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)
open PropertyKindCalculus.Tests.KindIncidence (halvedInDomainBoundary)

/-- The guarded chain's budget: one term for the one source that influences the
conditional output through the occurrences. -/
def halvedBudget : Uncertainty.PortBudget :=
  { port := (NodeId.result.field "some").within ``KindIncidence.halvedInDomain
    kind := .decl ``KindIncidence.epsilonK
    terms := [((NodeId.binder "q").within ``KindIncidence.halvedInDomain, 0.5)] }

/--
info: budget for 'halvedInDomain/result.some' : epsilonK on 'halvedInDomain': 1 term(s) over 1 influencing source(s)
  term halvedInDomain/q: 0.500000
  combined: 0.500000
-/
#guard_msgs (whitespace := lax) in #kind_budget halvedBudget halvedInDomainBoundary

/-- The empty budget: attaches, and every influencing source renders as unbudgeted —
the honest form of "no uncertainty is propagated to this port". -/
def halvedBudgetEmpty : Uncertainty.PortBudget :=
  { halvedBudget with terms := [] }

/--
info: budget for 'halvedInDomain/result.some' : epsilonK on 'halvedInDomain': 0 term(s) over 1 influencing source(s)
  combined: 0.000000
  unbudgeted source(s): halvedInDomain/q
-/
#guard_msgs (whitespace := lax) in #kind_budget halvedBudgetEmpty halvedInDomainBoundary

/-- A term that influences nothing: not a node of the graph at all. -/
def budgetTermUninfluential : Uncertainty.PortBudget :=
  { halvedBudget with
    terms := [((NodeId.binder "nothing").within ``KindIncidence.halvedInDomain, 0.5)] }

/--
error: the budget term 'halvedInDomain/nothing' does not influence 'halvedInDomain/result.some' in 'halvedInDomain' — a term of the sum must be a source among the port's ancestors
-/
#guard_msgs in #kind_budget budgetTermUninfluential halvedInDomainBoundary

/-- A budget hung on an input: a source carries no combined uncertainty of the module. -/
def budgetOnAnInput : Uncertainty.PortBudget :=
  { halvedBudget with
    port := (NodeId.binder "lo").within ``KindIncidence.halvedInDomain
    kind := .decl ``KindEdges.alphaK }

/--

error: the budget 'PropertyKindCalculus.Tests.BoundaryBudget.budgetOnAnInput' names a port with role 'input' — a budget attaches to what the boundary produces
-/
#guard_msgs in #kind_budget budgetOnAnInput halvedInDomainBoundary

/-- A budget stated at the wrong kind: the contributions would not be quantities of
what the port produces. -/
def budgetAtTheWrongKind : Uncertainty.PortBudget :=
  { halvedBudget with kind := .decl ``KindEdges.alphaK }

/--

error: the budget for 'halvedInDomain/result.some' is stated at kind 'alphaK', but the port produces 'epsilonK' — contributions and combined uncertainty are quantities at the port's own kind
-/
#guard_msgs in #kind_budget budgetAtTheWrongKind halvedInDomainBoundary

/-- A budget naming no port of the boundary. -/
def budgetOnNoPort : Uncertainty.PortBudget :=
  { halvedBudget with
    port := (NodeId.binder "zzz").within ``KindIncidence.halvedInDomain }

/--

error: the budget 'PropertyKindCalculus.Tests.BoundaryBudget.budgetOnNoPort' names 'halvedInDomain/zzz', which is no port of 'halvedInDomain'
-/
#guard_msgs in #kind_budget budgetOnNoPort halvedInDomainBoundary

end PropertyKindCalculus.Tests.BoundaryBudget
