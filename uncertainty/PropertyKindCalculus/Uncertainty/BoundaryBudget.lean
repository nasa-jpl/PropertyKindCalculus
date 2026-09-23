/-
# The budget at the boundary — `influencers` as the term list it names

`Influence.influencers` computes, for a produced port, the sources among its ancestors
through the authored occurrences — and names itself "the term list of an uncertainty
budget". This module is where that name is cashed: a `PortBudget` attaches a GUM-style
term list to one produced port of a declared boundary, and `#kind_budget` checks the
attachment against the assembled graph — the first join of the uncertainty stack and the
`Provenance` stack.

What the join asserts, and what it does not:

  * **each term is an influencing source.** A budget term names a source node of the
    boundary's graph that actually reaches the port through the occurrences — a term
    that does not influence the output is not a term of its budget, and is refused;
  * **the sum is well formed.** A budget sums one contribution per *path-reachable
    source*, so the graph must be acyclic — `Provenance.acyclic` is exactly the
    hypothesis under which paths through the incidence are finitely many
    (`Influence.lean`, header). A cyclic assembly is refused before any term is read;
  * **the combined value is computed, not stored.** `PortBudget.combined` is the
    quadrature `√(Σ uᵢ²)` of the terms, through the budget layer's own `combinedQ` —
    a stored copy could drift from its terms;
  * **coverage is what the sum is for.** A combined standard uncertainty scaled by a
    coverage factor is a `Quantity` at the port's kind — exactly what a `boundedBy`
    relation names as its tolerance (`Coverage.coverageBound_stdUnc` is the
    distribution-free floor a factor `k` buys). The worked Water-Cloud module declares
    that tolerance beside its budget;
  * **what the budget does not carry is reported, not hidden.** The sources that
    influence the port and appear in no term — a calibration constant carried without
    uncertainty, an attested mint — render as `unbudgeted source(s)`, so the report
    names the uncertainty the model is *not* propagating.

The attachment object is reference-addressed data, exactly as `Provenance.Contract` is:
the kinded truth (which contribution is at which kind, through which `ProductKind` gate)
lives in the declarations that computed the magnitudes (`Budget.contributionQ`,
`Sensitivity.gradient`), and the attachment records their result at the boundary where a
reader looks for it.
-/

module

public import PropertyKindCalculus.Influence
public meta import PropertyKindCalculus.Influence
public import PropertyKindCalculus.KindIncidence
public meta import PropertyKindCalculus.KindIncidence
public import PropertyKindCalculus.Uncertainty.Budget
public import PropertyKindCalculus.Uncertainty.Carriers

-- Same-module helpers serve both the command elaborators below and runtime callers, so the
-- phase check is relaxed for this file (the module system's mixed-use escape; imports are
-- still checked and take `public meta import`).
set_option compiler.relaxedMetaCheck true

@[expose] public section Blanket

namespace PropertyKindCalculus.Uncertainty

open Lean Meta
open PropertyKindCalculus
open PropertyKindCalculus.KindIncidence (contractValueOf assembleContract)

/-- **A budget attached to a produced port** of a declared boundary: the port, the kind
its combined uncertainty is stated at (the port's own kind), and the term list — one
influencing source node per entry, with the magnitude of its output-kind contribution
`uᵢ(y) = |cᵢ|·u(xᵢ)`. Reference-addressed data, like the contract it attaches to; the
kinded formation of each magnitude is the business of the declarations that computed it
(`Budget.contributionQ` — the `ProductKind kₛ kᵢ kₒ` gate — fed by autograd
sensitivities and the inputs' moments). -/
structure PortBudget where
  /-- The produced port the budget attaches to, as the contract references it. -/
  port : Provenance.NodeId
  /-- The kind the contributions and the combined uncertainty are stated at — checked
  to be the port's kind. -/
  kind : Provenance.KindRef
  /-- The term list: each influencing source node with its output-kind contribution
  magnitude. -/
  terms : List (Provenance.NodeId × Float)
deriving Repr, Inhabited, BEq

/-- **The combined standard uncertainty of the attachment** — the quadrature
`√(Σ uᵢ²)` of the terms, through the budget layer's own `combinedQ` (the kind index
erases, `combinedQ_magnitude`, so the attachment's kind is read as a ratio kind at its
rendering for the fold and contributes nothing to the value). Computed, never stored: a
stored copy could drift from its terms. -/
def PortBudget.combined (b : PortBudget) : Float :=
  (combinedQ (kO := { id := b.kind.render, scale := .ratio })
    (b.terms.map fun t =>
      (⟨t.2⟩ : Quantity { id := b.kind.render, scale := .ratio } Float))).magnitude

private unsafe def evalPortBudgetUnsafe (e : Expr) : MetaM PortBudget :=
  Meta.evalExpr PortBudget (mkConst ``PortBudget) e

/-- The declared budget's value, for checking and rendering. Replaced at run time by
the evaluator; the safe body stands only where no evaluator is available, and no
proposition rests on it. -/
@[implemented_by evalPortBudgetUnsafe]
def evalPortBudget (_e : Expr) : MetaM PortBudget :=
  throwError "port-budget values cannot be read in this environment"

/-- The declared budget's value, with the type check that gives a legible error before
the evaluator is asked for one. -/
def portBudgetValueOf (bname : Name) : MetaM PortBudget := do
  unless ← Meta.isDefEq (← Meta.inferType (mkConst bname)) (mkConst ``PortBudget) do
    throwError "'{bname}' is not a 'PortBudget'"
  evalPortBudget (mkConst bname)

open Elab Command in
/-- `#kind_budget b c` — check the attachment of the budget `b` to the boundary `c` and
render it: the port must be a *produced* port of `c` at the budget's stated kind; the
assembly of `c` must be acyclic (path-finiteness is the well-formedness of the sum);
every term must name a source that influences the port (`Provenance.influencers` — the
term list of an uncertainty budget, by its own name); and the influencing sources the
budget does not carry render as `unbudgeted source(s)`, so what the model is not
propagating is in the report rather than absent from it. The combined line is the
quadrature of the terms, computed. A single `info` message suitable for `#guard_msgs`
pinning; every violation throws, so the command is the report and the gate at once. -/
elab "#kind_budget " b:ident c:ident : command => liftTermElabM do
  let bname ← realizeGlobalConstNoOverload b
  let bud ← portBudgetValueOf bname
  let cname ← realizeGlobalConstNoOverload c
  let ctr ← contractValueOf cname
  let some p := ctr.ports.find? (·.node == bud.port)
    | throwError "the budget '{bname}' names '{bud.port.render}', which is no port of \
        '{ctr.name}'"
  unless p.dir.produced do
    throwError "the budget '{bname}' names a port with role '{p.dir.label}' — a \
      budget attaches to what the boundary produces"
  unless p.kind == bud.kind do
    throwError "the budget for '{bud.port.render}' is stated at kind \
      '{bud.kind.render}', but the port produces '{p.kind.render}' — contributions and \
      combined uncertainty are quantities at the port's own kind"
  let a ← assembleContract ctr
  let g := a.graph
  unless g.acyclic do
    throwError "the assembly of '{ctr.name}' is cyclic — paths through the incidence \
      are not finitely many, so a budget's sum over them is not well formed"
  let infl := g.influencers bud.port
  for (n, _) in bud.terms do
    unless infl.contains n do
      throwError "the budget term '{n.render}' does not influence '{bud.port.render}' \
        in '{ctr.name}' — a term of the sum must be a source among the port's ancestors"
  let unbudgeted := infl.filter fun n => !(bud.terms.any (·.1 == n))
  let mut lines : Array String :=
    #[s!"budget for '{bud.port.render}' : {bud.kind.render} on '{ctr.name}': \
      {bud.terms.length} term(s) over {infl.length} influencing source(s)"]
  for (n, u) in bud.terms do
    lines := lines.push s!"  term {n.render}: {u}"
  lines := lines.push s!"  combined: {bud.combined}"
  unless unbudgeted.isEmpty do
    lines := lines.push
      s!"  unbudgeted source(s): \
        {String.intercalate ", " (unbudgeted.map (·.render))}"
  logInfo m!"{String.intercalate "\n" lines.toList}"

end PropertyKindCalculus.Uncertainty

end Blanket
