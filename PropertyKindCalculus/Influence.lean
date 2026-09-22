/-
# Influence — the disjunctive closure and the queries an assembled graph answers

`Provenance.reachableFrom` is the *conjunctive* closure — a result is derivable once ALL
its operands are — and it is what well-formedness needs. The questions asked *of* a
well-formed graph run the other way: whether a value carries onward through **some**
operand position, which is the *disjunctive* closure over the same ordered incidence.
This module states that closure executably, in both directions — forward
(`influencedFrom`: the descendants a change can touch) and backward (`ancestorsOf`: the
pedigree a value rests on) — and the query vocabulary each direction carries:

  * **the propagation relation of a contract** (`Contract.propagation`) — which of a
    boundary's source ports reach which of its produced ports through the authored
    occurrences, so an interface publishes how metrological information moves through it,
    not only what it takes and returns;
  * **sensitivity scoping** (`mayInfluence`, `confounded`) — vary an input iff the closure
    carries it to the output of interest. The soundness runs in the useful direction: an
    occurrence states that a value flows, never that a derivative is nonzero, so
    *presence* in the closure is a conservative candidate and *absence* is what licenses
    excluding a perturbation without silently dropping a real influence. Two inputs that
    both reach the output are confounded and are varied jointly;
  * **the budget term list** (`influencers`) — the sources among an output's ancestors:
    the term list of an uncertainty budget over these edges, and equally the source set
    whose attached conditions a downstream flag may claim (a flag claims only what some
    ancestor path proves);
  * **the per-output assumption ledger** (`assumptionLedger`) — the same set split by
    what each source *is*: the ports left open at the boundary, the gated ingests, the
    attested mints with their harvested reasons — the review surface per retrieved value;
  * **trust decomposition at the erasure boundary** (`trustSplit`) — the whole pedigree
    classified by which checker carries each node: kernel-checked derivations, byte-gate
    ingests, attested sources, and the exits the pedigree crosses;
  * **change-impact scoping** (`revalidationCone`, `changedNodes`, `impactedBy`) — the
    descendants of a changed source are the re-validation cone, and the comparison of two
    versions of a graph is the same query with the changed-node set computed rather than
    guessed: a node counts as changed when its declaration or its producing occurrences
    differ between the versions.

Everything here is prelude-only data and structural recursion, like the graph it reads:
each query is decided by evaluation in a probe and by kernel reduction in a proof. The
closures are fuel-bounded fixpoints saturating in one productive sweep per addable node,
exactly as `sweeps` argues for the conjunctive case; `acyclic` decides that no value
feeds its own derivation, the hypothesis under which paths through the incidence are
finitely many and a budget's sum over them is well formed.
-/

module

public import PropertyKindCalculus.Provenance

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

namespace Provenance

variable {ν κ : Type} [BEq ν] [BEq κ]

/-- The node vocabulary of a graph, in first-mention order: every node a port, an
introduction, an occurrence (operand or result), or an exit names. The closed universe a
finite reading of the graph — an index, a figure, the incidence quiver — enumerates. -/
def nodeList (g : Provenance ν κ) : List ν :=
  (g.ports.map (·.node) ++ g.intros.map (·.node)
    ++ g.occurrences.map (·.result)
    ++ (g.occurrences.flatMap fun o => o.operands.map (·.1))
    ++ g.exits).eraseDups

/-! ## The disjunctive closure, forward: influence -/

/-- One monotone sweep of the influence closure: each occurrence with **some** operand
known adds its result, in occurrence order. The disjunctive counterpart of `sweep`. -/
def influenceSweep (occs : List (Occurrence ν κ)) (ks : List ν) : List ν :=
  occs.foldl (init := ks) fun ks o =>
    if o.operands.any (fun oc => ks.contains oc.1) && !ks.contains o.result then
      ks ++ [o.result]
    else ks

/-- `fuel` influence sweeps from `ks`, stopping at the fixpoint — the disjunctive
counterpart of `sweeps`, with the same saturation argument: a sweep only appends, so a
sweep that adds nothing has finished, and each productive sweep adds at least one
occurrence result. -/
def influenceSweeps (occs : List (Occurrence ν κ)) : Nat → List ν → List ν
  | 0, ks => ks
  | fuel + 1, ks =>
    let ks' := influenceSweep occs ks
    if ks'.length == ks.length then ks else influenceSweeps occs fuel ks'

/-- The nodes a starting set can influence: the least fixpoint of "an occurrence with
SOME operand known makes its result known", including the start set itself. This is the
descendant set — the forward cone a change at `start` can touch. Fuel is one sweep per
occurrence *plus one*: at most one occurrence result is appendable per sweep that
produces anything, so the extra sweep is the one that observes saturation. -/
def influencedFrom (g : Provenance ν κ) (start : List ν) : List ν :=
  influenceSweeps g.occurrences (g.occurrences.length + 1) start

/-- Does `a` influence `b`: is `b` in the forward cone of `a`? Reflexive by convention —
a node trivially carries its own value. Presence is a conservative candidate (an
occurrence states that a value flows, not that a derivative is nonzero); absence is the
sound direction, licensing a perturbation study to exclude `a` for `b`. -/
def mayInfluence (g : Provenance ν κ) (a b : ν) : Bool :=
  (g.influencedFrom [a]).contains b

/-- Are two nodes confounded for an output: both reach it, so a perturbation study
varies them jointly rather than one at a time. -/
def confounded (g : Provenance ν κ) (out a b : ν) : Bool :=
  g.mayInfluence a out && g.mayInfluence b out

/-! ## The disjunctive closure, backward: pedigree -/

/-- The incidence reversed edge-by-edge: each occurrence becomes one unit occurrence per
operand position, wired from the result back to that operand. The backward closure is
then the forward closure over this list — one engine, both directions — and occurrence
multiplicity survives, since a repeated operand yields a reversed edge per position. -/
def reverseOccurrences (g : Provenance ν κ) : List (Occurrence ν κ) :=
  g.occurrences.flatMap fun o =>
    o.operands.map fun oc =>
      { family := .copy, operands := [(o.result, o.resultKind)], result := oc.1,
        resultKind := oc.2, site := o.site }

/-- The pedigree of a node set: everything it is derived from, including the set itself —
the ancestor set the backward closure reaches through the occurrences, computed as the
forward closure of the reversed incidence. -/
def ancestorsOf (g : Provenance ν κ) (of : List ν) : List ν :=
  influenceSweeps g.reverseOccurrences (g.reverseOccurrences.length + 1) of

/-- The sources among an output's ancestors: the budget's term list — where standard
uncertainties attach when the graph's edges carry a propagation law — and the source set
whose attached conditions a downstream flag may claim for this output. -/
def influencers (g : Provenance ν κ) (out : ν) : List ν :=
  let anc := g.ancestorsOf [out]
  g.sources.filter anc.contains

/-! ## The per-output ledgers -/

/-- The assumption ledger of one output: its influencing sources split by what each *is*.
The review surface per retrieved value — every port left open at the boundary, every
gated ingest, every attested mint with its harvested reason, that this output's value
rests on. -/
structure AssumptionLedger (ν κ : Type) where
  /-- The source ports among the ancestors — inputs, configuration, unbound parameters. -/
  ports : List (Port ν κ)
  /-- The gated ingests among the ancestors. -/
  gated : List ν
  /-- The attested mints among the ancestors, each with its harvested reason. -/
  attested : List (ν × String)
deriving Repr, Inhabited, BEq

/-- The assumption ledger of `out` (see `AssumptionLedger`). -/
def assumptionLedger (g : Provenance ν κ) (out : ν) : AssumptionLedger ν κ :=
  let anc := g.ancestorsOf [out]
  { ports := g.ports.filter fun p => !p.dir.produced && anc.contains p.node
    gated := (g.intros.filter fun i => i.tier == .gated && anc.contains i.node).map (·.node)
    attested := (g.intros.filterMap fun i =>
      match i.tier with
      | .attested reason => if anc.contains i.node then some (i.node, reason) else none
      | _ => none) }

/-- The trust decomposition of one output's pedigree: every ancestor classified by which
checker carries it — kernel-checked derivations, byte-gate ingests, attested sources —
plus the exits the pedigree crosses, where the byte gate rather than the type system
carries the claim onward. A per-output statement of what each part of the number rests
on. -/
structure TrustSplit (ν : Type) where
  /-- Ancestors introduced as `derived`: the kernel-checked segment. -/
  derived : List ν
  /-- Ancestors introduced as gated ingests: the byte-gate-carried segment. -/
  gated : List ν
  /-- Ancestors introduced as attested mints, with their harvested reasons. -/
  attested : List (ν × String)
  /-- Ancestors that are marked exits: where this pedigree hands off to the bare
  carrier. -/
  exited : List ν
deriving Repr, Inhabited, BEq

/-- The trust decomposition of `out` (see `TrustSplit`). -/
def trustSplit (g : Provenance ν κ) (out : ν) : TrustSplit ν :=
  let anc := g.ancestorsOf [out]
  { derived := (g.intros.filter fun i => i.tier == .derived && anc.contains i.node).map (·.node)
    gated := (g.intros.filter fun i => i.tier == .gated && anc.contains i.node).map (·.node)
    attested := g.intros.filterMap fun i =>
      match i.tier with
      | .attested reason => if anc.contains i.node then some (i.node, reason) else none
      | _ => none
    exited := g.exits.filter anc.contains }

/-! ## Change impact, within and across versions -/

/-- The re-validation cone of a changed node set: its descendants — every value a change
there can touch, hence everything whose validation the change reopens. -/
def revalidationCone (g : Provenance ν κ) (changed : List ν) : List ν :=
  g.influencedFrom changed

/-- The nodes at which two versions of a graph differ: declared differently (as a port
or an introduction), or produced differently (the occurrences resulting in the node are
not the same list). The comparison is exact on the shared node vocabulary — a rename is
a removal plus an addition, and both endpoints count as changed. -/
def changedNodes (g₁ g₂ : Provenance ν κ) : List ν :=
  let nodes := (g₁.ports.map (·.node) ++ g₁.intros.map (·.node) ++ g₁.exits
    ++ g₂.ports.map (·.node) ++ g₂.intros.map (·.node) ++ g₂.exits).eraseDups
  nodes.filter fun n =>
    g₁.ports.find? (·.node == n) != g₂.ports.find? (·.node == n)
      || g₁.intros.find? (·.node == n) != g₂.intros.find? (·.node == n)
      || g₁.occurrences.filter (·.result == n) != g₂.occurrences.filter (·.result == n)
      || g₁.exits.contains n != g₂.exits.contains n

/-- Diffable provenance: the re-validation cone, in the new version, of everything the
version step changed. The delta localizes to the rewired nodes and what they reach. -/
def impactedBy (g₁ g₂ : Provenance ν κ) : List ν :=
  g₂.revalidationCone (changedNodes g₁ g₂)

/-! ## The propagation relation of a contract -/

/-- The propagation relation of a declared boundary over an assembled graph: which
source ports reach which produced ports through the occurrences. This is what upgrades a
black-box signature to a metrological contract — the interface states not only the
kinds it takes and returns but how information moves between them. Pairs are listed in
declaration order, one per reachable (source, produced) pair. -/
def Contract.propagation (c : Contract ν κ) (g : Provenance ν κ) : List (ν × ν) :=
  let outs := (c.ports.filter (·.dir.produced)).map (·.node)
  (c.ports.filter fun p => !p.dir.produced).foldr (init := []) fun p acc =>
    let cone := g.influencedFrom [p.node]
    (outs.filter cone.contains).map (fun o => (p.node, o)) ++ acc

/-! ## Acyclicity -/

/-- The immediate successors of a node: the results of the occurrences it feeds. -/
def successors (g : Provenance ν κ) (n : ν) : List ν :=
  (g.occurrences.filter (fun o => o.operands.any (·.1 == n))).map (·.result)

/-- No value feeds its own derivation: no occurrence result re-reaches itself through
the incidence. Under this hypothesis the paths through the graph are finitely many, so a
sum over paths — a budget — is well formed. Only occurrence results can lie on a cycle,
so only they are checked. -/
def acyclic (g : Provenance ν κ) : Bool :=
  g.occurrences.all fun o => !(g.influencedFrom (g.successors o.result)).contains o.result

/-- `Prop`-level acyclicity, for statements and `decide`. -/
def Acyclic (g : Provenance ν κ) : Prop := g.acyclic = true

instance (g : Provenance ν κ) : Decidable g.Acyclic :=
  inferInstanceAs (Decidable (g.acyclic = true))

end Provenance

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
