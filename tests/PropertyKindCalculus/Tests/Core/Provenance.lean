/-
# Validation probes — `Provenance` (the metrological provenance hypergraph)

The module's claim is that well-formedness is decided by evaluation in a probe and by
kernel reduction in a proof, and that its central condition is the boundary audit's
"raw mints = 0" made compositional. The probes here judge exactly that, on hand-built
graphs small enough to read: a well-formed step passes (`#guard`, and `decide` for the
kernel route); then each structural condition is violated in isolation and the predicate
refuses the graph. The doctrine-bearing pair is the anonymous-mint flip: a `derived` node
no occurrence produces fails, and the *same* graph with the node re-introduced as
`attested` — the declared source carrying its one-line reason — passes. The cycle probe
pins the closure semantics: results of occurrences that only feed each other are not
reached, so "is the result of some occurrence" is not the condition — reachability from
the sources is.
-/
import PropertyKindCalculus.Provenance

namespace PropertyKindCalculus.Tests.Provenance

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (EdgeFamily)

/-! A two-occurrence step over string-named nodes and kinds: `x · y → z` interior, then
`z / y → out`, with the output erased at the exit. The shape of a harvested compute body:
inputs and output in the signature, one intermediate value, every kind reached through an
authored occurrence. -/

/-- The well-formed probe step. -/
def step : Provenance String String where
  ports := [
    ⟨"x", "alphaK", .input⟩,
    ⟨"y", "betaK", .input⟩,
    ⟨"out", "deltaK", .output⟩]
  intros := [⟨"z", "gammaK", .derived⟩]
  occurrences := [
    ⟨.product, [("x", "alphaK"), ("y", "betaK")], "z", "gammaK", "step"⟩,
    ⟨.quotient, [("z", "gammaK"), ("y", "betaK")], "out", "deltaK", "step"⟩]
  exits := ["out"]

#guard step.wellFormed

-- Forward reachability reaches exactly the declared nodes here, in discovery order.
#guard step.known == ["x", "y", "z", "out"]

/-! The kernel route: the checker is structural recursion over lists, so `decide`
reduces it in the kernel — a proof, not an evaluator run. Stated on a `Nat`-labelled
twin of `step` (kernel reduction of `Nat` equality is immediate, and a harvest is free
to choose such labels). -/

/-- `step` with numeric labels: nodes 0/1/2/3 for x/y/z/out, kinds 10/11/12/13. -/
def stepN : Provenance Nat Nat where
  ports := [⟨0, 10, .input⟩, ⟨1, 11, .input⟩, ⟨3, 13, .output⟩]
  intros := [⟨2, 12, .derived⟩]
  occurrences := [
    ⟨.product, [(0, 10), (1, 11)], 2, 12, "step"⟩,
    ⟨.quotient, [(2, 12), (1, 11)], 3, 13, "step"⟩]
  exits := [3]

example : stepN.WellFormed := by decide

/-! ## The anonymous-mint flip — "raw mints = 0", compositional

Delete the occurrence that derives `z`: now `z` is a `derived` node nothing produces —
an anonymous mint — and the graph is refused. Re-introduce the same node as an
`attested` source carrying its reason: the mint is on the record, and the graph passes.
The predicate distinguishes exactly what the boundary audit's suspect/reviewed split
distinguishes. -/

/-- `step` without the occurrence producing `z`: an anonymous mint. -/
def rawMint : Provenance String String :=
  { step with occurrences := step.occurrences.filter (fun o => !(o.result == "z")) }

#guard !rawMint.wellFormed

/-- The same graph with `z` attested — a declared source with its reason label. -/
def attestedSource : Provenance String String :=
  { rawMint with intros := [⟨"z", "gammaK", .attested "cited interior value, reviewed"⟩] }

#guard attestedSource.wellFormed

/-- A gated ingest is a source the same way: raw host data admitted through a check. -/
def gatedSource : Provenance String String :=
  { rawMint with intros := [⟨"z", "gammaK", .gated⟩] }

#guard gatedSource.wellFormed

/-! ## The closure semantics — a cycle licenses nothing

Two derived nodes, each the result of an occurrence consuming the other: every derived
node "is the result of some occurrence", yet neither is reachable from the sources, and
the graph is refused. Reachability from the sources, not per-node producedness, is the
condition. -/

/-- `a` and `b` derive each other; nothing derives either from a source. -/
def cycle : Provenance String String where
  ports := [⟨"x", "alphaK", .input⟩]
  intros := [⟨"a", "gammaK", .derived⟩, ⟨"b", "gammaK", .derived⟩]
  occurrences := [
    ⟨.product, [("b", "gammaK"), ("x", "alphaK")], "a", "gammaK", "cycle"⟩,
    ⟨.product, [("a", "gammaK"), ("x", "alphaK")], "b", "gammaK", "cycle"⟩]
  exits := []

#guard !cycle.wellFormed

/-! ## Each remaining condition, violated in isolation -/

-- An occurrence stating an operand kind the node's declaration does not state: an
-- occurrence cannot re-kind a node.
#guard !({ step with occurrences := [
  ⟨.product, [("x", "betaK"), ("y", "betaK")], "z", "gammaK", "step"⟩,
  step.occurrences[1]!] } : Provenance String String).wellFormed

-- An occurrence touching an undeclared node.
#guard !({ step with occurrences := [
  ⟨.product, [("ghost", "alphaK"), ("y", "betaK")], "z", "gammaK", "step"⟩,
  step.occurrences[1]!] } : Provenance String String).wellFormed

-- A product occurrence with one operand: the family's operand count is part of the
-- edge's type.
#guard !({ step with occurrences := [
  ⟨.product, [("x", "alphaK")], "z", "gammaK", "step"⟩,
  step.occurrences[1]!] } : Provenance String String).wellFormed

-- An occurrence deriving an *attested* node: a source's whole point is that its kind
-- is not derived, so a result may never land on one.
#guard !({ step with
  intros := [⟨"z", "gammaK", .attested "already a source"⟩] }
    : Provenance String String).wellFormed

-- An occurrence deriving an *input* port.
#guard !({ step with occurrences := [
  step.occurrences[0]!,
  ⟨.quotient, [("z", "gammaK"), ("y", "betaK")], "x", "alphaK", "step"⟩] }
    : Provenance String String).wellFormed

-- A node declared twice — as a port and as an introduction.
#guard !({ step with intros := step.intros ++ [⟨"x", "alphaK", .gated⟩] }
    : Provenance String String).wellFormed

-- An exit on a node the sources never reach.
#guard !({ cycle with exits := ["a"] } : Provenance String String).wellFormed

/-! ## Single-operand families, repeated operands, rendering -/

/-- A reciprocal chain: one operand, kinds reached through the closure as before. -/
def recipStep : Provenance String String where
  ports := [⟨"T", "periodK", .input⟩, ⟨"f", "frequencyK", .output⟩]
  intros := []
  occurrences := [⟨.reciprocal, [("T", "periodK")], "f", "frequencyK", "recipStep"⟩]
  exits := []

#guard recipStep.wellFormed

/-- A repeated operand is two incidence positions (`kx / kx` — the shape a set-valued
edge could not state): the same node fills numerator and denominator, and the graph is
well-formed. -/
def repeatedOperand : Provenance String String where
  ports := [⟨"q", "kx", .input⟩, ⟨"r", "fractionK", .output⟩]
  intros := []
  occurrences := [⟨.quotient, [("q", "kx"), ("q", "kx")], "r", "fractionK", "ratio"⟩]
  exits := []

#guard repeatedOperand.wellFormed

-- The renderer prints the enumeration commands' kind-equation grammar.
#guard EdgeFamily.product.render ["alphaK", "betaK"] "gammaK" == "alphaK · betaK → gammaK"
#guard EdgeFamily.reciprocal.render ["periodK"] "frequencyK" == "1 / periodK → frequencyK"
#guard (EdgeFamily.power (1/2)).render ["areaK"] "lengthK" == "areaK ^ 1/2 → lengthK"
#guard EdgeFamily.tableMul.render ["alphaK", "betaK"] "gammaK"
  == "[table] alphaK · betaK → gammaK"

end PropertyKindCalculus.Tests.Provenance
