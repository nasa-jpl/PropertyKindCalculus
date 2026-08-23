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
the sources is. The identity wire closes the file: a pass-through wired by `copy`
passes, and a kind-changing copy is refused by the one clause `wellFormed` owns
semantically.
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

-- The renderer prints the enumeration commands' kind-equation grammar — the power
-- exponent in the pretty printer's spelling of the authored literal (`^ 1 / 2`, `^ -1`,
-- `^ 3`), so an edge renders one way whether read off a witness type or carried as
-- edge data.
#guard EdgeFamily.product.render ["alphaK", "betaK"] "gammaK" == "alphaK · betaK → gammaK"
#guard EdgeFamily.reciprocal.render ["periodK"] "frequencyK" == "1 / periodK → frequencyK"
#guard (EdgeFamily.power (1/2)).render ["areaK"] "lengthK" == "areaK ^ 1 / 2 → lengthK"
#guard (EdgeFamily.power (-1)).render ["kx"] "ky" == "kx ^ -1 → ky"
#guard EdgeFamily.tableMul.render ["alphaK", "betaK"] "gammaK"
  == "[table] alphaK · betaK → gammaK"
#guard EdgeFamily.copy.render ["kx"] "kx" == "kx → kx"

/-! ## The identity wire — `copy`

A pass-through interface restates a node the wiring already has: the output port is the
input under a second name, and without an occurrence reaching it the port would read as
an anonymous mint. The `copy` family is that occurrence. Its claim is structural — the
same value under two names — so it is the one family whose equation `wellFormed` itself
checks: a copy that changes the kind is refused. -/

/-- A pass-through step: two ports, one identity wire, nothing else. -/
def passThrough : Provenance String String where
  ports := [⟨"tab", "kx", .input⟩, ⟨"result", "kx", .output⟩]
  intros := []
  occurrences := [⟨.copy, [("tab", "kx")], "result", "kx", "passThrough"⟩]
  exits := []

#guard passThrough.wellFormed

-- A kind-changing copy is refused even though every node carries its declared kind:
-- the identity wire must preserve the kind, and that clause — not the per-node typing —
-- is what rejects it.
#guard !({ ports := [⟨"tab", "kx", .input⟩, ⟨"result", "ky", .output⟩],
           intros := [],
           occurrences := [⟨.copy, [("tab", "kx")], "result", "ky", "passThrough"⟩],
           exits := [] } : Provenance String String).wellFormed

/-! ## The procedure edge — `step`, and the assembly combinators

A whole step applied as a hyperedge: its operand count is the interface's input count,
carried by the label, and its equation is licensed by the step's own graph — so the
structural checker enforces the arity and the node typing, never the equation. The
combinator probes build a two-box assembly by hand — namespaced levels, a `copy`
cross-wire, the callee's fed input demoted to a derived node — and the union checks. -/

-- The procedure edge renders with its name, inputs joined per the interface's count.
#guard (EdgeFamily.step "resample" 2).render ["kr", "kv"] "kv"
  == "[step resample] kr · kv → kv"
#guard (EdgeFamily.step "mint" 0).render [] "kv" == "[step mint] → kv"
#guard (EdgeFamily.step "resample" 2).operandCount == 2

/-- A signature box: the output derived from the input through the step's own
procedure edge. -/
def procBox : Provenance String String where
  ports := [⟨"x", "kx", .input⟩, ⟨"result", "ky", .output⟩]
  intros := []
  occurrences := [⟨.step "procBox" 1, [("x", "kx")], "result", "ky", "procBox"⟩]
  exits := []

#guard procBox.wellFormed

-- A procedure edge at the wrong arity is refused by the family's operand count.
#guard !({ procBox with occurrences :=
  [⟨.step "procBox" 2, [("x", "kx")], "result", "ky", "procBox"⟩] }
    : Provenance String String).wellFormed

-- `mapNodes` renames every incidence; `mapKinds` is the monomorphization map.
#guard (procBox.mapNodes ("A/" ++ ·)).occurrences
  == [⟨.step "procBox" 1, [("A/x", "kx")], "A/result", "ky", "procBox"⟩]
#guard ((procBox.mapKinds fun k => if k == "kx" then "alphaK" else k).ports.map (·.kind))
  == ["alphaK", "ky"]

/-- The hand-built assembly: caller box `A` calling `procBox` as `B` — the caller's
operand cross-wired onto `B`'s demoted input, `B`'s own procedure edge deriving its
output, the caller's procedure edge standing as the call's derivation. -/
def assembled : Provenance String String :=
  let A : Provenance String String :=
    { ports := [⟨"x", "kx", .input⟩, ⟨"result", "ky", .output⟩]
      intros := []
      occurrences := [⟨.step "B" 1, [("x", "kx")], "result", "ky", "A"⟩]
      exits := [] }
  let B : Provenance String String :=
    { ports := [⟨"result", "ky", .output⟩]
      intros := [⟨"x", "kx", .derived⟩]  -- the fed input, demoted
      occurrences := [⟨.step "B" 1, [("x", "kx")], "result", "ky", "B"⟩]
      exits := [] }
  let wires : Provenance String String :=
    ⟨[], [], [⟨.copy, [("A/x", "kx")], "B/x", "kx", "A"⟩], []⟩
  ((A.mapNodes ("A/" ++ ·)).union (B.mapNodes ("B/" ++ ·))).union wires

#guard assembled.wellFormed

-- Un-wired, the demoted input is an anonymous mint and the union is refused: the
-- cross-wire is load-bearing, not decoration.
#guard !({ assembled with
  occurrences := assembled.occurrences.filter (fun o => !(o.family matches .copy)) }
    : Provenance String String).wellFormed

end PropertyKindCalculus.Tests.Provenance
