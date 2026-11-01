/-
# Validation probes — the seal of the computation on a recorded tape (capstone 2)

The bisimulation probes (`Tests.Graph.Bisimulation`) decide a match between an authored
hypergraph, `y = a · b + e`, and an authored tape graph. This module closes the loop with the
recorder: the same expression, instantiated at the complex carrier over the recording carrier,
is recorded, compacted, and projected onto its computational tape graph — which is, vertex
for vertex, the graph the bisimulation probes accept once its vertices are numbered in the
recorder's order. The match on the recorded graph is decided by the kernel, the cone lemma
and the seal of the computation are instantiated on it, and the recorded values are checked
against the seal's value clause at runtime: two environments that agree on the influencers
give the same value at both parts of `y`.

The projection `ofTape t == T` is a runtime check (the tape's stored tensors are opaque to
the kernel); the match's acceptance on `T`, and every theorem applied to it, is a kernel
theorem.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeSeal
meta import PropertyKindCalculus.Torch.Paradigm.TapeSeal
public import PropertyKindCalculus.Complex
meta import PropertyKindCalculus.Complex
public import PropertyKindCalculus.Tests.Graph.Bisimulation
meta import PropertyKindCalculus.Tests.Graph.Bisimulation

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.TapeSeal

open Spec TorchLean
open Runtime.Autograd (Tape Node TapeM)
open PropertyKindCalculus
open PropertyKindCalculus.Paradigm (TapeBuilder TapeGraph TapeVertex Match Realized)
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape evalTape WF)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Paradigm.TapeSeal
open PropertyKindCalculus.Tests.Bisimulation (g g_wellFormed)

abbrev TB := TapeBuilder Shape.scalar

/-- A named input leaf at the recording carrier. -/
def inLeaf (nm : String) : TB :=
  ⟨TapeM.leaf (Tensor.full Shape.scalar (0.0 : Float)) (name := some nm)⟩

/-- The two complex inputs and the baked complex offset. -/
def a : Complex TB := ⟨inLeaf "a.re", inLeaf "a.im"⟩
def b : Complex TB := ⟨inLeaf "b.re", inLeaf "b.im"⟩
def e : Complex TB := ⟨TapeBuilder.const 1.5, TapeBuilder.const 2.0⟩

/-- The module: `y = a · b + e`, at the complex carrier over the recording carrier. -/
def y : Complex TB := a * b + e

/-- Record both parts of `y` on one tape and compact it. -/
def recorded : Except String (Tape Float × Nat × Nat) := do
  let ((r, i), t) ← TapeM.run Tape.empty (do
    let r ← y.re.run
    let i ← y.im.run
    pure (r, i))
  let (t', remap) := cseCompact t
  pure (t', remap.getD r r, remap.getD i i)

/-- The compacted tape's graph, as the recorder numbers it: `a.re`, `b.re`, their product,
`a.im`, `b.im`, their product, the difference `c.re`, the offset's real part, `y.re`; then
the two cross products, their sum `c.im`, the offset's imaginary part, `y.im`. -/
def T : TapeGraph := ⟨[
  ⟨some "a.re", []⟩, ⟨some "b.re", []⟩, ⟨some "mul", [0, 1]⟩,     -- 0, 1, 2 = ac
  ⟨some "a.im", []⟩, ⟨some "b.im", []⟩, ⟨some "mul", [3, 4]⟩,     -- 3, 4, 5 = bd
  ⟨some "sub", [2, 5]⟩, ⟨none, []⟩, ⟨some "add", [6, 7]⟩,        -- 6 = c.re, 7 = e.re, 8 = y.re
  ⟨some "mul", [0, 4]⟩, ⟨some "mul", [3, 1]⟩, ⟨some "add", [9, 10]⟩, -- 9 = ad, 10 = bc, 11 = c.im
  ⟨none, []⟩, ⟨some "add", [11, 12]⟩]⟩                           -- 12 = e.im, 13 = y.im

/-- The match, in the recorder's numbering. -/
def m : Match Nat where
  components := [(0, [0, 3]), (1, [1, 4]), (2, [7, 12]), (3, [6, 11]), (4, [8, 13])]
  realized := [⟨0, [2, 5, 9, 10]⟩, ⟨1, []⟩]

/-! ## The recorded tape is the authored graph -/

#guard (recorded.map fun (t, _, _) => ofTape t == T) == .ok true
#guard (recorded.map fun (_, r, i) => (r, i)) == .ok (8, 13)
#guard (recorded.map fun (t, _, _) => (ofTape t).ordered) == .ok true
#guard m.accepts g T

/-! ## The match is accepted by the kernel; the seal applies -/

lemma accepted : m.Accepts g T := by decide

/-- The seal of the computation, on any well-formed tape whose graph is `T` — the recorded
one, by the runtime check above. -/
example (t : Tape Float) (hwft : WF t) (hT : ofTape t = T) :
    ∀ (env₁ env₂ : String → Float) (vals₁ vals₂ : Array Float),
      (∀ s ∈ g.influencers 4, ∀ u ∈ m.comps s, ∀ nm, (ofTape t).name? u = some nm →
        env₁ nm = env₂ nm) →
      evalTape env₁ t = .ok vals₁ → evalTape env₂ t = .ok vals₂ →
      vals₁.getD 8 0.0 = vals₂.getD 8 0.0 :=
  (semantic_seal g_wellFormed t hwft (by rw [hT]; exact accepted) (o := 4) (r := 8)
    (by decide)).1

/-! ## The value clause, at runtime -/

/-- `a = 1 + 2j`, `b = 3 + 4j`: `a · b = −5 + 10j`, `y = −3.5 + 12j`. -/
def env₁ : String → Float
  | "a.re" => 1.0 | "a.im" => 2.0 | "b.re" => 3.0 | "b.im" => 4.0 | _ => 0.0

/-- The same inputs, with a name no leaf carries set differently. -/
def env₂ : String → Float
  | "a.re" => 1.0 | "a.im" => 2.0 | "b.re" => 3.0 | "b.im" => 4.0 | "unused" => 7.0 | _ => 0.0

#guard (recorded.bind fun (t, r, i) => (evalTape env₁ t).map fun v => (v.getD r 0.0, v.getD i 0.0))
  == .ok (-3.5, 12.0)
#guard (recorded.bind fun (t, r, i) => (evalTape env₂ t).map fun v => (v.getD r 0.0, v.getD i 0.0))
  == .ok (-3.5, 12.0)

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Paradigm.TapeSeal.evalTape_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalTape_cone

/-- info: 'PropertyKindCalculus.Paradigm.TapeSeal.semantic_seal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_seal

/-- info: 'PropertyKindCalculus.Paradigm.TapeSeal.semantic_seal_of_denotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_seal_of_denotes

/-- info: 'PropertyKindCalculus.Paradigm.TapeCodegen.SL.ofProg_eq_ofTape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PropertyKindCalculus.Paradigm.TapeCodegen.SL.ofProg_eq_ofTape

/-- info: 'PropertyKindCalculus.Paradigm.TapeSeal.semantic_seal_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_seal_program

end PropertyKindCalculus.Tests.TapeSeal

end Blanket
