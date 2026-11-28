/-
# Validation probes — the kind-transporting weak bisimulation (capstone 2's relation)

An authored pair the kernel decides: a provenance hypergraph with a product and a same-kind
sum, `y = a · b + e`, and the computational tape graph its complex realization records — the
product expanded to `(ac − bd) + (ad + bc)j`, four interior vertices the bisimulation is silent
on, the sum componentwise. The match's acceptance is decided by the kernel, the three
bisimulation theorems are instantiated on it, and a mutant tape that bakes one constant the
hypergraph does not list is refused — the hypothesis fails where the conclusion's constant
clause would. `bisimulation_witnesses` conjoins the instance and the mutant for the
blueprint's witness node.
-/

module

public import PropertyKindCalculus.Graph.Bisimulation
meta import PropertyKindCalculus.Graph.Bisimulation

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Bisimulation

open Cslib
open PropertyKindCalculus Provenance
open PropertyKindCalculus.Paradigm (TapeGraph TapeVertex Match Realized)

/-- The hypergraph: inputs `a = 0` (kind 1) and `b = 2`… read: nodes `a = 0`, `b = 1`, the
attested constant `e = 2`, the derived product `c = 3`, the output `y = 4`; kinds `1`, `2`,
`3`. Two occurrences: `a · b → c` and `c ± e → y`. -/
def g : Provenance Nat Nat where
  ports := [⟨0, 1, .input⟩, ⟨1, 2, .input⟩, ⟨4, 3, .output⟩]
  intros := [⟨2, 3, .attested "calibration offset"⟩, ⟨3, 3, .derived⟩]
  occurrences := [
    ⟨.product, [(0, 1), (1, 2)], 3, 3, "probe", .anonymous⟩,
    ⟨.additive, [(3, 3), (2, 3)], 4, 3, "probe", .anonymous⟩]
  exits := []

/-- The tape graph the complex realization records: named leaves for the two inputs' parts,
unnamed constant leaves for the offset's parts, the four partial products, the two parts of
`c`, the two parts of `y`. -/
def T : TapeGraph := ⟨[
  ⟨some "a.re", []⟩, ⟨some "a.im", []⟩,          -- 0, 1
  ⟨some "b.re", []⟩, ⟨some "b.im", []⟩,          -- 2, 3
  ⟨none, []⟩, ⟨none, []⟩,                        -- 4, 5: e.re, e.im
  ⟨some "mul", [0, 2]⟩, ⟨some "mul", [1, 3]⟩,    -- 6: ac, 7: bd
  ⟨some "mul", [0, 3]⟩, ⟨some "mul", [1, 2]⟩,    -- 8: ad, 9: bc
  ⟨some "sub", [6, 7]⟩, ⟨some "add", [8, 9]⟩,    -- 10: c.re, 11: c.im
  ⟨some "add", [10, 4]⟩, ⟨some "add", [11, 5]⟩]⟩ -- 12: y.re, 13: y.im

/-- The match: each node to its two parts; the product realized with the four partial
products as its interior, the sum with no interior. -/
def m : Match Nat where
  components := [(0, [0, 1]), (1, [2, 3]), (2, [4, 5]), (3, [10, 11]), (4, [12, 13])]
  realized := [⟨0, [6, 7, 8, 9]⟩, ⟨1, []⟩]

/-- The mutant tape: one more constant leaf, `14`, baked into `y.re` in place of the listed
offset — a constant the hypergraph's assumption ledger does not carry. -/
def Tmut : TapeGraph := ⟨[
  ⟨some "a.re", []⟩, ⟨some "a.im", []⟩,
  ⟨some "b.re", []⟩, ⟨some "b.im", []⟩,
  ⟨none, []⟩, ⟨none, []⟩,
  ⟨some "mul", [0, 2]⟩, ⟨some "mul", [1, 3]⟩,
  ⟨some "mul", [0, 3]⟩, ⟨some "mul", [1, 2]⟩,
  ⟨some "sub", [6, 7]⟩, ⟨some "add", [8, 9]⟩,
  ⟨some "add", [10, 14]⟩, ⟨some "add", [11, 5]⟩,
  ⟨none, []⟩]⟩

/-! ## Inhabitation: acceptance decided, the theorems instantiated -/

#guard g.wellFormed
#guard m.accepts g T
#guard T.leaves == [0, 1, 2, 3, 4, 5]
#guard T.ops == [6, 7, 8, 9, 10, 11, 12, 13]

lemma g_wellFormed : g.WellFormed := by decide
lemma accepted : m.Accepts g T := by decide

/-- The strong bisimulation with the contracted tape graph, on the instance. -/
example : LTS.IsBisimulation g.lts (m.contracted g) (Match.obs m) :=
  Match.isBisimulation_contracted g_wellFormed (Match.Acc.of_accepts accepted)

/-- The contraction is a weak bisimulation with the tape graph, on the instance. -/
example : LTS.IsSWBisimulation (m.contracted g) (m.tapeLts g T) (Match.contraction g m) :=
  Match.isSWBisimulation_contraction g_wellFormed (Match.Acc.of_accepts accepted)

/-- The kind-transporting weak bisimulation, on the instance. -/
example : LTS.IsWeakBisimulation g.lts (m.tapeLts g T) (Match.weak g m) :=
  Match.isWeakBisimulation_weak g_wellFormed (Match.Acc.of_accepts accepted)

/-! ## The mutant: refused, where the constant clause would fail -/

#guard !m.accepts g Tmut
#guard !Match.leavesAreSources g Tmut m
#guard Tmut.leaves == [0, 1, 2, 3, 4, 5, 14]

lemma mutant_refused : ¬ m.Accepts g Tmut := by decide

/-- **Non-vacuity of the bisimulation**: the matcher accepts the instance and refuses the
mutant that bakes an unlisted constant. -/
lemma bisimulation_witnesses : m.Accepts g T ∧ ¬ m.Accepts g Tmut := ⟨accepted, mutant_refused⟩

/-! ## The real power — one occurrence for the one recorded `pow` vertex -/

/-- The hypergraph of `z = x ^ y`: base `0`, exponent `1`, result `2`, one `realPower` edge. -/
def gPow : Provenance Nat Nat where
  ports := [⟨0, 1, .input⟩, ⟨1, 1, .input⟩, ⟨2, 1, .output⟩]
  intros := []
  occurrences := [⟨.realPower, [(0, 1), (1, 1)], 2, 1, "probe", .anonymous⟩]
  exits := []

/-- The tape graph the recording produces: two named leaves and the two-parent `pow` vertex. -/
def TPow : TapeGraph := ⟨[⟨some "x", []⟩, ⟨some "y", []⟩, ⟨some "pow", [0, 1]⟩]⟩

/-- The match: each node its vertex, the power realized with no interior. -/
def mPow : Match Nat where
  components := [(0, [0]), (1, [1]), (2, [2])]
  realized := [⟨0, []⟩]

lemma gPow_wellFormed : gPow.WellFormed := by decide
lemma pow_accepted : mPow.Accepts gPow TPow := by decide

/-- The power's hypergraph is weakly bisimilar to its tape graph through the contraction. -/
example : LTS.IsSWBisimulation (mPow.contracted gPow) (mPow.tapeLts gPow TPow)
    (Match.contraction gPow mPow) :=
  Match.isSWBisimulation_contraction gPow_wellFormed (Match.Acc.of_accepts pow_accepted)

/-- The spelling `exp (y · log x)` as a hypergraph: nodes `l = 2`, `e = 3`, `z = 4`. -/
def gExpLog : Provenance Nat Nat where
  ports := [⟨0, 1, .input⟩, ⟨1, 1, .input⟩, ⟨4, 1, .output⟩]
  intros := [⟨2, 1, .derived⟩, ⟨3, 1, .derived⟩]
  occurrences := [
    ⟨.transcendental, [(0, 1)], 2, 1, "probe", .anonymous⟩,
    ⟨.product, [(1, 1), (2, 1)], 3, 1, "probe", .anonymous⟩,
    ⟨.transcendental, [(3, 1)], 4, 1, "probe", .anonymous⟩]
  exits := []

/-- Every component choice for `l`, `e`, `z` and every interior over the three vertices. -/
def powSubsets : List (List Nat) := [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]]

-- No match of the three-edge spelling against the one-vertex recording is accepted: the
-- intermediate nodes have no vertex, which is why the power is one family, not three.
#guard !(powSubsets.any fun cl => powSubsets.any fun ce => powSubsets.any fun cz =>
  powSubsets.any fun i0 => powSubsets.any fun i1 => powSubsets.any fun i2 =>
    (Match.mk [(0, [0]), (1, [1]), (2, cl), (3, ce), (4, cz)]
      [⟨0, i0⟩, ⟨1, i1⟩, ⟨2, i2⟩]).accepts gExpLog TPow)

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Paradigm.Match.isBisimulation_contracted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Match.isBisimulation_contracted

/-- info: 'PropertyKindCalculus.Paradigm.Match.isSWBisimulation_contraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Match.isSWBisimulation_contraction

/-- info: 'PropertyKindCalculus.Paradigm.Match.isWeakBisimulation_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Match.isWeakBisimulation_weak

/-- info: 'PropertyKindCalculus.Paradigm.Match.reachable_of_tape_path_comps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Match.reachable_of_tape_path_comps

/-- info: 'PropertyKindCalculus.Paradigm.Match.occurrence_of_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Match.occurrence_of_edge

/-- info: 'PropertyKindCalculus.Tests.Bisimulation.bisimulation_witnesses' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms bisimulation_witnesses

end PropertyKindCalculus.Tests.Bisimulation

end Blanket
