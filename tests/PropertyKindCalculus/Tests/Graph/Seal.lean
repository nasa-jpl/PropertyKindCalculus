/-
# Validation probes — the seal of a module (capstone 1)

Inhabitation, negative and axiom-profile probes for `Graph.Seal`: a `Nat`-labelled instance
whose well-formedness and seal the kernel decides, the theorem applied to it, a mutant with
an anonymous mint that fails the hypothesis *and* the conclusion — so the hypothesis is seen
to carry the weight — and the axiom profiles of the three statements, pinned.
`seal_witnesses` conjoins the instance and the mutant for the blueprint's witness node.
-/

module

public import PropertyKindCalculus.Graph.Seal
meta import PropertyKindCalculus.Graph.Seal

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.GraphSeal

open PropertyKindCalculus Provenance

/-- The influence probe with `Nat` labels, for the kernel route: nodes `in1 = 0`, `cfg = 1`,
`out = 2`, `mid = 3`, `att = 4`, `gat = 5`; kinds `kA = 10`, `kB = 11`, `kC = 12`. -/
def GN : Provenance Nat Nat where
  ports := [⟨0, 10, .input⟩, ⟨1, 11, .config⟩, ⟨2, 12, .output⟩]
  intros := [⟨3, 11, .derived⟩, ⟨4, 10, .attested "vendor table reviewed"⟩, ⟨5, 11, .gated⟩]
  occurrences := [
    ⟨.product, [(0, 10), (4, 10)], 3, 11, "probe", .anonymous⟩,
    ⟨.product, [(3, 11), (5, 11)], 2, 12, "probe", .anonymous⟩]
  exits := [3]

/-- The mutant: an anonymous mint `6` — `derived`, produced by no occurrence — wired into the
output in place of the gated ingest. -/
def GNmut : Provenance Nat Nat where
  ports := GN.ports
  intros := GN.intros ++ [⟨6, 11, .derived⟩]
  occurrences := [
    ⟨.product, [(0, 10), (4, 10)], 3, 11, "probe", .anonymous⟩,
    ⟨.product, [(3, 11), (6, 11)], 2, 12, "probe", .anonymous⟩]
  exits := [3]

/-! ## Inhabitation: the hypotheses hold and the conclusion is decided on the instance -/

lemma GN_wellFormed : GN.WellFormed := by decide
lemma GN_sealed : GN.Sealed := by decide

/-- The theorem, applied: the seal follows from well-formedness on the instance. -/
example : GN.Sealed := sealed_of_wellFormed GN_wellFormed

/-- The seal of the output, applied: every ancestor of `out` is a source or derived from
ancestors of `out`. -/
example {a : Nat} (ha : a ∈ GN.ancestorsOf [2]) :
    a ∈ GN.sources ∨
      ∃ o ∈ GN.occurrences, o.result = a ∧ ∀ oc ∈ o.operands, oc.1 ∈ GN.ancestorsOf [2] :=
  pedigree_seal GN_wellFormed (by decide) ha

/-! ## The mutant: the hypothesis fails and the conclusion fails, together -/

lemma GNmut_not_wellFormed : ¬ GNmut.WellFormed := by decide
lemma GNmut_not_sealed : ¬ GNmut.Sealed := by decide

-- The undeclared leaf is exactly the mint.
example : GNmut.undeclaredLeaves 2 = [6] := by decide

/-- **Non-vacuity of the seal**: the instance satisfies the hypothesis and the conclusion; the
mutant fails both. The axiom profile of the seal itself is pinned below. -/
lemma seal_witnesses :
    GN.WellFormed ∧ GN.Sealed ∧ ¬ GNmut.WellFormed ∧ ¬ GNmut.Sealed :=
  ⟨GN_wellFormed, GN_sealed, GNmut_not_wellFormed, GNmut_not_sealed⟩

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Provenance.pedigree_seal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pedigree_seal

/-- info: 'PropertyKindCalculus.Provenance.sealed_of_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealed_of_wellFormed

/-- info: 'PropertyKindCalculus.Provenance.seal_of_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms seal_of_agrees

/-- info: 'PropertyKindCalculus.Tests.GraphSeal.seal_witnesses' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms seal_witnesses

end PropertyKindCalculus.Tests.GraphSeal

end Blanket
