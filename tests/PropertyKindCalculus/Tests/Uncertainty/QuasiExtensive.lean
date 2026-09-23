/-
# Validation probes — §13.5.2 quasiextensive (R9, R18)

A tolerance predicate has a failure mode the other three §13.5 branches do not: it can be true
of everything. `QuasiExtensive k m t` with a large enough `t` says nothing, so both dangers have
to be probed from both sides.

  * **Non-vacuous.** The rounding balance is quasiextensive to within one digit *and not
    extensive*, so the branch is occupied by something §13.5.1 excludes.
  * **Discriminating.** Volume on mixing refutes every tolerance below 4 mL — the probe fixes
    `t = 3` and derives `False`, so the predicate genuinely rules something out.
  * **Bounded by the carving, not the whole.** The capstone is applied to a depth-2 carving and
    the three numbers it relates are computed here: reading 4, leaf sum 3, two joins.

The last probe is the one that keeps the tolerance honest: it is a coverage factor, and
`join_within_tolerance` is R18's Chebyshev bound supplying the probability.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
public import PropertyKindCalculus.Uncertainty.QuasiExtensive
meta import PropertyKindCalculus.Uncertainty.QuasiExtensive

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.QuasiExtensive

open PropertyKindCalculus
open PropertyKindCalculus.Uncertainty

/-- A depth-2 carving of three samples — nested, so the per-join tolerance actually accumulates
rather than being read off a single split. -/
def threeSamples : Decomposition System :=
  .union (.union (.atom ⟨"a"⟩) (.atom ⟨"b"⟩)) (.atom ⟨"c"⟩)

-- Inhabitation (Rule 2 — the nested case): the whole-tree bound, applied to a real carving.
theorem r9_quasi_bound :
    |((coarseMass threeSamples).numeral : ℝ) - (leafSum coarseMass threeSamples : ℝ)|
      ≤ (threeSamples.joins : ℝ) * 1 :=
  quasiExtensive_leafSum coarseMass_quasiExtensive threeSamples

-- … and the three numbers it relates: the composite reads 4, its parts total 3, over two joins.
#guard (coarseMass threeSamples).numeral == 4
#guard leafSum coarseMass threeSamples == 3
#guard threeSamples.joins == 2

-- Non-vacuity — the branch is occupied by something §13.5.1 excludes: the same measurement is
-- quasiextensive to within one digit and not extensive.
theorem r9_coarse_quasi : QuasiExtensive coarseMassKind coarseMass 1 := coarseMass_quasiExtensive

theorem r9_coarse_not_extensive : ¬ Extensive coarseMassKind coarseMass :=
  coarseMass_not_extensive

-- Boundary — the tolerance is doing work: 3 mL does not absorb a 4 mL contraction.
theorem r9_mixing_not_quasi : ¬ QuasiExtensive volume volMix 3 :=
  mixing_not_quasiExtensive (by norm_num)

-- Inhabitation: §13.5.1 sits inside §13.5.2 at zero tolerance, applied to a real extensive
-- measurement rather than stated in the abstract.
theorem r9_extensive_is_quasi_zero : QuasiExtensive partMassKind partMass 0 :=
  extensive_iff_quasiExtensive_zero.mp partMass_extensive

theorem r9_quasi_zero_is_extensive : Extensive partMassKind partMass :=
  extensive_iff_quasiExtensive_zero.mpr r9_extensive_is_quasi_zero

/-- info: 'PropertyKindCalculus.Uncertainty.quasiExtensive_leafSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.quasiExtensive_leafSum

/-- info: 'PropertyKindCalculus.Uncertainty.extensive_iff_quasiExtensive_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.extensive_iff_quasiExtensive_zero

/-- info: 'PropertyKindCalculus.Uncertainty.coarseMass_quasiExtensive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.coarseMass_quasiExtensive

/-- info: 'PropertyKindCalculus.Uncertainty.mixing_not_quasiExtensive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.mixing_not_quasiExtensive

/-- info: 'PropertyKindCalculus.Uncertainty.join_within_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.join_within_tolerance

end PropertyKindCalculus.Tests.QuasiExtensive

end Blanket
