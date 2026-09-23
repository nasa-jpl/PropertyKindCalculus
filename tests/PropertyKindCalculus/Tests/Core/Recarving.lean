/-
# Validation probes — re-carving and counts (R9)

Two claims that answer each other, and each has a way of being vacuously true. "Every licensed
aggregate survives a re-carving" is empty if no re-carving exists, so the probe applies it to a
real one — `coalesce`, which takes a two-part carving of a mass to a one-part carving of the
same mass. "A count does not survive" is empty if the two counts are never computed, so the
probe computes both: 2 before, 1 after. The pair is what makes the point checkable rather than
rhetorical — one and the same map, preserving the whole and changing how many parts there are.

The third probe is the sortal: one carving, two predicates, two counts. A count that did not
depend on its predicate would make `countMeasurement`'s argument decoration.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.Recarving

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Recarving

open PropertyKindCalculus

-- Inhabitation: `coalesce` is a real re-carving of a real carving, and the aggregate survives —
-- obtained from the general law, not by computing both sides.
theorem r9_coalesce_leafSum :
    leafSum partMass (coalesce.map twoParts) = leafSum partMass twoParts :=
  Recarving.leafSum_invariant partMass_extensive coalesce twoParts

-- … and both sides are 2 kg, so the law is applied to something with content.
#guard leafSum partMass twoParts == 2
#guard leafSum partMass (coalesce.map twoParts) == 2

-- Boundary — the count is exactly what does *not* survive: two parts before, one after.
theorem r9_coalesce_count_ne :
    Decomposition.count (fun _ => true) (coalesce.map twoParts)
      ≠ Decomposition.count (fun _ => true) twoParts :=
  coalesce_count_ne

#guard Decomposition.count (fun _ => true) twoParts == 2
#guard Decomposition.count (fun _ => true) (coalesce.map twoParts) == 1

-- Inhabitation: a count is extensive, so it aggregates over a *fixed* carving …
theorem r9_count_extensive :
    Extensive partMassKind (countMeasurement (O := Int) partMassKind (fun _ => true)) :=
  countMeasurement_extensive _ _

-- … and the sortal it is keyed to is load-bearing: the same carving, counted two ways.
theorem r9_count_sortal_ne :
    Decomposition.count (fun n => n == 1) twoParts
      ≠ Decomposition.count (fun n => n == 2) twoParts :=
  count_sortal_ne

#guard Decomposition.count (fun n => n == 1) twoParts == 2
#guard Decomposition.count (fun n => n == 2) twoParts == 0

-- The two shape numbers agree: a carving with `n` joins exhibits `n + 1` parts.
#guard twoParts.joins == 1

/-! ## The boundary-level form — one map, every extensive output preserved (R27)

A module's boundary is a list of outputs, and the distribution license is the
quantifier over that list: one re-carving of the batch axis, every declared-extensive
output's total preserved. The probe needs a module with *two* extensive outputs so the
list form says more than the per-output law — and the count is deliberately not among
them, because `coalesce` does not preserve a count's whole and the license correctly
has no instance for it. -/

/-- A second extensive output over the same parts — twice the mass, as its own fold. -/
def partMassDoubled : Measurement Int := fun d =>
  { kind := partMassKind, numeral := 2 * Decomposition.fold id (· + ·) d,
    reference := "kg" }

/-- Twice an extensive fold is extensive: additivity is `Int.mul_add` at the union. -/
theorem partMassDoubled_extensive : Extensive partMassKind partMassDoubled :=
  ⟨fun _ => rfl, fun _ _ => Int.mul_add 2 _ _⟩

/-- The module's declared-extensive outputs: both masses, one batch axis. -/
def massOutputs : List (KindOfProperty × Measurement Int) :=
  [(partMassKind, partMass), (partMassKind, partMassDoubled)]

-- The boundary-level license, applied: `coalesce` re-carves the axis once, and both
-- outputs' totals survive — from the one quantified law, not output by output.
theorem r27_distribution_license :
    ∀ o ∈ massOutputs, leafSum o.2 (coalesce.map twoParts) = leafSum o.2 twoParts :=
  Recarving.distribution_license massOutputs coalesce.map
    (by
      intro o ho
      simp only [massOutputs, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact partMass_extensive
      · exact partMassDoubled_extensive)
    (by
      intro o ho
      simp only [massOutputs, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> intro d <;> rfl)
    twoParts

-- … and both sides carry content: 2 kg and 4 kg respectively, before and after.
#guard leafSum partMassDoubled twoParts == 4
#guard leafSum partMassDoubled (coalesce.map twoParts) == 4

/-- info: 'PropertyKindCalculus.Recarving.leafSum_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Recarving.leafSum_invariant

/-- info: 'PropertyKindCalculus.Recarving.distribution_license' does not depend on any axioms -/
#guard_msgs in #print axioms Recarving.distribution_license

/-- info: 'PropertyKindCalculus.countMeasurement_extensive' does not depend on any axioms -/
#guard_msgs in #print axioms countMeasurement_extensive

/-- info: 'PropertyKindCalculus.count_true_eq_joins_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms count_true_eq_joins_succ

/-- info: 'PropertyKindCalculus.coalesce_count_ne' does not depend on any axioms -/
#guard_msgs in #print axioms coalesce_count_ne

/-- info: 'PropertyKindCalculus.count_sortal_ne' does not depend on any axioms -/
#guard_msgs in #print axioms count_sortal_ne

end PropertyKindCalculus.Tests.Recarving

end Blanket
