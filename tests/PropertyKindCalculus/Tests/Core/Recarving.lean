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

import PropertyKindCalculus

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

/-- info: 'PropertyKindCalculus.Recarving.leafSum_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Recarving.leafSum_invariant

/-- info: 'PropertyKindCalculus.countMeasurement_extensive' does not depend on any axioms -/
#guard_msgs in #print axioms countMeasurement_extensive

/-- info: 'PropertyKindCalculus.count_true_eq_joins_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms count_true_eq_joins_succ

/-- info: 'PropertyKindCalculus.coalesce_count_ne' does not depend on any axioms -/
#guard_msgs in #print axioms coalesce_count_ne

/-- info: 'PropertyKindCalculus.count_sortal_ne' does not depend on any axioms -/
#guard_msgs in #print axioms count_sortal_ne

end PropertyKindCalculus.Tests.Recarving
