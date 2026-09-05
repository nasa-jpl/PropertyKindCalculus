/-
# Re-carving, and what a count is keyed to (Marmodoro §3; SI amount of substance)

A `Decomposition` is a carving and not a census (`Mereology.lean`). This module says what
follows from that, in two halves that answer each other.

**Re-carving.** A `Recarving` is a map from one carving of a whole to another, carrying the
obligation that the whole is the same whole. Its theorem is that *every licensed aggregate
survives*: for an extensive kind, `leafSum` is the value of the whole (`extensive_additive`),
so a re-carving preserves the total over the parts however many parts it leaves behind. That
is the generalization of the pattern PhysLib already proves in one corner — `TenQuanta.reduce`
merges matter curves of equal charge and `reduce_sum_eq_sum_toCharges` shows every additive
functional is carving-invariant — stated once, for any extensive kind, instead of once per
functional.

**Counts.** The count of parts does *not* survive: `coalesce` below preserves the mass of a
two-part carving while leaving one part. So a count is extensive (it adds over a fixed
carving — the law PhysLib's `CanonicalEnsemble.dof_add` and `ACCSystemCharges.numberCharges`
each use for one particular count) and yet is *not* a property of the whole. What supplies
the missing principle is the sortal the count is keyed to, which is the SI's own reading of
amount of substance: a count **of a specified elementary entity**. `countMeasurement` takes
that sortal as an argument, and `count_sortal_ne` is the check that the argument matters.

Together these are Marmodoro's claim as two theorems rather than a slogan: physical structure
unites without bringing a count principle, so "[i]t is an open question how many entities a
physical structure is" (*Whole, but not One*, 2018, §3) — the aggregate is answerable to the
whole, the count is answerable only to a sortal.
-/

import PropertyKindCalculus.Extensivity

namespace PropertyKindCalculus

universe u

/-! ## Re-carving a whole -/

/-- **A re-carving of a whole**: a map on carvings, with the obligation that the measured
whole is left where it was. The obligation is a field rather than a side condition for the
reason `WeightedCarving`'s nonzero total is a field — a map that does not preserve the whole
is not a re-carving of it, and should not be a term of this type. -/
structure Recarving {O : Type u} (m : Measurement O) where
  /-- The map from one carving of the whole to another. -/
  map : Decomposition O → Decomposition O
  /-- **The obligation**: the whole is the same whole. -/
  preserves : ∀ d, (m (map d)).numeral = (m d).numeral

namespace Recarving

/-- **Every licensed aggregate is re-carving invariant.** For an extensive kind the total over
the parts *is* the value of the whole, so a map that preserves the whole preserves the total —
whatever it does to the parts. This is the law `reduce_sum_eq_sum_toCharges` establishes for
one functional in one corner of PhysLib, proved once for every extensive kind. -/
theorem leafSum_invariant {O : Type u} {k : KindOfProperty} {m : Measurement O}
    (h : Extensive k m) (r : Recarving m) (d : Decomposition O) :
    leafSum m (r.map d) = leafSum m d := by
  rw [← extensive_additive h (r.map d), ← extensive_additive h d]
  exact r.preserves d

end Recarving

/-! ## Counts, and the sortal they are keyed to

The count itself (`Decomposition.count`) and its equality with the join count are
`Mereology.lean`'s; here the count meets the measurement layer and its refutations. -/

/-- **A count kind**: the measurement whose value on a carving is that count, of kind `k` and
in the unit one. -/
def countMeasurement {O : Type u} (k : KindOfProperty) (p : O → Bool) : Measurement O :=
  fun d => { kind := k, numeral := Decomposition.count p d, reference := "1" }

/-- **A count is extensive.** Additivity over a carving is the fold's union case, so counts
sit in §13.5.1 alongside mass — which is the law each of PhysLib's bare-scalar counts uses
(`dof_add`, "for N particles in 3D this is 3N"), one count at a time. -/
theorem countMeasurement_extensive {O : Type u} (k : KindOfProperty) (p : O → Bool) :
    Extensive k (countMeasurement (O := O) k p) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-! ### Witness — the whole survives a re-carving, the count does not

The simplest whole there is: a part *is* its mass in whole kilograms, so a carving is a tree
of numbers and the whole is their sum. `coalesce` replaces any carving by the single part
whose mass is that total — fewer entities, same whole, the `reduce` pattern with nothing else
in it. Its `preserves` field is `rfl`, because the total of a one-leaf carving of the total is
the total. -/

/-- Mass, a ratio kind. -/
def partMassKind : KindOfProperty := { id := "mass", scale := .ratio }

/-- A part is its own mass, in whole kilograms; a carving reads the total of its parts. -/
def partMass : Measurement Int := fun d =>
  { kind := partMassKind, numeral := Decomposition.fold id (· + ·) d, reference := "kg" }

/-- **Mass is extensive here**, so `leafSum_invariant` applies to it. -/
theorem partMass_extensive : Extensive partMassKind partMass := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- **The coalescing re-carving**: one part, of the total mass. It preserves the whole by
`rfl` — the total of `⟨total d⟩` is `total d`. -/
def coalesce : Recarving partMass where
  map d := .atom (Decomposition.fold id (· + ·) d)
  preserves _ := rfl

/-- Two one-kilogram parts. -/
def twoParts : Decomposition Int := .union (.atom 1) (.atom 1)

/-- **The aggregate survives.** The total over the parts is the same before and after — by the
general law, applied to a real re-carving of a real carving. -/
theorem coalesce_leafSum :
    leafSum partMass (coalesce.map twoParts) = leafSum partMass twoParts :=
  Recarving.leafSum_invariant partMass_extensive coalesce twoParts

/-- **The count does not.** The same re-carving takes two parts to one. So there is no
function from the whole to how many parts it has, and a library that reports a count is
reporting a fact about its carving — which is why a count needs a sortal to be a quantity of
the whole at all. -/
theorem coalesce_count_ne :
    Decomposition.count (fun _ => true) (coalesce.map twoParts)
      ≠ Decomposition.count (fun _ => true) twoParts := by decide

/-- **And the sortal is what a count is keyed to.** One carving, two predicates, two counts:
counting the one-kilogram parts of `twoParts` gives 2 and counting its two-kilogram parts
gives 0. The elementary entity is not recoverable from the whole, which is the content of the
SI's insistence that amount of substance is a count *of a specified* entity. -/
theorem count_sortal_ne :
    Decomposition.count (fun n => n == 1) twoParts
      ≠ Decomposition.count (fun n => n == 2) twoParts := by decide

end PropertyKindCalculus
