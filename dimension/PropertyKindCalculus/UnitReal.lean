/-
# The real-valued unit — a chosen reference quantity of a kind (Dybkær §13.3.3, §18.12)

`PropertyKindCalculus.Unit` realizes the §18.12 *metrological unit* symbolically: a kind and a
terminological symbol, with the §13.3.3 number-and-reference form as an exact round-trip over
the `Int` numeral. That layer settles commensurability and comparability, and it is
Mathlib-free.

This module is its magnitude-carrying refinement. A `RealUnit k` is a *quantity* of kind `k`
chosen as the reference, with the one condition the choice has to satisfy — a zero reference
compares nothing — carried as a field. Measuring is then division and re-applying is
multiplication, so the §13.3.3 round-trip is the field axiom rather than a definitional
unfolding, and conversion between two units of a kind becomes their *ratio*: an arbitrary real
number, where the prefixed units of `UnitConversion` have a power of the radix.

The kind index does the same work it does everywhere else: `RealUnit lengthKind` and
`RealUnit waterContentKind` are different types, so "a metre" is not a candidate reference for
a gravimetric water content, and that is a fact of the types rather than a runtime check.
Lives in the `Dimension` library because `ℝ` needs Mathlib.
-/

import PropertyKindCalculus.Unit
import PropertyKindCalculus.QuantityReal
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PropertyKindCalculus

variable {k : KindOfProperty}

/-- **§18.12 — a unit as a chosen reference quantity, carrying its magnitude.** One quantity of
the kind `k`, distinguished as the reference "with which any other quantity of the same kind
can be compared to express the ratio of the two quantities as a number" (VIM4 2CD 1.12).

`ref_ne_zero` is the condition that phrase presupposes and the symbolic layer never has to
state: a reference of magnitude zero expresses no ratio. Carried as a field, so a degenerate
unit is not a term of this type — the same discipline `WeightedCarving` applies to a mean's
denominator. -/
structure RealUnit (k : KindOfProperty) where
  /-- The quantity of kind `k` chosen as the reference. -/
  ref : Quantity k ℝ
  /-- **The license**: the reference has a nonzero magnitude, so ratios against it exist. -/
  ref_ne_zero : ref.magnitude ≠ 0

namespace RealUnit

/-- **§13.3.3 — measuring: `quantity / unit = number`.** The numeric value of `q` expressed in
`u`, which is exactly the ratio of the two quantities. -/
noncomputable def measure (q : Quantity k ℝ) (u : RealUnit k) : ℝ :=
  q.magnitude / u.ref.magnitude

/-- **§13.3.3 — the reverse: `number × unit = quantity`.** The quantity of kind `k` whose value
in `u` is `n`. -/
noncomputable def ofNumber (u : RealUnit k) (n : ℝ) : Quantity k ℝ :=
  ⟨n * u.ref.magnitude⟩

/-- **A unit measures one of itself.** The defining property of a reference, and the reason the
license is needed to state it at all. -/
@[simp] theorem measure_self (u : RealUnit k) : measure u.ref u = 1 :=
  div_self u.ref_ne_zero

/-- **Round-trip, one way**: read back the number a quantity was built from. -/
@[simp] theorem measure_ofNumber (u : RealUnit k) (n : ℝ) : measure (u.ofNumber n) u = n := by
  unfold measure ofNumber
  have hu := u.ref_ne_zero
  field_simp

/-- **Round-trip, the other way**: rebuild the quantity from its numeric value. Together with
`measure_ofNumber` this is the §13.3.3 number-and-reference form as a bijection between
`Quantity k ℝ` and `ℝ`, once a reference is fixed. -/
@[simp] theorem ofNumber_measure (u : RealUnit k) (q : Quantity k ℝ) :
    u.ofNumber (measure q u) = q := by
  unfold measure ofNumber
  rw [div_mul_cancel₀ _ u.ref_ne_zero]

/-- **§1.22 — the conversion factor between two units of one kind**, as the ratio of their
references. This is the *general* factor the prefixed units of `UnitConversion` specialize:
there it is a power of the radix and therefore structurally nonzero, here it is nonzero
because both references are. -/
noncomputable def ratio (u v : RealUnit k) : ℝ := u.ref.magnitude / v.ref.magnitude

/-- The conversion factor is nonzero — from the two licenses, and from nothing else. -/
theorem ratio_ne_zero (u v : RealUnit k) : u.ratio v ≠ 0 :=
  div_ne_zero u.ref_ne_zero v.ref_ne_zero

/-- **Conversion**: the value in `v` is the value in `u` times the factor from `u` to `v`. -/
theorem measure_eq_measure_mul_ratio (q : Quantity k ℝ) (u v : RealUnit k) :
    measure q v = measure q u * u.ratio v := by
  unfold measure ratio
  have hu := u.ref_ne_zero
  have hv := v.ref_ne_zero
  field_simp

/-- **Conversion is a faithful round-trip**, for an arbitrary chosen reference rather than a
power of ten: the two factors between commensurable units are reciprocal. -/
theorem ratio_mul_ratio_symm (u v : RealUnit k) : u.ratio v * v.ratio u = 1 := by
  unfold ratio
  have hu := u.ref_ne_zero
  have hv := v.ref_ne_zero
  field_simp

/-! ## Well-formedness, and the symbolic unit refined -/

/-- **§13.3.3** — a real-valued unit is *well-formed* exactly when the symbolic one is: its
kind must bear a unit. Neither layer can measure a nominal or ordinal kind, and the refinement
does not quietly widen what a unit is. -/
def WellFormed (_u : RealUnit k) : Prop := k.BearsUnit

/-- A real-valued unit of a nominal kind is ill-formed (§9.13.4) — the refinement inherits the
exclusion rather than restating it. -/
theorem not_wellFormed_of_nominal {u : RealUnit k} (h : k.IsNominal) : ¬ u.WellFormed :=
  KindOfProperty.nominal_bears_no_unit h

/-- A real-valued unit of an ordinal kind is ill-formed (§9.13.4). -/
theorem not_wellFormed_of_ordinal {u : RealUnit k} (h : k.IsOrdinal) : ¬ u.WellFormed :=
  KindOfProperty.ordinal_bears_no_unit h

/-- The symbolic §18.12 unit this reference names, once a terminological symbol is chosen. -/
def toMetrological (_u : RealUnit k) (symbol : String) : MetrologicalUnit := k.unit symbol

/-- **The refinement agrees with what it refines.** The `Int` numeral the symbolic layer records
for `n` is the real number this layer reads back for the same `n` — so the magnitude-carrying
unit is a refinement of the symbolic one and not a second, unrelated notion of measuring. -/
theorem measure_ofNumber_eq_symbolic (u : RealUnit k) (symbol : String) (n : Int) :
    measure (u.ofNumber (n : ℝ)) u = (((u.toMetrological symbol).measure n).numeral : ℝ) := by
  rw [measure_ofNumber]
  rfl

end RealUnit

end PropertyKindCalculus
