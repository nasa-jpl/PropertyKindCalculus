/-
# Validation probes — the angle-augmented base (parametric `Dimension` adopted)

Inhabitation and axiom-profile probes for the reform layer PKC gained by adopting the
basis-parametric `Dimension`: plane angle promoted to a base dimension, solid angle its
square. Each result is applied to concrete witnesses; the Rule-2 boundary is that the
five-generator sub-basis *conflates* what the angle-augmented base separates, and that
the dimension-one conflation the kind layer repairs *survives* the reform (angle-free
kinds are still one dimension). The Mathlib-backed proofs legitimately use
`[propext, Classical.choice, Quot.sound]`; the gate confirms **no `sorryAx`** creeps in.
-/

import PropertyKindCalculus.AngleReform

namespace PropertyKindCalculus.Tests.AngleReform

open PropertyKindCalculus PropertyKindCalculus.AngleReform

/-! ## The reform separates radian, steradian, and number at the dimension layer -/

-- Inhabitation: the three are pairwise dimensionally distinct over the angle-augmented base —
-- the separation a five-generator basis cannot draw, here drawn by the dimension group itself.
theorem reform_separates :
    radianKind.toDimension ≠ steradianKind.toDimension ∧
    radianKind.toDimension ≠ numberKind.toDimension ∧
    steradianKind.toDimension ≠ numberKind.toDimension :=
  radian_steradian_number_distinct

-- Inhabitation: torque and energy are dimensionally distinct (torque is energy per angle), yet
-- the sanctioned product `torque · angle = energy` is coherent by genuine cancellation.
theorem reform_torque_energy :
    torque ≠ energy ∧ torque * planeAngle = energy :=
  ⟨torque_ne_energy, torque_mul_angle_eq_energy⟩

-- Inhabitation: solid angle is the square of plane angle (`sr = rad²`).
theorem reform_solid_is_square : solidAngle = planeAngle * planeAngle := solidAngle_eq_sq

/-! ## Kind invariance under change of basis, and the surviving conflation -/

-- Inhabitation: lifting a catalogue kind into the angle-augmented base fixes its kind and
-- preserves its exponents — the base choice is invisible one layer up.
theorem reform_kind_invariant :
    (lengthKind.extend emb).kind = lengthKind.kind ∧
    (lengthKind.extend emb).toDimension.exponent (emb .length)
      = lengthKind.toDimension.exponent .length :=
  ⟨lengthKind_lift_kind, lengthKind_lift_faithful⟩

-- Boundary: promoting angle does not dissolve the kind layer's job. Volumetric and gravimetric
-- water content are angle-free, so they remain a *single* dimension over `Base` too, yet distinct
-- kinds — a dimension-only classifier still cannot tell them apart.
theorem reform_conflation_survives :
    (vwc.extend emb).toDimension = (gwc.extend emb).toDimension ∧
    (vwc.extend emb).kind ≠ (gwc.extend emb).kind :=
  waterContent_still_conflated

/-- info: 'PropertyKindCalculus.AngleReform.torque_ne_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms torque_ne_energy

/-- info: 'PropertyKindCalculus.AngleReform.radian_steradian_number_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms radian_steradian_number_distinct

/-- info: 'PropertyKindCalculus.DimensionedKind.extend_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DimensionedKind.extend_kind

end PropertyKindCalculus.Tests.AngleReform
