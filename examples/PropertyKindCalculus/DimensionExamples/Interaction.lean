/-
# Worked examples — the interaction algebra

Checked facts exercising the curated kind product (`InteractionAlgebra`): the
worked SI-mechanics algebra, its dimensional coherence, the curation that keeps
`torque × angle = energy` apart from the category error `torque × angle = torque`,
and the multiplication/division round-trip.

These live in the `DimensionExamples` library (not the Mathlib-free `Examples`
library), because the coherence side-condition is stated over PhysLib's
`Dimension`.
-/

module

public import PropertyKindCalculus.Interaction

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.Interaction

open PropertyKindCalculus

/-! ## Torque and energy: one dimension, two kinds

The dimension layer cannot separate torque from energy — both are `M·L²·T⁻²` — so
this is exactly the within-dimension confusion the interaction algebra exists to
prevent. -/

/-- The dimension layer cannot tell torque from energy … -/
example : torqueKind.toDimension = energyKind.toDimension := rfl

/-- … and both carry the mechanical-work dimension `M·L²·T⁻²` (mass 1, length 2,
time −2), a checked computation in PhysLib's group. -/
example : Dim.energy.mass = 1 := by
  norm_num [Dim.energy, Dim.force, Dim.length, Dimension.M𝓭]
example : Dim.energy.length = 2 := by
  norm_num [Dim.energy, Dim.force, Dim.length, Dimension.M𝓭]
example : Dim.energy.time = -2 := by
  norm_num [Dim.energy, Dim.force, Dim.length, Dimension.M𝓭]

/-- … yet they are distinct *kinds*. -/
example : energyKind.kind ≠ torqueKind.kind := by decide

/-! ## The sanctioned products, and their coherence (R7) -/

example : siMech.KMul forceKind lengthKind energyKind := .force_length_energy
example : siMech.KMul torqueKind angleKind energyKind := .torque_angle_energy

/-- Forgetting a sanctioned product to the dimension layer yields the dimension
product — the homomorphism, on a concrete edge. -/
example :
    energyKind.toDimension = torqueKind.toDimension * angleKind.toDimension :=
  siMech.dim_homomorphism .torque_angle_energy

/-! ## Curation: dimensional coherence is necessary, not sufficient (R5 / R7)

`torque × angle = torque` is dimensionally fine — plane angle is dimension one, so
the dimensions would balance — yet the algebra does *not* sanction it. The kind
relation, not `dim`, decides legality. -/

/-- Every product the worked algebra sanctions yields `energy`. -/
theorem sanctioned_yields_energy {a b c : DimensionedKind}
    (h : siMech.KMul a b c) : c = energyKind := by
  cases h <;> rfl

example : ¬ siMech.KMul torqueKind angleKind torqueKind := by
  intro h
  have : torqueKind.kind = energyKind.kind :=
    congrArg DimensionedKind.kind (sanctioned_yields_energy h)
  exact absurd this (by decide)

/-! ## Multiplication and division are inverse (R5) -/

/-- The round-trip is an equivalence: `torque × angle = energy` iff
`energy / angle = torque`. -/
example :
    siMech.KMul torqueKind angleKind energyKind
      ↔ siMech.KDiv energyKind angleKind torqueKind :=
  siMech.kMul_iff_kDiv torqueKind angleKind energyKind

/-- Dividing the product `energy` by the factor `angle` recovers `torque`. -/
example : siMech.KDiv energyKind angleKind torqueKind :=
  SIMech.KMul.torque_angle_energy

/-! ## The whole worked instance in one fact

The product holds, `energy ≠ torque` as kinds, and they share a dimension. -/

example :
    siMech.KMul torqueKind angleKind energyKind
      ∧ energyKind.kind ≠ torqueKind.kind
      ∧ energyKind.toDimension = torqueKind.toDimension :=
  torque_angle_work

end PropertyKindCalculus.Examples.Interaction

end -- pkc-blanket-expose
end -- pkc-blanket
