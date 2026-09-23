/-
# The catalogue over ISQ — base-agnosticism and citation fidelity, on real entries

`IsqBase` proves the bridge's laws but deliberately does not import the catalogue (a
downstream library), so its "the catalogue is base-agnostic" headline is demonstrated on a
local witness kind. This module closes that gap: the same two statements — *the lift fixes
the kind* and *the lifted dimension is the standard's printed ISQ form* — on catalogued
entries, per entry:

* **Part 4 mechanics**: mass (4-1, `M`), the energy family (4-28.1–.3, `M·L²·T⁻²`), torque
  (4-12.2, the *same* `M·L²·T⁻²` — the one proof serving all five is itself the "dimension
  does not classify" point), and action (4-32, `M·L²·T⁻¹`).
* **Part 6 electromagnetism**: electric current (6-1) lands on the bare `I` generator, and
  electric charge (6-2) on the *product* `I·T` — the two directions of the charge/current
  change of coordinates, exercised on the entries the standard actually prints.

With this, the design note's claim (`Dimension`, "The canonical basis
`LTMCTDimensionBase`…") is a per-entry build artifact: the catalogue commits to a
*presentation*, and the presentation is provably invisible one layer up and re-expressible
in the standard's own base with the printed exponents.
-/

module

public import PropertyKindCalculus.IsqBase
public import PropertyKindCalculus.Iso80000.Part4
public import PropertyKindCalculus.Iso80000.Part6

@[expose] public section Blanket

open Dimension

namespace PropertyKindCalculus.Iso80000.IsqLift

open PropertyKindCalculus PropertyKindCalculus.IsqBase

/-! ## Part 4 — mass, the energy family, action -/

/-- **The lift fixes the kind** — mass (item 4-1). -/
theorem mass_lift_kind :
    ((Part4.mass).mapDim toISQHom).kind = (Part4.mass).kind := rfl

/-- **Mass prints as `M`** — the catalogued dimension lands on the bare ISQ mass
generator. -/
theorem mass_lift_dim :
    ((Part4.mass).mapDim toISQHom).toDimension = single ISQDimensionBase.mass :=
  toISQHom_mass

/-- **The lift fixes the kind** — mechanical energy (item 4-28.3). -/
theorem mechanicalEnergy_lift_kind :
    ((Part4.mechanicalEnergy).mapDim toISQHom).kind = (Part4.mechanicalEnergy).kind := rfl

/-- **Mechanical energy prints as `M·L²·T⁻²`** — the catalogued dimension lands on the
standard's printed ISQ exponents. -/
theorem mechanicalEnergy_lift_dim :
    ((Part4.mechanicalEnergy).mapDim toISQHom).toDimension
      = single ISQDimensionBase.mass * single ISQDimensionBase.length ^ 2
          / single ISQDimensionBase.time ^ 2 := by
  show toISQHom Part4.MDim.energy = _
  ext b
  cases b <;>
    simp [toISQHom_apply, toISQFun, ofFunction_exponent, Part4.MDim.energy, Dim.mass,
      Dim.area, Dim.time, Dimension.M𝓭, Dimension.L𝓭, Dimension.T𝓭,
      Dimension.ofLTMCTDimensionBase, mul_exponent, div_exponent,
      single_exponent, Dimension.length, Dimension.time, Dimension.mass,
      Dimension.charge, Dimension.temperature] <;>
    norm_num

/-- Kinetic energy (item 4-28.2) shares the proof: same dimension, distinct kind. -/
theorem kineticEnergy_lift_dim :
    ((Part4.kineticEnergy).mapDim toISQHom).toDimension
      = single ISQDimensionBase.mass * single ISQDimensionBase.length ^ 2
          / single ISQDimensionBase.time ^ 2 :=
  mechanicalEnergy_lift_dim

/-- Potential energy (item 4-28.1) likewise. -/
theorem potentialEnergy_lift_dim :
    ((Part4.potentialEnergy).mapDim toISQHom).toDimension
      = single ISQDimensionBase.mass * single ISQDimensionBase.length ^ 2
          / single ISQDimensionBase.time ^ 2 :=
  mechanicalEnergy_lift_dim

/-- **And torque (item 4-12.2) shares it too** — the same `M·L²·T⁻²`, in the ISQ base as in
the canonical one: the collision the dimension functor cannot see survives the change of
basis, which is exactly why the *kind* layer, invariant under the lift, has to carry the
distinction. -/
theorem torque_lift_dim :
    ((Part4.torque).mapDim toISQHom).toDimension
      = single ISQDimensionBase.mass * single ISQDimensionBase.length ^ 2
          / single ISQDimensionBase.time ^ 2 :=
  mechanicalEnergy_lift_dim

/-- But the kinds stay apart under the lift: lifted torque and lifted mechanical energy are
distinct kinds with equal dimensions — the Part-4 textbook case, stated over ISQ. -/
theorem torque_ne_mechanicalEnergy_over_isq :
    ((Part4.torque).mapDim toISQHom).kind ≠ ((Part4.mechanicalEnergy).mapDim toISQHom).kind := by
  decide

/-- **The lift fixes the kind** — action (item 4-32, ℏ's kind). -/
theorem action_lift_kind :
    ((Part4.action).mapDim toISQHom).kind = (Part4.action).kind := rfl

/-- **Action prints as `M·L²·T⁻¹`** (`S`, J·s). -/
theorem action_lift_dim :
    ((Part4.action).mapDim toISQHom).toDimension
      = single ISQDimensionBase.mass * single ISQDimensionBase.length ^ 2
          / single ISQDimensionBase.time := by
  show toISQHom Part4.MDim.angularMomentum = _
  ext b
  cases b <;>
    simp [toISQHom_apply, toISQFun, ofFunction_exponent, Part4.MDim.angularMomentum,
      Dim.mass, Dim.area, Dim.time, Dimension.M𝓭, Dimension.L𝓭, Dimension.T𝓭,
      Dimension.ofLTMCTDimensionBase, mul_exponent, div_exponent,
      single_exponent, Dimension.length, Dimension.time, Dimension.mass,
      Dimension.charge, Dimension.temperature]
  norm_num

/-! ## Part 6 — the charge/current change of coordinates, on the printed entries -/

/-- **The lift fixes the kind** — electric current (item 6-1). -/
theorem electricCurrent_lift_kind :
    ((Part6.electricCurrent).mapDim toISQHom).kind = (Part6.electricCurrent).kind := rfl

/-- **The ampere prints as the bare `I` generator** — PhysLib's internal `C·T⁻¹` collapses
to the ISQ base quantity, on the catalogued item 6-1 itself. -/
theorem electricCurrent_lift_dim :
    ((Part6.electricCurrent).mapDim toISQHom).toDimension = single ISQDimensionBase.current :=
  toISQHom_current

/-- **The lift fixes the kind** — electric charge (item 6-2). -/
theorem electricCharge_lift_kind :
    ((Part6.electricCharge).mapDim toISQHom).kind = (Part6.electricCharge).kind := rfl

/-- **The coulomb prints as the product `I·T`** — the generator PhysLib takes as base maps
to a *product* over ISQ, the direction a mere generator reindexing cannot express, on the
catalogued item 6-2 itself. -/
theorem electricCharge_lift_dim :
    ((Part6.electricCharge).mapDim toISQHom).toDimension
      = single ISQDimensionBase.current * single ISQDimensionBase.time := by
  show toISQHom Dim.charge = _
  rw [toISQHom_charge]
  rfl

end PropertyKindCalculus.Iso80000.IsqLift

end Blanket
