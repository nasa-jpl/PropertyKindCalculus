/-
# ISO 80000-8 — defining relations from the Remarks (the algebraic remarks)

Several ISO 80000-8 *Remarks* and definitions state a quantity's **defining relation** to
other quantities as a quotient or a product — the constitutive laws of linear acoustics:

  * sound particle velocity `u = ∂δ/∂t` — particle displacement per time (item 8-4; the
    time is ISO 80000-3);
  * sound particle acceleration `a = ∂u/∂t` — particle velocity per time (item 8-5);
  * sound intensity `I = p·u` — sound pressure times particle velocity (item 8-10);
  * characteristic impedance `Z_c = p/u` — sound pressure per particle velocity
    (item 8-12);
  * acoustic impedance `Z_a = p̄/q_V` — sound pressure per volume flow rate (item 8-13).

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
product and quotient families of `QuantityClassification`. Three payoffs:

  1. **Linear acoustics is built from one another by the kind algebra.** The kinematic
     chain (displacement → velocity → acceleration) and the field quantities (intensity,
     the impedances) compose Part-8 kinds out of one another, and the kinematics cross to
     ISO 80000-3 for their time factor.
  2. **The dimension follows from the relation, as a checked computation.** The sound
     intensity is `M·T⁻³` *because* it is sound pressure times particle velocity
     (`soundIntensity_dim_from_pressure_velocity`), and the two impedances differ in
     dimension *because* one divides by velocity and the other by volume flow rate — the
     extra `L²` made a checked computation.
  3. **Verified construction and certificates instantiate at the quantity level.** A sound
     intensity built as pressure × velocity carries its product certificate by
     construction, over the `ℝ` carrier.

No normative text from the licensed standard is reproduced; the relations are restated in
this work's own formalism.
-/

import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part8
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.QuantityReal

namespace PropertyKindCalculus.Iso80000.Part8.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part8

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `ProductKind` / `QuotientKind` instance: a proof that the kinds
involved are all ratio-scale, the precondition for multiplying or dividing quantities
(Dybkær §13.3.5). For these catalogued kinds the scale facts hold by reflexivity —
including the **cross-part** kinematic laws, whose ISO 80000-3 time factor
(`Part3.duration`) is equally ratio-scale. -/

/-- **Sound particle velocity is particle displacement per time** (item 8-4:
`u = ∂δ/∂t`) — a *cross-part* law, the time an ISO 80000-3 quantity. -/
theorem particleVelocity_quot_displacement_duration :
    QuotientKind particleDisplacement.kind Part3.duration.kind particleVelocity.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Sound particle acceleration is particle velocity per time** (item 8-5:
`a = ∂u/∂t`) — a *cross-part* law. -/
theorem particleAcceleration_quot_velocity_duration :
    QuotientKind particleVelocity.kind Part3.duration.kind particleAcceleration.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Sound intensity is sound pressure times particle velocity** (item 8-10:
`I = p·u`). -/
theorem soundIntensity_prod_pressure_velocity :
    ProductKind soundPressure.kind particleVelocity.kind soundIntensity.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Characteristic impedance is sound pressure per particle velocity** (item 8-12:
`Z_c = p/u`). -/
theorem characteristicImpedance_quot_pressure_velocity :
    QuotientKind soundPressure.kind particleVelocity.kind characteristicImpedance.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Acoustic impedance is sound pressure per volume flow rate** (item 8-13:
`Z_a = p̄/q_V`). -/
theorem acousticImpedance_quot_pressure_volumeFlow :
    QuotientKind soundPressure.kind volumeFlowRate.kind acousticImpedance.kind :=
  ⟨rfl, rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- Particle velocity's dimension is displacement over time: `L·T⁻¹` because `u = ∂δ/∂t`.
A checked cross-part computation (the time is `T` from ISO 80000-3). -/
theorem particleVelocity_dim_from_displacement_duration :
    particleVelocity.dim = particleDisplacement.dim / Part3.duration.dim := rfl

/-- **Sound intensity is `M·T⁻³` because it is sound pressure times particle velocity.**
From `I = p·u` with `dim p = M·L⁻¹·T⁻²` and `dim u = L·T⁻¹`, the length cancels — a
checked computation realizing the acoustic intensity law at the dimensional level. -/
theorem soundIntensity_dim_from_pressure_velocity :
    soundIntensity.dim = soundPressure.dim * particleVelocity.dim := by
  show ADim.intensity = ADim.pressure * ADim.velocity
  rw [ADim.intensity, ADim.pressure, ADim.velocity, Dim.power, Dim.energy, Dim.speed,
    Dim.force, Dim.area, Dim.length, Dim.time]
  ext b
  simp only [Dimension.div_exponent, Dimension.mul_exponent]
  ring

/-- Characteristic impedance's dimension is sound pressure over particle velocity:
`M·L⁻²·T⁻¹` because `Z_c = p/u`. -/
theorem characteristicImpedance_dim_from_pressure_velocity :
    characteristicImpedance.dim = soundPressure.dim / particleVelocity.dim := rfl

/-- Acoustic impedance's dimension is sound pressure over volume flow rate: `M·L⁻⁴·T⁻¹`
because `Z_a = p̄/q_V`. The extra `L²` over the characteristic impedance (which divides by
velocity, `L·T⁻¹`, not volume flow rate, `L³·T⁻¹`) is what lets the dimension tell the two
homonymous impedances apart. -/
theorem acousticImpedance_dim_from_pressure_volumeFlow :
    acousticImpedance.dim = soundPressure.dim / volumeFlowRate.dim := rfl

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructors build a classified quantity from its constituents, licensed by the
kind-law; the certificate holds by construction, and (canonicity) any quantity carrying
the certificate equals the constructed one. -/

/-- A sound intensity built as sound pressure × particle velocity — classified as a sound
intensity **by construction** (`I = p·u`). -/
noncomputable def soundIntensityOf (p : Quantity soundPressure.kind ℝ)
    (u : Quantity particleVelocity.kind ℝ) : Quantity soundIntensity.kind ℝ :=
  Quantity.mul soundIntensity_prod_pressure_velocity p u

/-- The constructed sound intensity satisfies the product certificate by construction. -/
theorem soundIntensityOf_isProduct (p : Quantity soundPressure.kind ℝ)
    (u : Quantity particleVelocity.kind ℝ) :
    (soundIntensityOf p u).IsProduct soundIntensity_prod_pressure_velocity p u := rfl

/-- A characteristic impedance built as sound pressure / particle velocity — classified
**by construction** (`Z_c = p/u`), over `ℝ`. -/
noncomputable def characteristicImpedanceOf (p : Quantity soundPressure.kind ℝ)
    (u : Quantity particleVelocity.kind ℝ) : Quantity characteristicImpedance.kind ℝ :=
  Quantity.div characteristicImpedance_quot_pressure_velocity p u

/-- The constructed characteristic impedance satisfies the quotient certificate by
construction. -/
theorem characteristicImpedanceOf_isQuotient (p : Quantity soundPressure.kind ℝ)
    (u : Quantity particleVelocity.kind ℝ) :
    (characteristicImpedanceOf p u).IsQuotient
      characteristicImpedance_quot_pressure_velocity p u := rfl

/-- **Canonicity, instantiated.** Any characteristic impedance certified as a given sound
pressure per a given particle velocity equals the constructed one. -/
theorem characteristicImpedance_certificate_canonical
    {p : Quantity soundPressure.kind ℝ} {u : Quantity particleVelocity.kind ℝ}
    {z : Quantity characteristicImpedance.kind ℝ}
    (h : z.IsQuotient characteristicImpedance_quot_pressure_velocity p u) :
    z = characteristicImpedanceOf p u :=
  Quantity.eq_div_of_isQuotient characteristicImpedance_quot_pressure_velocity h

end PropertyKindCalculus.Iso80000.Part8.DefiningRelations
