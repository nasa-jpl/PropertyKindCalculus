/-
# ISO 80000-4 — defining relations from the Remarks (the algebraic remarks)

Many ISO 80000-4 *Remarks* state a quantity's **defining relation** to other
quantities as a product, quotient, or reciprocal — and, characteristically of
mechanics, the other quantities are often *space-and-time* quantities from Part 3:

  * mass density `ρ = m/V` — mass per volume (item 4-2; volume is ISO 80000-3);
  * specific volume `v = 1/ρ` — the reciprocal of mass density (item 4-3);
  * momentum `p = m·v` — mass times velocity (item 4-8; velocity is ISO 80000-3);
  * pressure `p = F/A` — force per area (item 4-14.1; area is ISO 80000-3);
  * kinematic viscosity `ν = η/ρ` — dynamic viscosity per mass density (item 4-25);
  * efficiency `η = P_out/P_in` — output power per input power, so the powers cancel
    and the efficiency is dimension one (item 4-29);
  * modulus of elasticity `E = σ/ε` — normal stress per relative linear strain
    (item 4-19.1).

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
product, quotient, and reciprocal families of `QuantityClassification`. Three payoffs:

  1. **Mechanics is built from space and time.** The kind-laws compose Part-4 kinds
     out of Part-3 kinds — momentum from mass and velocity, pressure from force and
     area — so the cross-part dependency structure of the ISQ is made explicit and
     checked, not left to prose.
  2. **The dimension follows from the relation, as a checked computation.** Efficiency
     is dimension one *because* it is a ratio of two powers
     (`efficiency_dim_from_power_ratio`), exactly as a plane angle is dimensionless
     because it is a ratio of two lengths — yet it remains a distinct kind from every
     other dimension-one quantity.
  3. **Verified construction and certificates instantiate at the quantity level.** A
     momentum built as mass × velocity carries its classification certificate by
     construction (`momentumOf_isProduct`), and the certificate determines the
     quantity (canonicity), over the `ℝ` carrier.

No normative text from the licensed standard is reproduced; the relations are
restated in this work's own formalism.
-/

import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.QuantityReal

namespace PropertyKindCalculus.Iso80000.Part4.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part4

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `ProductKind` / `QuotientKind` / `ReciprocalKind` instance: a proof
that the kinds involved are all ratio-scale, the precondition for multiplying,
dividing, or inverting quantities (Dybkær §13.3.5). For these catalogued kinds the
scale facts hold by reflexivity — including the **cross-part** ones, whose Part-3
factors (`Part3.volume`, `Part3.velocity`, `Part3.area`) are equally ratio-scale. -/

/-- **Mass density is mass per volume** (item 4-2: `ρ = m/V`) — a *cross-part* law,
since the volume is an ISO 80000-3 quantity. -/
theorem massDensity_quot_mass_volume :
    QuotientKind mass.kind Part3.volume.kind massDensity.kind := ⟨rfl, rfl, rfl⟩

/-- **Specific volume is the reciprocal of mass density** (item 4-3: `v = 1/ρ`). -/
theorem specificVolume_recip_massDensity :
    ReciprocalKind massDensity.kind specificVolume.kind := ⟨rfl, rfl⟩

/-- **Momentum is mass times velocity** (item 4-8: `p = m·v`) — a *cross-part* law,
since the velocity is an ISO 80000-3 quantity. -/
theorem momentum_prod_mass_velocity :
    ProductKind mass.kind Part3.velocity.kind momentum.kind := ⟨rfl, rfl, rfl⟩

/-- **Pressure is force per area** (item 4-14.1: `p = F/A`) — a *cross-part* law,
since the area is an ISO 80000-3 quantity. -/
theorem pressure_quot_force_area :
    QuotientKind force.kind Part3.area.kind pressure.kind := ⟨rfl, rfl, rfl⟩

/-- **Kinematic viscosity is dynamic viscosity per mass density** (item 4-25:
`ν = η/ρ`). -/
theorem kinematicViscosity_quot_dynamicViscosity_massDensity :
    QuotientKind dynamicViscosity.kind massDensity.kind kinematicViscosity.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Efficiency is output power per input power** (item 4-29: `η = P_out/P_in`). -/
theorem efficiency_quot_power_power :
    QuotientKind power.kind power.kind efficiency.kind := ⟨rfl, rfl, rfl⟩

/-- **Modulus of elasticity is normal stress per relative linear strain** (item 4-19.1:
`E = σ/ε`). -/
theorem modulusOfElasticity_quot_normalStress_relativeLinearStrain :
    QuotientKind normalStress.kind relativeLinearStrain.kind modulusOfElasticity.kind :=
  ⟨rfl, rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- Mass density's dimension is mass over volume: `M·L⁻³` because `ρ = m/V`. A checked
computation that crosses parts (the volume is `L³` from ISO 80000-3). -/
theorem massDensity_dim_from_mass_volume :
    massDensity.dim = mass.dim / Part3.volume.dim := rfl

/-- Momentum's dimension is mass times velocity: `M·L·T⁻¹` because `p = m·v`. A checked
cross-part computation (the velocity is `L·T⁻¹` from ISO 80000-3). -/
theorem momentum_dim_from_mass_velocity :
    momentum.dim = mass.dim * Part3.velocity.dim := rfl

/-- Modulus of elasticity's dimension equals normal stress's: `M·L⁻¹·T⁻²` because
`E = σ/ε` and the strain is dimensionless. -/
theorem modulusOfElasticity_dim_from_stress_strain :
    modulusOfElasticity.dim = normalStress.dim / relativeLinearStrain.dim := by
  simp [modulusOfElasticity, normalStress, relativeLinearStrain, dimKind, Dim.one]

/-- **Efficiency is dimension one because it is a ratio of two powers.** Output and
input power are both `M·L²·T⁻³`, so `η = P_out/P_in` cancels the dimension — the
efficiency's dimensionlessness is a *checked computation from its defining relation*,
not a stipulation. (It nonetheless remains a distinct kind from every other
dimension-one quantity; see `Part4.iso80000_4_dim_one_collision`.) This is the
mechanics analogue of the plane angle being a ratio of two lengths. -/
theorem efficiency_dim_from_power_ratio :
    efficiency.dim = power.dim / power.dim := by
  simp [efficiency, dimKind, Dim.one]

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructors build a classified quantity from its constituents, licensed by
the kind-law; the certificate holds by construction, and (canonicity) any quantity
carrying the certificate equals the constructed one. The momentum constructor crosses
parts: it consumes a mass (Part 4) and a velocity (Part 3). -/

/-- A momentum built as mass × velocity — classified as a momentum **by construction**
(and built from a Part-4 mass and a Part-3 velocity). -/
noncomputable def momentumOf (m : Quantity mass.kind ℝ)
    (v : Quantity Part3.velocity.kind ℝ) : Quantity momentum.kind ℝ :=
  Quantity.mul momentum_prod_mass_velocity m v

/-- The constructed momentum satisfies the product certificate by construction. -/
theorem momentumOf_isProduct (m : Quantity mass.kind ℝ)
    (v : Quantity Part3.velocity.kind ℝ) :
    (momentumOf m v).IsProduct momentum_prod_mass_velocity m v := rfl

/-- **Canonicity, instantiated.** Any momentum certified as mass × a given velocity
equals the constructed one — a kind-law applied at the quantity level. -/
theorem momentum_certificate_canonical {m : Quantity mass.kind ℝ}
    {v : Quantity Part3.velocity.kind ℝ} {p : Quantity momentum.kind ℝ}
    (h : p.IsProduct momentum_prod_mass_velocity m v) : p = momentumOf m v :=
  Quantity.eq_mul_of_isProduct momentum_prod_mass_velocity h

/-- A pressure built as force / area — classified as a pressure **by construction**
(and built from a Part-4 force and a Part-3 area). -/
noncomputable def pressureOf (f : Quantity force.kind ℝ)
    (a : Quantity Part3.area.kind ℝ) : Quantity pressure.kind ℝ :=
  Quantity.div pressure_quot_force_area f a

/-- The constructed pressure satisfies the quotient certificate by construction. -/
theorem pressureOf_isQuotient (f : Quantity force.kind ℝ)
    (a : Quantity Part3.area.kind ℝ) :
    (pressureOf f a).IsQuotient pressure_quot_force_area f a := rfl

/-- An efficiency built as output power / input power — classified as an efficiency
**by construction** (and dimensionless by `efficiency_dim_from_power_ratio`). -/
noncomputable def efficiencyOf (pOut pIn : Quantity power.kind ℝ) :
    Quantity efficiency.kind ℝ :=
  Quantity.div efficiency_quot_power_power pOut pIn

/-- The constructed efficiency satisfies the quotient certificate by construction. -/
theorem efficiencyOf_isQuotient (pOut pIn : Quantity power.kind ℝ) :
    (efficiencyOf pOut pIn).IsQuotient efficiency_quot_power_power pOut pIn := rfl

end PropertyKindCalculus.Iso80000.Part4.DefiningRelations
