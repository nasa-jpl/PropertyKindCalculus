/-
# ISO 80000-10 — defining relations from the Remarks (the algebraic remarks)

Several ISO 80000-10 *Remarks* and definitions state a quantity's **defining relation** to
other quantities — the constitutive laws of nuclear physics and dosimetry:

  * dose equivalent `H = D·Q` — absorbed dose times the (dimensionless) quality factor
    (item 10-83.1);
  * mean life `τ = 1/λ` — the reciprocal of the decay constant (item 10-25);
  * specific activity `a = A/m` — activity per mass (item 10-28; the mass is ISO 80000-4);
  * absorbed-dose rate `Ḋ = dD/dt` — absorbed dose per time (item 10-84; the time is
    ISO 80000-3);
  * mass attenuation coefficient `μ_m = μ/ρ` — linear attenuation per mass density
    (item 10-50; the density is ISO 80000-4).

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
product, reciprocal, and quotient families of `QuantityClassification`. Three payoffs:

  1. **Dosimetry is built from the other parts by the kind algebra.** Specific activity and
     the dose rate compose Part-10 kinds out of ISO 80000-3 (time) and -4 (mass) kinds.
  2. **The gray/sievert distinction holds under the algebra.** Dose equivalent is the
     product of absorbed dose with the *dimensionless* quality factor, so it carries the
     *same* dimension as absorbed dose (`doseEquivalent_dim_from_dose_quality`) — a checked
     computation that the two doses collide on `L²·T⁻²` *because* the quality factor is
     dimension one, yet remain distinct kinds (the gray and the sievert).
  3. **Verified construction and certificates instantiate at the quantity level.** A dose
     equivalent built as absorbed dose × quality factor carries its product certificate by
     construction, over the `ℝ` carrier.

No normative text from the licensed standard is reproduced; the relations are restated in
this work's own formalism.
-/

import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.Iso80000.Part10
import PropertyKindCalculus.QuantityClassification

namespace PropertyKindCalculus.Iso80000.Part10.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part10

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `ProductKind` / `ReciprocalKind` / `QuotientKind` instance: a proof that
the kinds involved are all ratio-scale, the precondition for multiplying, inverting, or
dividing quantities (Dybkær §13.3.5). For these catalogued kinds the scale facts hold by
reflexivity — including the **cross-part** dosimetry laws, whose ISO 80000-3 time and -4
mass factors are equally ratio-scale. -/

/-- **Dose equivalent is absorbed dose times the quality factor** (item 10-83.1:
`H = D·Q`). -/
theorem doseEquivalent_prod_dose_quality :
    ProductKind absorbedDose.kind qualityFactor.kind doseEquivalent.kind := ⟨rfl, rfl, rfl⟩

/-- **Mean life is the reciprocal of the decay constant** (item 10-25: `τ = 1/λ`). -/
theorem meanLife_recip_decayConstant :
    ReciprocalKind decayConstant.kind meanLife.kind := ⟨rfl, rfl⟩

/-- **Specific activity is activity per mass** (item 10-28: `a = A/m`) — a *cross-part*
law, the mass an ISO 80000-4 quantity. -/
theorem specificActivity_quot_activity_mass :
    QuotientKind activity.kind Part4.mass.kind specificActivity.kind := ⟨rfl, rfl, rfl⟩

/-- **Absorbed-dose rate is absorbed dose per time** (item 10-84: `Ḋ = dD/dt`) — a
*cross-part* law, the time an ISO 80000-3 quantity. -/
theorem absorbedDoseRate_quot_dose_duration :
    QuotientKind absorbedDose.kind Part3.duration.kind absorbedDoseRate.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Mass attenuation coefficient is linear attenuation per mass density** (item 10-50:
`μ_m = μ/ρ`) — a *cross-part* law, the density an ISO 80000-4 quantity. -/
theorem massAttenuation_quot_linear_density :
    QuotientKind linearAttenuationCoefficient.kind Part4.massDensity.kind
      massAttenuationCoefficient.kind := ⟨rfl, rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- **Dose equivalent keeps the dimension of absorbed dose because the quality factor is
dimension one.** From `H = D·Q` with `dim Q = 1`, the product leaves `L²·T⁻²` unchanged —
the two doses collide on one dimension, made a checked computation. They nonetheless remain
distinct kinds: the gray and the sievert (see `Part10.iso80000_10_dim_collision`). -/
theorem doseEquivalent_dim_from_dose_quality :
    doseEquivalent.dim = absorbedDose.dim * qualityFactor.dim := by
  show NDim.specificEnergy = NDim.specificEnergy * (1 : Dimension PhyslibBase)
  rw [mul_one]

/-- **Mean life is the reciprocal of the decay constant's dimension** (`τ = 1/λ`, so
`dim τ = T = (T⁻¹)⁻¹`). -/
theorem meanLife_dim_from_decayConstant :
    meanLife.dim = decayConstant.dim⁻¹ := by
  show Dim.time = (Dim.time⁻¹)⁻¹
  rw [inv_inv]

/-- Specific activity's dimension is activity over mass: `M⁻¹·T⁻¹` because `a = A/m`. A
checked cross-part computation. -/
theorem specificActivity_dim_from_activity_mass :
    specificActivity.dim = activity.dim / Part4.mass.dim := rfl

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructors build a classified quantity from its constituents, licensed by the
kind-law; the certificate holds by construction. -/

/-- A dose equivalent built as absorbed dose × quality factor — classified as a dose
equivalent **by construction** (`H = D·Q`). -/
noncomputable def doseEquivalentOf (d : Quantity absorbedDose.kind ℝ)
    (q : Quantity qualityFactor.kind ℝ) : Quantity doseEquivalent.kind ℝ :=
  Quantity.mul doseEquivalent_prod_dose_quality d q

/-- The constructed dose equivalent satisfies the product certificate by construction. -/
theorem doseEquivalentOf_isProduct (d : Quantity absorbedDose.kind ℝ)
    (q : Quantity qualityFactor.kind ℝ) :
    (doseEquivalentOf d q).IsProduct doseEquivalent_prod_dose_quality d q := rfl

/-- A specific activity built as activity / mass — classified **by construction**
(`a = A/m`), over `ℝ`. -/
noncomputable def specificActivityOf (a : Quantity activity.kind ℝ)
    (m : Quantity Part4.mass.kind ℝ) : Quantity specificActivity.kind ℝ :=
  Quantity.div specificActivity_quot_activity_mass a m

/-- The constructed specific activity satisfies the quotient certificate by construction. -/
theorem specificActivityOf_isQuotient (a : Quantity activity.kind ℝ)
    (m : Quantity Part4.mass.kind ℝ) :
    (specificActivityOf a m).IsQuotient specificActivity_quot_activity_mass a m := rfl

/-- **Canonicity, instantiated.** Any specific activity certified as a given activity per a
given mass equals the constructed one. -/
theorem specificActivity_certificate_canonical
    {a : Quantity activity.kind ℝ} {m : Quantity Part4.mass.kind ℝ}
    {sa : Quantity specificActivity.kind ℝ}
    (h : sa.IsQuotient specificActivity_quot_activity_mass a m) :
    sa = specificActivityOf a m :=
  Quantity.eq_div_of_isQuotient specificActivity_quot_activity_mass h

end PropertyKindCalculus.Iso80000.Part10.DefiningRelations
