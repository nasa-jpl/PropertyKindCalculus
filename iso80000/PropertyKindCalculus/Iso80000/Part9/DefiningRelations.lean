/-
# ISO 80000-9 — defining relations from the Remarks (the algebraic remarks)

The molar quantities of ISO 80000-9 are defined as quotients *by the amount of substance*
— the constitutive form that, the mole reducing to dimension one (R13), makes each molar
quantity carry the dimension of its non-molar counterpart:

  * molar mass `M = m/n` — mass per amount of substance (item 9-4; the mass is
    ISO 80000-4);
  * molar volume `V_m = V/n` — volume per amount of substance (item 9-5; the volume is
    ISO 80000-3);
  * amount-of-substance concentration `c = n/V` — amount per volume (item 9-12.1);
  * molar internal energy `U_m = U/n` — internal energy per amount (item 9-6.1; the energy
    is ISO 80000-5);
  * molality `b = n/m` — amount of solute per mass of solvent (item 9-15).

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
quotient family of `QuantityClassification`. Three payoffs:

  1. **Physical chemistry is built from the other parts by the kind algebra.** The molar
     quantities compose Part-9 kinds out of ISO 80000-3 (volume), -4 (mass), and -5
     (energy) kinds and the mole.
  2. **The mole reduces, as a checked computation.** Molar mass carries the dimension of
     mass *because* `M = m/n` and `dim n = 1` (`molarMass_dim_from_mass_amount`); the
     amount concentration is a number density *because* `c = n/V` divides a dimensionless
     count by a volume (`amountConcentration_dim_from_amount_volume`). The `/mol` is
     invisible to the dimension functor — R13 made a theorem.
  3. **Verified construction and certificates instantiate at the quantity level.** A molar
     mass built as mass / amount carries its quotient certificate by construction, over the
     `ℝ` carrier.

No normative text from the licensed standard is reproduced; the relations are restated in
this work's own formalism.
-/

import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.Iso80000.Part5
import PropertyKindCalculus.Iso80000.Part9
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.QuantityReal

namespace PropertyKindCalculus.Iso80000.Part9.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part9

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `QuotientKind` instance: a proof that the kinds involved are all
ratio-scale, the precondition for dividing quantities (Dybkær §13.3.5). For these
catalogued kinds the scale facts hold by reflexivity — including the **cross-part** molar
laws, whose ISO 80000-3 volume, -4 mass, and -5 energy factors are equally ratio-scale. -/

/-- **Molar mass is mass per amount of substance** (item 9-4: `M = m/n`) — a *cross-part*
law, the mass an ISO 80000-4 quantity. -/
theorem molarMass_quot_mass_amount :
    QuotientKind Part4.mass.kind amountOfSubstance.kind molarMass.kind := ⟨rfl, rfl, rfl⟩

/-- **Molar volume is volume per amount of substance** (item 9-5: `V_m = V/n`) — a
*cross-part* law, the volume an ISO 80000-3 quantity. -/
theorem molarVolume_quot_volume_amount :
    QuotientKind Part3.volume.kind amountOfSubstance.kind molarVolume.kind := ⟨rfl, rfl, rfl⟩

/-- **Amount-of-substance concentration is amount per volume** (item 9-12.1: `c = n/V`) —
a *cross-part* law, the volume an ISO 80000-3 quantity. -/
theorem amountConcentration_quot_amount_volume :
    QuotientKind amountOfSubstance.kind Part3.volume.kind amountConcentration.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Molar internal energy is internal energy per amount of substance** (item 9-6.1:
`U_m = U/n`) — a *cross-part* law, the energy an ISO 80000-5 quantity. -/
theorem molarInternalEnergy_quot_energy_amount :
    QuotientKind Part5.internalEnergy.kind amountOfSubstance.kind molarInternalEnergy.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Molality is amount of solute per mass of solvent** (item 9-15: `b = n/m`) — a
*cross-part* law, the mass an ISO 80000-4 quantity. -/
theorem molality_quot_amount_mass :
    QuotientKind amountOfSubstance.kind Part4.mass.kind molality.kind := ⟨rfl, rfl, rfl⟩

/-! ## (2) The mole reduces — the dimension follows from the relation (checked) -/

/-- **Molar mass carries the dimension of mass because the mole is dimension one.** From
`M = m/n` with `dim n = 1`, the division by the amount of substance leaves `M` unchanged —
the `/mol` reducing away (R13), made a checked computation. -/
theorem molarMass_dim_from_mass_amount :
    molarMass.dim = Part4.mass.dim / amountOfSubstance.dim := by
  show Dim.mass = Dim.mass / Dim.amountOfSubstance
  rw [Dim.amountOfSubstance_eq_one, div_one]

/-- **The amount-of-substance concentration is a number density because the mole is
dimension one.** From `c = n/V` with `dim n = 1`, the dimension is `1/V = L⁻³` — the same
as a particle concentration, the mole reduced. -/
theorem amountConcentration_dim_from_amount_volume :
    amountConcentration.dim = amountOfSubstance.dim / Part3.volume.dim := by
  show PDim.numberDensity = Dim.amountOfSubstance / (Dim.area * Dim.length)
  rw [Dim.amountOfSubstance_eq_one, one_div, PDim.numberDensity, PDim.volume]

/-- **Molar volume carries the dimension of volume** (`V_m = V/n`, the mole reduced). -/
theorem molarVolume_dim_from_volume_amount :
    molarVolume.dim = Part3.volume.dim / amountOfSubstance.dim := by
  show PDim.volume = (Dim.area * Dim.length) / Dim.amountOfSubstance
  rw [Dim.amountOfSubstance_eq_one, div_one, PDim.volume]

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructor builds a classified quantity from its constituents, licensed by the
kind-law; the certificate holds by construction, and (canonicity) any quantity carrying
the certificate equals the constructed one. -/

/-- A molar mass built as mass / amount of substance — classified as a molar mass **by
construction** (`M = m/n`). -/
noncomputable def molarMassOf (m : Quantity Part4.mass.kind ℝ)
    (n : Quantity amountOfSubstance.kind ℝ) : Quantity molarMass.kind ℝ :=
  Quantity.div molarMass_quot_mass_amount m n

/-- The constructed molar mass satisfies the quotient certificate by construction. -/
theorem molarMassOf_isQuotient (m : Quantity Part4.mass.kind ℝ)
    (n : Quantity amountOfSubstance.kind ℝ) :
    (molarMassOf m n).IsQuotient molarMass_quot_mass_amount m n := rfl

/-- **Canonicity, instantiated.** Any molar mass certified as a given mass per a given
amount of substance equals the constructed one. -/
theorem molarMass_certificate_canonical
    {m : Quantity Part4.mass.kind ℝ} {n : Quantity amountOfSubstance.kind ℝ}
    {mm : Quantity molarMass.kind ℝ}
    (h : mm.IsQuotient molarMass_quot_mass_amount m n) :
    mm = molarMassOf m n :=
  Quantity.eq_div_of_isQuotient molarMass_quot_mass_amount h

/-- An amount-of-substance concentration built as amount / volume — classified **by
construction** (`c = n/V`), over `ℝ`. -/
noncomputable def amountConcentrationOf (n : Quantity amountOfSubstance.kind ℝ)
    (v : Quantity Part3.volume.kind ℝ) : Quantity amountConcentration.kind ℝ :=
  Quantity.div amountConcentration_quot_amount_volume n v

/-- The constructed amount concentration satisfies the quotient certificate by
construction. -/
theorem amountConcentrationOf_isQuotient (n : Quantity amountOfSubstance.kind ℝ)
    (v : Quantity Part3.volume.kind ℝ) :
    (amountConcentrationOf n v).IsQuotient amountConcentration_quot_amount_volume n v := rfl

end PropertyKindCalculus.Iso80000.Part9.DefiningRelations
