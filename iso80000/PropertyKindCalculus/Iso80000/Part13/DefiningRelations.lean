/-
# IEC 80000-13 — defining relations from the Remarks (the algebraic remarks)

Several IEC 80000-13 *Remarks* state a quantity's **defining relation** to others — the
constitutive laws of digital transmission:

  * signal energy per binary digit `E_bit = P_c·T_bit` — carrier power times the bit period
    (item 13-19);
  * period of data elements `T = 1/r` — the reciprocal of the transfer rate (item 13-12);
  * period of binary digits `T_bit = 1/r_bit` — the reciprocal of the bit rate (item 13-14).

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
product and reciprocal families of `QuantityClassification`. Two payoffs:

  1. **Digital transmission is built from the kind algebra.** The signal energy and the
     periods compose Part-13 kinds out of one another.
  2. **The dimension follows from the relation, as a checked computation.** The signal
     energy per bit is `M·L²·T⁻²` *because* it is a power times a time
     (`signalEnergy_dim_from_power_period`), and the period is `T` because it is the
     reciprocal of a rate (`periodOfDataElements_dim_from_transferRate`).

No normative text from the licensed standard is reproduced; the relations are restated in
this work's own formalism.
-/

module

public import PropertyKindCalculus.Iso80000.Part13
public import PropertyKindCalculus.QuantityClassification
public import PropertyKindCalculus.QuantityReal

@[expose] public section Blanket

namespace PropertyKindCalculus.Iso80000.Part13.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part13

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `ProductKind` / `ReciprocalKind` instance over ratio-scale kinds — the
precondition for multiplying or inverting quantities (Dybkær §13.3.5). -/

/-- **Signal energy per binary digit is carrier power times the bit period** (item 13-19:
`E_bit = P_c·T_bit`). -/
theorem signalEnergy_prod_power_period :
    ProductKind carrierPower.kind periodOfBinaryDigits.kind
      signalEnergyPerBinaryDigit.kind := ⟨rfl, rfl, rfl⟩

/-- **The period of data elements is the reciprocal of the transfer rate** (item 13-12:
`T = 1/r`). -/
theorem periodOfDataElements_recip_transferRate :
    ReciprocalKind transferRate.kind periodOfDataElements.kind := ⟨rfl, rfl⟩

/-- **The period of binary digits is the reciprocal of the bit rate** (item 13-14:
`T_bit = 1/r_bit`). -/
theorem periodOfBinaryDigits_recip_binaryDigitRate :
    ReciprocalKind binaryDigitRate.kind periodOfBinaryDigits.kind := ⟨rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- **Signal energy per binary digit is `M·L²·T⁻²` because it is a power times a time.**
From `E_bit = P_c·T_bit`, the time-exponent of power (`-3`) and the time (`+1`) combine to
`-2` — a checked computation realizing the energy relation at the dimensional level. -/
theorem signalEnergy_dim_from_power_period :
    signalEnergyPerBinaryDigit.dim = carrierPower.dim * periodOfBinaryDigits.dim := by
  show Dim.energy = Dim.power * Dim.time
  rw [Dim.power, Dim.energy, Dim.force, Dim.length, Dim.time]
  ext b
  simp only [Dimension.div_exponent, Dimension.mul_exponent]
  ring

/-- **The period of data elements is the reciprocal of the transfer rate's dimension**
(`T = 1/r`, so `dim T = T = (T⁻¹)⁻¹`). -/
theorem periodOfDataElements_dim_from_transferRate :
    periodOfDataElements.dim = transferRate.dim⁻¹ := by
  show Dim.time = (Dim.time⁻¹)⁻¹
  rw [inv_inv]

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructor builds a classified quantity from its constituents, licensed by the
kind-law; the certificate holds by construction. -/

/-- A signal energy per binary digit built as carrier power × bit period — classified **by
construction** (`E_bit = P_c·T_bit`). -/
noncomputable def signalEnergyOf (p : Quantity carrierPower.kind ℝ)
    (t : Quantity periodOfBinaryDigits.kind ℝ) :
    Quantity signalEnergyPerBinaryDigit.kind ℝ :=
  Quantity.mul signalEnergy_prod_power_period p t

/-- The constructed signal energy satisfies the product certificate by construction. -/
theorem signalEnergyOf_isProduct (p : Quantity carrierPower.kind ℝ)
    (t : Quantity periodOfBinaryDigits.kind ℝ) :
    (signalEnergyOf p t).IsProduct signalEnergy_prod_power_period p t := rfl

end PropertyKindCalculus.Iso80000.Part13.DefiningRelations

end Blanket
