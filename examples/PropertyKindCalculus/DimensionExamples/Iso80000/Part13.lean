/-
# Worked examples — IEC 80000-13 (Information science and technology)

Part-13 examples, mirroring the `Iso80000` library's own `Iso80000/Part13` layout:

1. the dimensional algebra (information content is dimension one, the bit rate `T⁻¹`, the
   carrier power `M·L²·T⁻³`, the signal energy per bit `M·L²·T⁻²`);
2. **dimension one, three incommensurable special units (R13)** — information content
   (shannon), traffic intensity (erlang), and storage capacity (bit) are distinct kinds all
   at dimension one, with the shannon not commensurable with the erlang or the bit;
3. **the rates re-dimension to `T⁻¹`** — the bit rate and the call intensity collide on
   `T⁻¹`, distinct kinds;
4. **defining relations** — signal energy per bit = carrier power × bit period, period =
   1 / rate;
5. **catalogue coverage** — all 42 items carry their source as data.

These live in the Mathlib-backed `DimensionExamples` library.
-/

import PropertyKindCalculus.Iso80000.Part13
import PropertyKindCalculus.Iso80000.Part13.DefiningRelations
import PropertyKindCalculus.QuantityReal

namespace PropertyKindCalculus.Examples.Iso80000.Part13

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part13
open PropertyKindCalculus.Iso80000.Part13.DefiningRelations

/-! ## (1) IEC 80000-13 — the dimensional algebra -/

example : informationContent.dim = 1 := informationContent_dim_eq_one
example : binaryDigitRate.dim.time = -1 := binaryDigitRate_dim_time
example : carrierPower.dim.time = -3 := carrierPower_dim_time
example : signalEnergyPerBinaryDigit.dim.time = -2 := signalEnergyPerBinaryDigit_dim_time

-- each kind carries its exact item citation as data
#guard informationContentCK.item == "13-24"
#guard trafficIntensityCK.item == "13-1"
#guard informationContentCK.cite == "IEC 80000-13, Edition 2.0, 2025-02 item 13-24"
#guard channelTimeCapacityCK.item == "13-42"

-- the shannon and the erlang are well-formed units
example : shannon.WellFormed := shannon_wellFormed
example : erlang.WellFormed := erlang_wellFormed

/-! ## (2) Dimension one, three incommensurable special units (requirement R13)

Information content (the shannon), traffic intensity (the erlang), and storage capacity (the
bit) are all dimension one, yet are different kinds with different human-selected
dimensionless units — the scale-spanning collision (R13) on information. -/

-- SAME DIMENSION: information content ≡ traffic intensity (dimension one).
example : informationContent.dim = trafficIntensity.dim :=
  informationContent_dim_eq_trafficIntensity_dim
-- DISTINCT KIND: yet they are not the same kind.
example : informationContent.kind ≠ trafficIntensity.kind :=
  informationContent_ne_trafficIntensity
-- and the shannon is not commensurable with the erlang, nor with the bit — three
-- dimensionless references for three kinds.
example : ¬ shannon.Commensurable erlang := shannon_erlang_not_commensurable
example : ¬ shannon.Commensurable bit := shannon_bit_not_commensurable
-- the dimension-1 capstone on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iec80000_13_dim_one_collision

/-! ## (3) The rates re-dimension to `T⁻¹`

Per-character entropies are dimension one, but the per-second rates carry `T⁻¹`: the bit
rate and the call intensity collide there, distinct kinds. -/

example : binaryDigitRate.dim = callIntensity.dim :=
  binaryDigitRate_dim_eq_callIntensity_dim
example : binaryDigitRate.kind ≠ callIntensity.kind := binaryDigitRate_ne_callIntensity
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim := iec80000_13_dim_collision

/-! ## (4) Defining relations: digital transmission built by the kind algebra

The signal energy per bit is carrier power times the bit period; the period is the
reciprocal of the rate. -/

-- DIM FROM RELATION: the signal energy per bit is `M·L²·T⁻²` *because* it is a power times a
-- time (`E_bit = P_c·T_bit`).
example : signalEnergyPerBinaryDigit.dim = carrierPower.dim * periodOfBinaryDigits.dim :=
  signalEnergy_dim_from_power_period
-- the period of data elements is `T` because it is the reciprocal of the transfer rate.
example : periodOfDataElements.dim = transferRate.dim⁻¹ :=
  periodOfDataElements_dim_from_transferRate

-- VERIFIED CONSTRUCTION (item 13-19): a signal energy built as carrier power × bit period
-- carries its product certificate by construction, over `ℝ`.
example (p : Quantity carrierPower.kind ℝ) (t : Quantity periodOfBinaryDigits.kind ℝ) :
    (signalEnergyOf p t).IsProduct signalEnergy_prod_power_period p t :=
  signalEnergyOf_isProduct p t

-- the signal-energy product instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `4 W · 3 s = 12 J` (at `Int`).
def signalEnergyInt : Quantity signalEnergyPerBinaryDigit.kind Int :=
  Quantity.mul signalEnergy_prod_power_period
    (⟨4⟩ : Quantity carrierPower.kind Int) (⟨3⟩ : Quantity periodOfBinaryDigits.kind Int)
#guard signalEnergyInt.magnitude == 12

/-! ## (5) Catalogue coverage — all 42 items carry their source as data -/

#guard PropertyKindCalculus.Iso80000.Part13.catalogue.length == 42
#guard trafficIntensityCK.item == "13-1"
#guard storageCapacityCK.item == "13-9"
#guard entropyCK.item == "13-25"
#guard channelTimeCapacityCK.item == "13-42"
#guard informationContentCK.coherentUnit == "Sh"
#guard trafficIntensityCK.coherentUnit == "E"
#guard storageCapacityCK.coherentUnit == "bit"

end PropertyKindCalculus.Examples.Iso80000.Part13
