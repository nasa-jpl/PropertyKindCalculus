/-
# Worked examples — ISO 80000-8 (Acoustics)

Part-8 examples, mirroring the `Iso80000` library's own `Iso80000/Part8` layout:

1. the dimensional algebra (sound pressure is `M·L⁻¹·T⁻²`, sound intensity `M·T⁻³`,
   reverberation time `T`);
2. **the logarithmic levels collapse to dimension one (R1)** — sound pressure level,
   sound power level, and sound exposure level are distinct kinds the dimension functor
   sends to a single point, with `dB` no more making one the other than `1` makes a
   Reynolds number a Froude number;
3. **a genuine dimension collision** — sound pressure ≡ sound energy density
   (`M·L⁻¹·T⁻²`), the pascal and the joule-per-cubic-metre not commensurable;
4. **the boundary case** — the two homonymous *impedances* the dimension *does* tell
   apart (`Pa·s/m` versus `Pa·s/m³`);
5. **defining relations** — particle velocity = displacement / time, sound intensity =
   pressure × velocity (a product), the impedances as quotients; the kinematics cross to
   ISO 80000-3;
6. **catalogue coverage** — all 18 items carry their source as data.

These live in the Mathlib-backed `DimensionExamples` library.
-/

import PropertyKindCalculus.Iso80000.Part8
import PropertyKindCalculus.Iso80000.Part8.DefiningRelations
import PropertyKindCalculus.QuantityReal

namespace PropertyKindCalculus.Examples.Iso80000.Part8

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part8
open PropertyKindCalculus.Iso80000.Part8.DefiningRelations

/-! ## (1) ISO 80000-8 — the dimensional algebra -/

-- sound pressure is `M·L⁻¹·T⁻²` (the pascal)
example : soundPressure.dim.mass = 1 := soundPressure_dim_mass
example : soundPressure.dim.length = -1 := soundPressure_dim_length
-- sound intensity is `M·T⁻³`; reverberation time is `T`
example : soundIntensity.dim.time = -3 := soundIntensity_dim_time
example : reverberationTime.dim.time = 1 := reverberationTime_dim_time

-- each kind carries its exact item citation as data
#guard soundPressureCK.item == "8-2.2"
#guard soundIntensityCK.item == "8-10"
#guard soundIntensityCK.cite == "ISO 80000-8, Second edition, 2020-02 item 8-10"
#guard reverberationTimeCK.item == "8-17"

-- the pascal and the decibel are well-formed units
example : pascalSound.WellFormed := pascalSound_wellFormed
example : decibelPressure.WellFormed := decibelPressure_wellFormed

/-! ## (2) The logarithmic levels collapse to dimension one (requirement R1)

Sound pressure level, sound power level, and sound exposure level (8-14 … 8-16) are each
`10·lg(quantity / reference)` — ratios on a logarithmic scale, dimension one, reported in
the decibel. Each is the level of a *different* base quantity, and that keeps them apart. -/

-- DIMENSION ONE: the levels all forget to the dimensionless point.
example : soundPressureLevel.dim = 1 := rfl
example : soundPowerLevel.dim = 1 := rfl
example : soundExposureLevel.dim = 1 := rfl
-- DISTINCT KIND: the sound pressure level is not the sound power level …
example : soundPressureLevel.kind ≠ soundPowerLevel.kind :=
  soundPressureLevel_ne_soundPowerLevel
-- … and their decibel units are not commensurable, *though both are* `dB` *and dimension
-- one* — the ISO 80000-11 `"1"` pattern (Reynolds vs Euler) on the acoustic levels.
example : ¬ decibelPressure.Commensurable decibelPower :=
  decibelPressure_decibelPower_not_commensurable
-- the dimension-1 capstone on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_8_dim_one_collision

/-! ## (3) A genuine dimension collision — sound pressure ≡ sound energy density

Sound pressure (`Pa`) and sound energy density (`J/m³`) carry the *same* dimension
`M·L⁻¹·T⁻²` — force per area equals energy per volume — yet are different kinds. -/

-- SAME DIMENSION: pressure ≡ energy density (`M·L⁻¹·T⁻²`).
example : soundPressure.dim = soundEnergyDensity.dim :=
  soundPressure_dim_eq_energyDensity_dim
-- DISTINCT KIND: yet they are not the same kind.
example : soundPressure.kind ≠ soundEnergyDensity.kind :=
  soundPressure_ne_soundEnergyDensity
-- and the pascal and the joule-per-cubic-metre are not commensurable.
example : ¬ pascalSound.Commensurable joulePerCubicMetre :=
  pascalSound_joulePerCubicMetre_not_commensurable
-- the collision capstone on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  iso80000_8_dim_collision

/-! ## (4) The boundary case — where the dimension *does* discriminate

The characteristic impedance of a medium (`Pa·s/m`, `M·L⁻²·T⁻¹`) and the acoustic
impedance (`Pa·s/m³`, `M·L⁻⁴·T⁻¹`) are both named an "impedance", but here the dimension
tells the homonyms apart — dimension is a *necessary* discriminator, and this is one of
the cases where it is also sufficient. -/

-- the two impedances carry DIFFERENT length-exponents (-2 versus -4): the dimension
-- separates them where, for the levels and the pressures, it could not.
example : characteristicImpedance.dim = soundPressure.dim / particleVelocity.dim :=
  characteristicImpedance_dim_from_pressure_velocity
example : acousticImpedance.dim = soundPressure.dim / volumeFlowRate.dim :=
  acousticImpedance_dim_from_pressure_volumeFlow

/-! ## (5) Defining relations: linear acoustics built by the kind algebra

Particle velocity is the time-derivative of displacement, sound intensity the product of
sound pressure and particle velocity, the impedances quotients; the kinematics cross to
ISO 80000-3. -/

-- DIM FROM RELATION: particle velocity's `L·T⁻¹` follows from displacement / time
-- (cross-part, the time from ISO 80000-3).
example : particleVelocity.dim = particleDisplacement.dim / Part3.duration.dim :=
  particleVelocity_dim_from_displacement_duration
-- ALGEBRAIC REMARK (item 8-10): sound intensity is `M·T⁻³` *because* it is sound pressure
-- times particle velocity (`I = p·u`), the length cancelling.
example : soundIntensity.dim = soundPressure.dim * particleVelocity.dim :=
  soundIntensity_dim_from_pressure_velocity

-- VERIFIED CONSTRUCTION (item 8-10): a sound intensity built as pressure × velocity
-- carries its product certificate by construction, over `ℝ`.
example (p : Quantity soundPressure.kind ℝ) (u : Quantity particleVelocity.kind ℝ) :
    (soundIntensityOf p u).IsProduct soundIntensity_prod_pressure_velocity p u :=
  soundIntensityOf_isProduct p u

-- the intensity product instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `3 Pa · 4 m/s = 12 W/m²` (at `Int`).
def soundIntensityInt : Quantity soundIntensity.kind Int :=
  Quantity.mul soundIntensity_prod_pressure_velocity
    (⟨3⟩ : Quantity soundPressure.kind Int) (⟨4⟩ : Quantity particleVelocity.kind Int)
#guard soundIntensityInt.magnitude == 12

/-! ## (6) Catalogue coverage — all 18 items carry their source as data -/

#guard PropertyKindCalculus.Iso80000.Part8.catalogue.length == 18
#guard staticPressureCK.item == "8-2.1"
#guard soundEnergyDensityCK.item == "8-7"
#guard acousticImpedanceCK.item == "8-13"
#guard soundExposureLevelCK.item == "8-16"
#guard soundPowerCK.coherentUnit == "W"
#guard soundPressureLevelCK.coherentUnit == "dB"

end PropertyKindCalculus.Examples.Iso80000.Part8
