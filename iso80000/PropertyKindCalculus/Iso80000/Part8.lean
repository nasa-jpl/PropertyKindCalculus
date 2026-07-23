/-
# ISO 80000-8 — Acoustics (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
ISO 80000-8 *Acoustics* — all of items 8-1 … 8-17, including the sub-suffixed
pressure pair (8-2.1, 8-2.2) — each carrying its exact source as data: the part
(`iso80000_8`), the printed item designation, the principal quantity symbol, and the
coherent SI unit symbol. Only **citation locators** are recorded (item number, symbol,
coherent SI unit); no normative content (definitions, remarks) from the licensed
standard is reproduced. The defining *mathematics* of selected remarks is formalized in
the sibling module `Part8.DefiningRelations`.

Acoustics brings two themes the calculus is built for:

* **The logarithmic *levels* collapse to dimension one — the acoustics face of R1.**
  Sound pressure level, sound power level, and sound exposure level (8-14 … 8-16) are
  each `10·lg(quantity / reference)` — a ratio on a logarithmic scale, reported in the
  decibel. They are *dimension one*, three distinct {kinds} the {dimension functor}
  collapses to a single point, held apart by *which quantity each is the level of*. Their
  shared unit symbol `dB` no more makes one the other than the shared symbol `1` makes a
  Reynolds number a Froude number (ISO 80000-11).

* **A genuine dimension collision: sound pressure ≡ sound energy density.** Sound
  pressure (8-2.2, `Pa`) and sound energy density (8-7, `J/m³`) carry the *same*
  dimension `M·L⁻¹·T⁻²` — pressure being force per area, energy density energy per volume,
  and the two equal — yet are different kinds. The pascal and the joule-per-cubic-metre
  are not commensurable.

* **The counter-case: where the dimension *does* discriminate.** ISO 80000-8 lists two
  quantities both called an *impedance* — the characteristic impedance of a medium
  (8-12, `Pa·s/m`, `M·L⁻²·T⁻¹`) and the acoustic impedance (8-13, `Pa·s/m³`,
  `M·L⁻⁴·T⁻¹`). Here the dimension *does* tell the homonyms apart: one is pressure over
  particle velocity, the other pressure over volume flow rate, and the extra `L²` in the
  denominator shows in the dimension. Dimension is a *necessary* discriminator, never a
  *sufficient* one — the thesis of the whole catalogue, with its boundary made explicit.

* **The dimensional facts are checked computations**, discharged in PhysLib's dimension
  group over mass, length, and time.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.Iso80000.Catalogue

namespace PropertyKindCalculus.Iso80000.Part8

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_8

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Acoustic dimensions

The dimensions of acoustics, composed in PhysLib's `Dimension` group from mass `M`,
length `L`, and time `T`. -/

namespace ADim

/-- Volume, `L³`. -/
def volume : Dimension LTMCTDimensionBase := Dim.area * Dim.length
/-- Pressure, `M·L⁻¹·T⁻²` (force per area; the pascal). Static and sound pressure
share it; so — the collision — does the sound energy density (energy per volume). -/
def pressure : Dimension LTMCTDimensionBase := Dim.force / Dim.area
/-- Sound particle velocity, `L·T⁻¹` (the time-derivative of displacement). -/
def velocity : Dimension LTMCTDimensionBase := Dim.speed
/-- Sound particle acceleration, `L·T⁻²`. -/
def acceleration : Dimension LTMCTDimensionBase := Dim.speed / Dim.time
/-- Volume flow rate, `L³·T⁻¹` (volume per time). -/
def volumeFlowRate : Dimension LTMCTDimensionBase := volume / Dim.time
/-- Sound energy density, `M·L⁻¹·T⁻²` (energy per volume) — *equal* to `pressure`. -/
def energyDensity : Dimension LTMCTDimensionBase := Dim.energy / volume
/-- Sound intensity, `M·T⁻³` (power per area). -/
def intensity : Dimension LTMCTDimensionBase := Dim.power / Dim.area
/-- Sound exposure, `M²·L⁻²·T⁻³` (sound pressure squared, integrated over time —
`Pa²·s`). -/
def exposure : Dimension LTMCTDimensionBase := pressure * pressure * Dim.time
/-- Characteristic impedance of a medium, `M·L⁻²·T⁻¹` (pressure per particle velocity —
`Pa·s/m`). -/
def charImpedance : Dimension LTMCTDimensionBase := pressure / velocity
/-- Acoustic impedance, `M·L⁻⁴·T⁻¹` (pressure per volume flow rate — `Pa·s/m³`). The
extra `L²` over the characteristic impedance is what lets the dimension tell the two
homonymous "impedances" apart. -/
def acousticImpedance : Dimension LTMCTDimensionBase := pressure / volumeFlowRate

end ADim

/-! ## (A) The logarithmic frequency range (item 8-1)

The logarithmic frequency range (8-1, the octave/decade) is the base-2 (or base-10)
logarithm of a ratio of two frequencies — dimension one. -/

/-- Logarithmic frequency range — item 8-1, dimension one (`lb(f₂/f₁)` octaves). -/
def logFrequencyRange : DimensionedKind := dimKind "logarithmic frequency range" Dim.one

/-! ## (B) Pressure: static and sound (items 8-2.1, 8-2.2)

Static pressure (8-2.1) and sound pressure (8-2.2) are both the pascal, `M·L⁻¹·T⁻²` —
the same dimension, two kinds (the ambient mean versus the acoustic fluctuation). -/

/-- Static pressure — item 8-2.1, dimension `M·L⁻¹·T⁻²` (unit Pa). -/
def staticPressure : DimensionedKind := dimKind "static pressure" ADim.pressure
/-- Sound pressure — item 8-2.2, dimension `M·L⁻¹·T⁻²` (unit Pa). -/
def soundPressure : DimensionedKind := dimKind "sound pressure" ADim.pressure

/-! ## (C) The sound-particle kinematics chain (items 8-3 … 8-5)

Displacement (8-3), velocity (8-4, its time-derivative), and acceleration (8-5, the
next) — `L`, `L·T⁻¹`, `L·T⁻²`. -/

/-- Sound particle displacement — item 8-3, dimension `L` (unit m). -/
def particleDisplacement : DimensionedKind := dimKind "sound particle displacement" Dim.length
/-- Sound particle velocity — item 8-4, dimension `L·T⁻¹` (unit m/s). -/
def particleVelocity : DimensionedKind := dimKind "sound particle velocity" ADim.velocity
/-- Sound particle acceleration — item 8-5, dimension `L·T⁻²` (unit m/s²). -/
def particleAcceleration : DimensionedKind :=
  dimKind "sound particle acceleration" ADim.acceleration

/-! ## (D) Volume flow and the sound-energy cluster (items 8-6 … 8-11)

Volume flow rate (8-6, `m³/s`); the sound energy density (8-7, `J/m³`), sound energy
(8-8, `J`, its volume integral), sound power (8-9, `W`) and sound intensity (8-10,
`W/m²`); and sound exposure (8-11, `Pa²·s`). -/

/-- Volume velocity, volume flow rate — item 8-6, dimension `L³·T⁻¹` (unit m³/s). -/
def volumeFlowRate : DimensionedKind := dimKind "volume flow rate" ADim.volumeFlowRate
/-- Sound energy density — item 8-7, dimension `M·L⁻¹·T⁻²` (unit J/m³) — *the same*
dimension as sound pressure. -/
def soundEnergyDensity : DimensionedKind := dimKind "sound energy density" ADim.energyDensity
/-- Sound energy — item 8-8, dimension `M·L²·T⁻²` (unit J). -/
def soundEnergy : DimensionedKind := dimKind "sound energy" Dim.energy
/-- Sound power — item 8-9, dimension `M·L²·T⁻³` (unit W). -/
def soundPower : DimensionedKind := dimKind "sound power" Dim.power
/-- Sound intensity — item 8-10, dimension `M·T⁻³` (unit W/m²). -/
def soundIntensity : DimensionedKind := dimKind "sound intensity" ADim.intensity
/-- Sound exposure — item 8-11, dimension `M²·L⁻²·T⁻³` (unit Pa²·s). -/
def soundExposure : DimensionedKind := dimKind "sound exposure" ADim.exposure

/-! ## (E) The two impedances (items 8-12, 8-13)

Both are named an *impedance*, but they carry different dimensions: the characteristic
impedance (8-12, `Pa·s/m`, `M·L⁻²·T⁻¹`) is pressure per particle velocity; the acoustic
impedance (8-13, `Pa·s/m³`, `M·L⁻⁴·T⁻¹`) is pressure per volume flow rate. -/

/-- Characteristic impedance of a medium for longitudinal waves — item 8-12, dimension
`M·L⁻²·T⁻¹` (unit Pa·s/m). -/
def characteristicImpedance : DimensionedKind :=
  dimKind "characteristic impedance of a medium" ADim.charImpedance
/-- Acoustic impedance — item 8-13, dimension `M·L⁻⁴·T⁻¹` (unit Pa·s/m³). -/
def acousticImpedance : DimensionedKind := dimKind "acoustic impedance" ADim.acousticImpedance

/-! ## (F) The logarithmic levels (items 8-14 … 8-16)

Sound pressure level (8-14), sound power level (8-15), and sound exposure level (8-16)
are each `10·lg(quantity / reference)` — ratios on a logarithmic scale, *dimension one*,
reported in the decibel. Each is the level of a *different* base quantity, and that is
what keeps the three kinds apart. -/

/-- Sound pressure level — item 8-14, dimension one (unit dB). -/
def soundPressureLevel : DimensionedKind := dimKind "sound pressure level" Dim.one
/-- Sound power level — item 8-15, dimension one (unit dB). -/
def soundPowerLevel : DimensionedKind := dimKind "sound power level" Dim.one
/-- Sound exposure level — item 8-16, dimension one (unit dB). -/
def soundExposureLevel : DimensionedKind := dimKind "sound exposure level" Dim.one

/-! ## (G) Reverberation time (item 8-17) -/

/-- Reverberation time — item 8-17, dimension `T` (unit s). -/
def reverberationTime : DimensionedKind := dimKind "reverberation time" Dim.time

/-! ## The catalogue (every kind, with its source as data) -/

def logFrequencyRangeCK : CataloguedKind := cat "8-1" "G" "oct" logFrequencyRange
def staticPressureCK : CataloguedKind := cat "8-2.1" "p_s" "Pa" staticPressure
def soundPressureCK : CataloguedKind := cat "8-2.2" "p" "Pa" soundPressure
def particleDisplacementCK : CataloguedKind := cat "8-3" "δ" "m" particleDisplacement
def particleVelocityCK : CataloguedKind := cat "8-4" "u" "m/s" particleVelocity
def particleAccelerationCK : CataloguedKind := cat "8-5" "a" "m/s²" particleAcceleration
def volumeFlowRateCK : CataloguedKind := cat "8-6" "q_V" "m³/s" volumeFlowRate
def soundEnergyDensityCK : CataloguedKind := cat "8-7" "w" "J/m³" soundEnergyDensity
def soundEnergyCK : CataloguedKind := cat "8-8" "Q" "J" soundEnergy
def soundPowerCK : CataloguedKind := cat "8-9" "P" "W" soundPower
def soundIntensityCK : CataloguedKind := cat "8-10" "I" "W/m²" soundIntensity
def soundExposureCK : CataloguedKind := cat "8-11" "E" "Pa²·s" soundExposure
def characteristicImpedanceCK : CataloguedKind :=
  cat "8-12" "Z_c" "Pa·s/m" characteristicImpedance
def acousticImpedanceCK : CataloguedKind := cat "8-13" "Z_a" "Pa·s/m³" acousticImpedance
def soundPressureLevelCK : CataloguedKind := cat "8-14" "L_p" "dB" soundPressureLevel
def soundPowerLevelCK : CataloguedKind := cat "8-15" "L_W" "dB" soundPowerLevel
def soundExposureLevelCK : CataloguedKind := cat "8-16" "L_E" "dB" soundExposureLevel
def reverberationTimeCK : CataloguedKind := cat "8-17" "T" "s" reverberationTime

/-- The full ISO 80000-8 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [logFrequencyRangeCK, staticPressureCK, soundPressureCK,
   particleDisplacementCK, particleVelocityCK, particleAccelerationCK,
   volumeFlowRateCK, soundEnergyDensityCK, soundEnergyCK, soundPowerCK, soundIntensityCK,
   soundExposureCK, characteristicImpedanceCK, acousticImpedanceCK,
   soundPressureLevelCK, soundPowerLevelCK, soundExposureLevelCK, reverberationTimeCK]

/-! ## (H) Units — a few coherent SI units of these kinds

The pascal of sound pressure and the joule-per-cubic-metre of sound energy density carry
the *same* dimension `M·L⁻¹·T⁻²`, yet are not commensurable; and the decibel of sound
pressure level and the decibel of sound power level share the unit symbol `dB` and the
dimension one, yet are not commensurable either. -/

/-- The pascal of sound pressure (item 8-2.2). -/
def pascalSound : MetrologicalUnit := soundPressure.kind.unit "Pa"
/-- The joule-per-cubic-metre of sound energy density (item 8-7) — *also* `M·L⁻¹·T⁻²`. -/
def joulePerCubicMetre : MetrologicalUnit := soundEnergyDensity.kind.unit "J/m³"
/-- The decibel of sound pressure level (item 8-14). -/
def decibelPressure : MetrologicalUnit := soundPressureLevel.kind.unit "dB"
/-- The decibel of sound power level (item 8-15) — *also* the symbol `dB`, dimension
one. -/
def decibelPower : MetrologicalUnit := soundPowerLevel.kind.unit "dB"

/-! ## (I) Checked dimensional facts (the dimensional algebra) -/

/-- Sound pressure is `M·L⁻¹·T⁻²`: its mass-exponent is `1` (item 8-2.2). -/
theorem soundPressure_dim_mass : soundPressure.dim.mass = 1 := by
  norm_num [soundPressure, dimKind, ADim.pressure, Dim.force, Dim.area, Dim.length,
    Dimension.div_mass, Dimension.mass_mul, Dimension.M𝓭, Dimension.L𝓭_mass,
    Dimension.T𝓭_mass]

/-- Sound pressure is `M·L⁻¹·T⁻²`: its length-exponent is `-1` (item 8-2.2). -/
theorem soundPressure_dim_length : soundPressure.dim.length = -1 := by
  norm_num [soundPressure, dimKind, ADim.pressure, Dim.force, Dim.area, Dim.length,
    Dimension.div_length, Dimension.length_mul, Dimension.M𝓭, Dimension.L𝓭_length,
    Dimension.T𝓭_length]

/-- Sound intensity is `M·T⁻³`: its time-exponent is `-3` (item 8-10). -/
theorem soundIntensity_dim_time : soundIntensity.dim.time = -3 := by
  norm_num [soundIntensity, dimKind, ADim.intensity, Dim.power, Dim.energy, Dim.force,
    Dim.length, Dim.time, Dim.area, Dimension.div_time, Dimension.time_mul,
    Dimension.M𝓭, Dimension.L𝓭_time, Dimension.T𝓭_time]

/-- Sound power is `M·L²·T⁻³` (item 8-9). -/
theorem soundPower_dim_mass : soundPower.dim.mass = 1 := Dim.power_mass

/-- Reverberation time is `T` — the time generator (item 8-17). -/
theorem reverberationTime_dim_time : reverberationTime.dim.time = 1 := rfl

/-! ## (J) Unit well-formedness and (in)commensurability -/

/-- The pascal of sound pressure is a well-formed unit. -/
theorem pascalSound_wellFormed : pascalSound.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- The decibel of sound pressure level is a well-formed unit. -/
theorem decibelPressure_wellFormed : decibelPressure.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- **The pascal of sound pressure and the joule-per-cubic-metre of sound energy density
are not commensurable, though both are `M·L⁻¹·T⁻²`.** Pressure is force per area, energy
density energy per volume, and the two dimensions coincide — yet they are different
kinds, and the unit layer keeps them apart. -/
theorem pascalSound_joulePerCubicMetre_not_commensurable :
    ¬ pascalSound.Commensurable joulePerCubicMetre := by
  unfold MetrologicalUnit.Commensurable pascalSound joulePerCubicMetre soundPressure
    soundEnergyDensity dimKind KindOfProperty.unit
  decide

/-- **The decibel of sound pressure level and the decibel of sound power level are not
commensurable, though both have unit symbol `dB` and dimension one.** Same symbol, same
dimension, different kind — the level of pressure is not the level of power. This is the
ISO 80000-11 `"1"` pattern (Reynolds versus Euler) on the acoustic levels. -/
theorem decibelPressure_decibelPower_not_commensurable :
    ¬ decibelPressure.Commensurable decibelPower := by
  unfold MetrologicalUnit.Commensurable decibelPressure decibelPower soundPressureLevel
    soundPowerLevel dimKind KindOfProperty.unit
  decide

/-! ## (K) Dimension collisions — and the boundary where the dimension *does* classify

ISO 80000-8 shows both sides of the thesis. Sound pressure and sound energy density
collide on `M·L⁻¹·T⁻²`; the three logarithmic levels collide on dimension one. But the
two homonymous *impedances* are told apart *by* their dimension — the boundary case where
the necessary discriminator is, this time, also sufficient. -/

/-- Static pressure and sound pressure share dimension `M·L⁻¹·T⁻²`. -/
theorem staticPressure_dim_eq_soundPressure_dim :
    staticPressure.dim = soundPressure.dim := rfl

/-- **Sound pressure and sound energy density share dimension `M·L⁻¹·T⁻²`** — force per
area equals energy per volume. -/
theorem soundPressure_dim_eq_energyDensity_dim :
    soundPressure.dim = soundEnergyDensity.dim := by
  show ADim.pressure = ADim.energyDensity
  rw [ADim.pressure, ADim.energyDensity, ADim.volume, Dim.energy, Dim.force, Dim.area,
    Dim.length]
  ext b
  simp only [Dimension.div_exponent, Dimension.mul_exponent]
  ring

/-- Static pressure is not sound pressure, though both are `M·L⁻¹·T⁻²`. -/
theorem staticPressure_ne_soundPressure : staticPressure.kind ≠ soundPressure.kind := by
  unfold staticPressure soundPressure dimKind; decide

/-- Sound pressure is not sound energy density, though both are `M·L⁻¹·T⁻²`. -/
theorem soundPressure_ne_soundEnergyDensity :
    soundPressure.kind ≠ soundEnergyDensity.kind := by
  unfold soundPressure soundEnergyDensity dimKind; decide

/-- Sound pressure level is not sound power level, though both are dimension one. -/
theorem soundPressureLevel_ne_soundPowerLevel :
    soundPressureLevel.kind ≠ soundPowerLevel.kind := by
  unfold soundPressureLevel soundPowerLevel dimKind; decide

/-- **The dimension collision capstone, on the standard.** There exist distinct
ISO 80000-8 kinds with the same dimension — sound pressure and sound energy density
witness it (`M·L⁻¹·T⁻²`), as do the three logarithmic levels at dimension one. The
{dimension functor} cannot separate them; the kind layer — and the unit, `Pa` versus
`J/m³` — does. -/
theorem iso80000_8_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨soundPressure, soundEnergyDensity, soundPressure_ne_soundEnergyDensity,
    soundPressure_dim_eq_energyDensity_dim⟩

/-- **The dimension-one disambiguation, on the standard.** There exist distinct
ISO 80000-8 kinds with the same dimension one — the sound pressure level and the sound
power level witness it, alongside the sound exposure level and the logarithmic frequency
range. The logarithmic levels are the acoustic face of R1. -/
theorem iso80000_8_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨soundPressureLevel, soundPowerLevel, soundPressureLevel_ne_soundPowerLevel, rfl, rfl⟩

end PropertyKindCalculus.Iso80000.Part8
