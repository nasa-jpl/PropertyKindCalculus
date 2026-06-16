import Verso
import VersoManual
import VersoBlueprint
-- The Part-8 nodes link real declarations (the acoustic dimensioned kinds, the
-- logarithmic-level dimension-one collapse, the sound-pressure/energy-density collision,
-- the impedance boundary case, and the defining-relation kind-laws), so this chapter
-- imports the Part-8 modules of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part8
import PropertyKindCalculus.Iso80000.Part8.DefiningRelations

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "ISO 80000-8 — Acoustics" =>

The sixth part specified in full is ISO 80000-8, _Acoustics_. Every item — all of
8-1 … 8-17, including the sub-suffixed pressure pair (8-2.1, 8-2.2) — is catalogued: the
logarithmic frequency range, static and sound pressure, the sound-particle kinematics
(displacement, velocity, acceleration), volume flow rate, the sound-energy cluster
(energy density, energy, power, intensity), sound exposure, the two impedances, the three
logarithmic levels, and the reverberation time — each carrying its exact source as data:
the part, the printed item designation, the principal quantity symbol, and the coherent
SI unit symbol. Only _citation locators_ are recorded; no normative content from the
licensed standard is reproduced. The defining _mathematics_ of selected remarks is
specified in the sibling module `Part8.DefiningRelations`.

Acoustics brings two faces of the catalogue's central thesis, and — unusually — its
boundary. The _logarithmic levels_ (sound pressure level, sound power level, sound
exposure level) are each `10·lg(quantity / reference)`, ratios on a logarithmic scale
reported in the decibel: _dimension one_, three distinct kinds the dimension functor
collapses to a single point. A genuine _dimension collision_ has sound pressure and sound
energy density carry the same dimension `M·L⁻¹·T⁻²` — force per area equals energy per
volume — while staying distinct kinds. And the _boundary_: the two homonymous
_impedances_ are told apart _by_ their dimension, the case where the necessary
discriminator is, this time, also sufficient.

# Quantity-kinds and units of ISO 80000-8

:::group "iso80000_part8"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, here over mass, length, and time. The standard's dimensional facts — a sound
pressure is `M·L⁻¹·T⁻²`, a sound intensity `M·T⁻³`, a reverberation time `T` — are
_checked computations_. Each unit is a {uses "def_metrologicalUnit"}[metrological unit] of
its kind; commensurability is a type-level fact, so the pascal of sound pressure and the
joule-per-cubic-metre of sound energy density are not interchangeable though they share
one dimension.
:::

:::definition "def_part8_catalogued_kind" (parent := "iso80000_part8") (lean := "PropertyKindCalculus.Iso80000.Part8.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "8-2.2"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with the
kind as data, so the source of each definition can be rendered or audited downstream.
:::

:::proof "def_part8_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `ISO 80000-8, Second edition, 2020-02 item 8-2.2`. The `catalogue` lists all 18
items in item order — the logarithmic frequency range (8-1), static and sound pressure
(8-2.1, 8-2.2), the kinematics (8-3 … 8-5), the sound-energy cluster (8-7 … 8-10), the
impedances (8-12, 8-13), the levels (8-14 … 8-16), … — each paired with its coherent SI
unit symbol.
:::

# The logarithmic levels — the acoustic face of dimension one

ISO 80000-8 lists three _levels_: the sound pressure level (8-14), the sound power level
(8-15), and the sound exposure level (8-16). Each is `10·lg(quantity / reference)` — a
ratio of a quantity to a stated reference, taken on a logarithmic scale, and reported in
the decibel. A level is _dimension one_: the logarithm of a ratio of like quantities. So
the dimension functor sends all three to the single point `1`, and a dimension-only model
sees one type, "a real number of decibels", for all of them.

What keeps them apart is _which quantity each is the level of_ — the pressure, the power,
the exposure. This is requirement _R1_ once more (the dimension does not classify the
kind), in the form the part makes vivid: a shared unit symbol `dB` no more makes the
sound pressure level the sound power level than the shared symbol `1` makes a Reynolds
number a Froude number (ISO 80000-11).

:::group "iso80000_part8_levels"
The three levels are distinct dimension-one {uses "def_quantity"}[quantity]-kinds. Their
decibel units share the symbol `dB` and the dimension one, yet are not
{uses "def_metrologicalUnit"}[commensurable] — the kind layer keeps the level of pressure
from being read as the level of power.
:::

:::theorem "thm_part8_levels" (parent := "iso80000_part8_levels") (lean := "PropertyKindCalculus.Iso80000.Part8.decibelPressure_decibelPower_not_commensurable") (tags := "proved") (effort := "small")
*The decibel of sound pressure level and the decibel of sound power level are not
commensurable, though both are `dB` and dimension one (items 8-14, 8-15).* Same symbol,
same dimension, different kind — the level of pressure is not the level of power. This is
the ISO 80000-11 `"1"` pattern (Reynolds versus Euler) on the acoustic levels. Uses
{uses "def_metrologicalUnit"}[the metrological unit].
:::

:::proof "thm_part8_levels"
`decibelPressure_decibelPower_not_commensurable`, by `decide` after unfolding
`MetrologicalUnit.Commensurable` on the two dimension-one kinds. The companion
`soundPressureLevel_ne_soundPowerLevel` is the underlying kind distinction, and
`iso80000_8_dim_one_collision` packages the dimension-one capstone. Axiom-free.
:::

:::theorem "thm_part8_dim_one" (parent := "iso80000_part8_levels") (lean := "PropertyKindCalculus.Iso80000.Part8.iso80000_8_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard.* There exist distinct ISO 80000-8 kinds
with the same dimension one — the sound pressure level and the sound power level witness
it, alongside the sound exposure level and the logarithmic frequency range. The dimension
cannot separate them; the kind layer does. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part8_dim_one"
`iso80000_8_dim_one_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
a.dim = 1`, witnessed by `⟨soundPressureLevel, soundPowerLevel, …⟩` with the kind
distinction a `decide` and reflexivity. Axiom-free.
:::

# A dimension collision, and the boundary where the dimension *does* classify

ISO 80000-8 shows both sides of the thesis. Sound pressure (8-2.2, `Pa`) and sound energy
density (8-7, `J/m³`) carry the _same_ dimension `M·L⁻¹·T⁻²` — pressure being force per
area, energy density energy per volume, and the two equal — yet are different kinds: a
collision the dimension cannot resolve.

But the part also marks the _boundary_. It lists two quantities both called an
_impedance_: the characteristic impedance of a medium (8-12, `Pa·s/m`, `M·L⁻²·T⁻¹`) and
the acoustic impedance (8-13, `Pa·s/m³`, `M·L⁻⁴·T⁻¹`). Here the dimension _does_ tell the
homonyms apart, because one is pressure over particle velocity and the other pressure
over volume flow rate — the extra `L²` shows. Dimension is a _necessary_ discriminator of
kind, never a _sufficient_ one; the impedances are the case where, this once, it is also
sufficient, and naming them makes the limit of the dimension test explicit.

:::group "iso80000_part8_collision"
The dimension-collision capstone, on _standard_ quantities: the {uses "def_dim"}[dimension
map] identifies sound pressure with sound energy density, while the kind layer keeps them
apart, both as kinds and as {uses "def_metrologicalUnit"}[units]. The impedances are the
contrasting boundary case.
:::

:::theorem "thm_part8_collision" (parent := "iso80000_part8_collision") (lean := "PropertyKindCalculus.Iso80000.Part8.iso80000_8_dim_collision") (tags := "proved") (effort := "small")
*Sound pressure is not sound energy density, though both are `M·L⁻¹·T⁻²` (items 8-2.2,
8-7).* There exist distinct ISO 80000-8 kinds with the same dimension — sound pressure and
sound energy density witness it. Force per area equals energy per volume, so no
dimension-only type system can separate them; the kind layer — and the unit, `Pa` versus
`J/m³` — does. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part8_collision"
`iso80000_8_dim_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim`,
witnessed by `⟨soundPressure, soundEnergyDensity, …⟩`. The dimension equality
`soundPressure_dim_eq_energyDensity_dim` is a `Dimension.ext` computation (force/area =
energy/volume); `pascalSound_joulePerCubicMetre_not_commensurable` records the unit-level
fact. The contrasting `acousticImpedance_dim_from_pressure_volumeFlow` shows where the
dimension instead discriminates. Axiom-free.
:::

# The algebraic Remarks as kind-laws: linear acoustics built by the kind algebra

Several Part-8 definitions state a quantity's defining relation _algebraically_ — the
constitutive laws of linear acoustics. Sound particle velocity is the time-derivative of
displacement (8-4), acceleration of velocity (8-5); sound intensity is the _product_ of
sound pressure and particle velocity (8-10, `I = p·u`); the two impedances are quotients
of sound pressure (8-12, 8-13). Each is specified as an R12 kind-law, the kinematics
crossing to ISO 80000-3 for time.

:::group "iso80000_part8_relations"
The {uses "def_quotient_kind"}[quotient] and product families carry the kind-laws. Two
payoffs on the standard's own definitions: linear acoustics is built from one another, and
the _dimension follows from the relation_ as a checked computation (sound intensity is
`M·T⁻³` because pressure times velocity cancels the length).
:::

:::theorem "thm_part8_intensity" (parent := "iso80000_part8_relations") (lean := "PropertyKindCalculus.Iso80000.Part8.DefiningRelations.soundIntensityOf_isProduct") (tags := "proved") (effort := "small")
*Sound intensity is sound pressure × particle velocity — a verified construction (item
8-10).* A sound intensity built as the product of a sound pressure and a particle velocity
carries its product certificate by construction, over the `ℝ` carrier. The companion
`soundIntensity_dim_from_pressure_velocity` shows the intensity is `M·T⁻³` _because_ the
length in pressure and velocity cancels — the acoustic intensity law as a checked
computation. Uses {uses "def_quotient_kind"}[the quotient kind-law].
:::

:::proof "thm_part8_intensity"
`soundIntensityOf p u := Quantity.mul soundIntensity_prod_pressure_velocity p u`, and
`soundIntensityOf_isProduct` is `rfl`. The same family gives the quotient constructors
`characteristicImpedanceOf` (= `p/u`) and the cross-part kinematic laws
`particleVelocity_quot_displacement_duration` (= displacement / time), the time crossing
to ISO 80000-3.
:::

# Item index — ISO 80000-8

Every catalogued item of ISO 80000-8, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it. Each item number links to the formalized result it participates in — a
dimension collision, a dimension-one level, a defining relation, or the catalogue itself.
Symbols and unit strings are _citation locators_; nothing normative is reproduced.

:::table +header (align := left)
*
  * Item
  * Quantity
  * Symbol
  * Unit
  * Dimension
*
  * {bpref "thm_part8_dim_one"}[8-1]
  * logarithmic frequency range
  * `G`
  * `oct`
  * `1`
*
  * {bpref "thm_part8_collision"}[8-2.1]
  * static pressure
  * `p_s`
  * `Pa`
  * `M·L⁻¹·T⁻²`
*
  * {bpref "thm_part8_collision"}[8-2.2]
  * sound pressure
  * `p`
  * `Pa`
  * `M·L⁻¹·T⁻²`
*
  * {bpref "thm_part8_intensity"}[8-3]
  * sound particle displacement
  * `δ`
  * `m`
  * `L`
*
  * {bpref "thm_part8_intensity"}[8-4]
  * sound particle velocity
  * `u`
  * `m/s`
  * `L·T⁻¹`
*
  * {bpref "thm_part8_intensity"}[8-5]
  * sound particle acceleration
  * `a`
  * `m/s²`
  * `L·T⁻²`
*
  * {bpref "thm_part8_intensity"}[8-6]
  * volume flow rate
  * `q_V`
  * `m³/s`
  * `L³·T⁻¹`
*
  * {bpref "thm_part8_collision"}[8-7]
  * sound energy density
  * `w`
  * `J/m³`
  * `M·L⁻¹·T⁻²`
*
  * {bpref "def_part8_catalogued_kind"}[8-8]
  * sound energy
  * `Q`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "def_part8_catalogued_kind"}[8-9]
  * sound power
  * `P`
  * `W`
  * `M·L²·T⁻³`
*
  * {bpref "thm_part8_intensity"}[8-10]
  * sound intensity
  * `I`
  * `W/m²`
  * `M·T⁻³`
*
  * {bpref "def_part8_catalogued_kind"}[8-11]
  * sound exposure
  * `E`
  * `Pa²·s`
  * `M²·L⁻²·T⁻³`
*
  * {bpref "thm_part8_intensity"}[8-12]
  * characteristic impedance of a medium
  * `Z_c`
  * `Pa·s/m`
  * `M·L⁻²·T⁻¹`
*
  * {bpref "thm_part8_intensity"}[8-13]
  * acoustic impedance
  * `Z_a`
  * `Pa·s/m³`
  * `M·L⁻⁴·T⁻¹`
*
  * {bpref "thm_part8_dim_one"}[8-14]
  * sound pressure level
  * `L_p`
  * `dB`
  * `1`
*
  * {bpref "thm_part8_dim_one"}[8-15]
  * sound power level
  * `L_W`
  * `dB`
  * `1`
*
  * {bpref "thm_part8_dim_one"}[8-16]
  * sound exposure level
  * `L_E`
  * `dB`
  * `1`
*
  * {bpref "def_part8_catalogued_kind"}[8-17]
  * reverberation time
  * `T`
  * `s`
  * `T`
:::
