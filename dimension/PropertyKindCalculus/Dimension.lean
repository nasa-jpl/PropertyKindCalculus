/-
# Dimension — the forgetful functor `dim` into PhysLib's `Dimension`

Dybkær (2009), Chapter 19 (the *dimension* of a kind-of-quantity); VIM4 2CD 1.7
(quantity dimension: "expression of the dependence of a quantity on the base
quantities … as a product of powers").

This module realizes the layer that originally motivated PropertyKindCalculus: a
*kind* carries strictly more information than its *dimension*. PhysLib's
`Dimension` is a free commutative group on the SI base quantities (length, time,
mass, charge, temperature) with ℚ exponents, so it identifies **every**
dimension-one quantity. The `dim` map here forgets a kind down to that group —
it is a *forgetful functor* in the plain-engineering sense: it drops the kind's
identity and keeps only its product-of-powers signature. Its **non-injectivity
at dimension one** is the dimension-1 disambiguation capstone: distinct kinds
(volumetric vs gravimetric water content, relative permittivity, reflectivity)
that PhysLib's `Dimension`, and any dimension-only type system, structurally
cannot tell apart, yet which the kind layer keeps distinct.

This is the **only** library in the package that depends on PhysLib (hence
Mathlib); the core spine stays Mathlib-free. It lives in its own source tree
(`dimension/`) and builds with `lake build Dimension`.
-/
import Physlib.Units.Dimension
import PropertyKindCalculus

open Dimension

namespace PropertyKindCalculus

/-- A **dimensioned kind** (Dybkær Ch. 19): a {kind-of-property} together with
the physical `Dimension` of its quantities. Pairing the dimension *with* the
kind — rather than storing it on `KindOfProperty` — keeps the core spine
Mathlib-free and matches the open-world convention (an application declares a
dimensioned kind with a `def`, never by editing a central type). -/
structure DimensionedKind where
  /-- The underlying kind-of-property (the richer datum). -/
  kind : KindOfProperty
  /-- The physical dimension of the kind's quantities (PhysLib `Dimension`). -/
  dim : Dimension

namespace DimensionedKind

/-- The **forgetful functor** on objects: drop the kind identity, keep only the
dimension. Naming it as a standalone map is what lets the central fact — that it
is *not injective* — be stated and proved. -/
def toDimension (dk : DimensionedKind) : Dimension := dk.dim

@[simp] theorem toDimension_eq (dk : DimensionedKind) : dk.toDimension = dk.dim := rfl

/-! ## Forgetful-functor coherence

A forgetful functor preserves the monoidal (here, multiplicative) structure: the
dimension of a *product* of dimensioned kinds is the product of their
dimensions, and the dimension of the unit is the dimensionless `1`. The full
kind-product algebra — scale gating and Flater's `KMul` — is the next module
(`Interaction`); here only the **dimension-component** laws the functor must
satisfy are recorded, using a provisional product whose kind component merely
records the composition. -/

/-- Provisional product of dimensioned kinds (superseded by `Interaction`'s
`KMul`): the dimensions multiply (PhysLib `Dimension.mul`, i.e. exponents add)
and the kind identity records the composition. Only the dimension component is
load-bearing for the coherence laws below. -/
def times (a b : DimensionedKind) : DimensionedKind :=
  { kind := { id := a.kind.id ++ "·" ++ b.kind.id, scale := .ratio }
    dim := a.dim * b.dim }

/-- The dimensionless unit dimensioned kind (`dim = 1`). -/
def unitless : DimensionedKind :=
  { kind := { id := "1", scale := .ratio }, dim := 1 }

/-- **Coherence (multiplicativity).** `dim` carries products to products — it is
a homomorphism into the multiplicative `Dimension` group. -/
@[simp] theorem toDimension_times (a b : DimensionedKind) :
    (a.times b).toDimension = a.toDimension * b.toDimension := rfl

/-- **Coherence (unit).** `dim` carries the unit dimensioned kind to the
dimensionless `1`. -/
@[simp] theorem toDimension_unitless : unitless.toDimension = 1 := rfl

end DimensionedKind

/-! ## Named dimensions

A handful of dimensions expressed in PhysLib's generators, enough to state the
capstone and to exercise the dimensional algebra. -/

namespace Dim

/-- Dimensionless (dimension one). -/
def one : Dimension := 1
/-- Length, `L`. -/
def length : Dimension := L𝓭
/-- Mass, `M`. -/
def mass : Dimension := M𝓭
/-- Time, `T`. -/
def time : Dimension := T𝓭
/-- Area, `L²`. -/
def area : Dimension := L𝓭 * L𝓭
/-- Speed, `L·T⁻¹`. -/
def speed : Dimension := L𝓭 / T𝓭
/-- Thermodynamic temperature, `Θ` — the SI base quantity ISO 80000-5
*Thermodynamics* is built on. -/
def temperature : Dimension := Θ𝓭
/-- Electric charge, `C` (the coulomb). PhysLib's `Dimension` takes electric
*charge* as the electromagnetic base generator; the SI base quantity electric
current then appears as `charge · time⁻¹` (the ampere as coulomb per second), so
`charge` is the generator IEC 80000-6 *Electromagnetism* is built on. -/
def charge : Dimension := C𝓭
/-- Electric current, `C·T⁻¹` (the ampere, coulomb per second). IEC 80000-6 takes
electric current as the SI base quantity; PhysLib takes charge as the generator, so
the two presentations of the electromagnetic dimension group are isomorphic. -/
def current : Dimension := C𝓭 / T𝓭

/-- Force, `M·L·T⁻²` (Newton's second law) — the mechanical dimension that energy and
torque are both built from (`force · length`). Named here so the dimension/interaction
layers and the scale-spanning reductions share one definition. -/
def force : Dimension := M𝓭 * L𝓭 / T𝓭 / T𝓭
/-- Energy and work, `M·L²·T⁻²` — force along a displacement. This is the mechanical
dimension the Finkelstein–Whitehead *scale-spanning* analysis (Eur. J. Phys. 46 (2025)
035701) assigns to the **kelvin** — thermodynamic temperature read as energy per
Boltzmann constant `k_B`. ISO 80000-7 *Light and radiation* uses it for radiant energy
(item 7-2.1). -/
def energy : Dimension := force * length
/-- Power, `M·L²·T⁻³` (energy per time). This is the mechanical dimension the
Finkelstein–Whitehead *scale-spanning* analysis assigns to the **candela** — luminous
intensity read as radiant power weighted by the luminous-efficacy coefficient `K_cd`
(see `ScaleSpanning`). ISO 80000-7 uses it for radiant flux (item 7-4.1). -/
def power : Dimension := energy / time
/-- **Luminous intensity, the candela — reduced to power `M·L²·T⁻³`.** PhysLib's
`Dimension` has no luminous-intensity generator, and — following the
Finkelstein–Whitehead *scale-spanning* analysis (and the spectral luminous efficiency
`V(λ)` being dimensionless) — none is needed: the candela is the dimension of *power*,
the radiant intensity it weights. The luminous quantities of ISO 80000-7 therefore
share the dimensions of their radiometric partners; what keeps them apart is the
{kind}, not the dimension. -/
def luminousIntensity : Dimension := power
/-- **Amount of substance, the mole — reduced to dimension one.** Following the
Finkelstein–Whitehead *scale-spanning* analysis, the mole is a (human-selected)
dimensionless count of entities (`N_A` particles), so a quantity *per mole* drops the
mole entirely. ISO 80000-7's molar absorption coefficient (item 7-37, `m²/mol`) is
therefore an area, `L²`. -/
def amountOfSubstance : Dimension := one

/-- The dimensional algebra composes in the PhysLib group: speed is length over
time. -/
theorem speed_eq : speed = length / time := rfl

/-- Area is length squared, carrying the expected length-exponent `2` — a
checked computation in the `Dimension` group, not an annotation. -/
theorem area_length : area.length = 2 := by
  norm_num [area, Dimension.length_mul, Dimension.L𝓭_length]

/-- Temperature carries temperature-exponent `1` — the base generator `Θ`. -/
theorem temperature_temperature : temperature.temperature = 1 := rfl

/-- Charge carries charge-exponent `1` — the base generator `C`. -/
theorem charge_charge : charge.charge = 1 := rfl

/-- Electric current is charge over time — the ampere as coulomb per second. -/
theorem current_eq : current = charge / time := rfl

/-- Power is energy over time — `M·L²·T⁻³`. -/
theorem power_eq : power = energy / time := rfl

/-- **The candela reduces to power.** Luminous intensity carries the dimension of
power; the spectral luminous efficiency that relates them is dimensionless. -/
theorem luminousIntensity_eq_power : luminousIntensity = power := rfl

/-- **The mole reduces to dimension one.** Amount of substance is a dimensionless
count. -/
theorem amountOfSubstance_eq_one : amountOfSubstance = 1 := rfl

/-- Energy carries mass-exponent `1` — `M·L²·T⁻²`. -/
theorem energy_mass : energy.mass = 1 := by
  norm_num [energy, force, length, Dimension.div_mass, Dimension.mass_mul,
    Dimension.M𝓭, Dimension.L𝓭_mass, Dimension.T𝓭_mass]

/-- Energy carries length-exponent `2` — `M·L²·T⁻²`. -/
theorem energy_length : energy.length = 2 := by
  norm_num [energy, force, length, Dimension.div_length, Dimension.length_mul,
    Dimension.M𝓭, Dimension.L𝓭_length, Dimension.T𝓭_length]

/-- Energy carries time-exponent `-2` — `M·L²·T⁻²`. -/
theorem energy_time : energy.time = -2 := by
  norm_num [energy, force, length, Dimension.div_time, Dimension.time_mul,
    Dimension.M𝓭, Dimension.L𝓭_time, Dimension.T𝓭_time]

/-- Power carries mass-exponent `1` — `M·L²·T⁻³`. -/
theorem power_mass : power.mass = 1 := by
  norm_num [power, energy, force, length, time, Dimension.div_mass, Dimension.mass_mul,
    Dimension.M𝓭, Dimension.L𝓭_mass, Dimension.T𝓭_mass]

/-- Power carries length-exponent `2` — `M·L²·T⁻³`. -/
theorem power_length : power.length = 2 := by
  norm_num [power, energy, force, length, time, Dimension.div_length, Dimension.length_mul,
    Dimension.M𝓭, Dimension.L𝓭_length, Dimension.T𝓭_length]

/-- Power carries time-exponent `-3` — `M·L²·T⁻³`. -/
theorem power_time : power.time = -3 := by
  norm_num [power, energy, force, length, time, Dimension.div_time, Dimension.time_mul,
    Dimension.M𝓭, Dimension.L𝓭_time, Dimension.T𝓭_time]

/-- **Power is mechanically reducible: it carries no charge.** The candela's dimension
involves only mass, length, and time — no electromagnetic generator. -/
theorem power_charge : power.charge = 0 := by
  norm_num [power, energy, force, length, time, Dimension.div_charge,
    Dimension.charge_mul, Dimension.M𝓭, Dimension.L𝓭_charge, Dimension.T𝓭_charge]

/-- **Power is mechanically reducible: it carries no temperature.** -/
theorem power_temperature : power.temperature = 0 := by
  norm_num [power, energy, force, length, time, Dimension.div_temperature,
    Dimension.temperature_mul, Dimension.M𝓭, Dimension.L𝓭_temperature,
    Dimension.T𝓭_temperature]

/-- **Energy is mechanically reducible: it carries no charge.** -/
theorem energy_charge : energy.charge = 0 := by
  norm_num [energy, force, length, Dimension.div_charge, Dimension.charge_mul,
    Dimension.M𝓭, Dimension.L𝓭_charge, Dimension.T𝓭_charge]

/-- **Energy is mechanically reducible: it carries no temperature.** -/
theorem energy_temperature : energy.temperature = 0 := by
  norm_num [energy, force, length, Dimension.div_temperature,
    Dimension.temperature_mul, Dimension.M𝓭, Dimension.L𝓭_temperature,
    Dimension.T𝓭_temperature]

/-- **Electric current carries charge-exponent `1`** — it is *not* mechanically
reducible: the ampere genuinely needs the electromagnetic generator, so it is a true
physical base unit, not a scale-spanning one. -/
theorem current_charge : current.charge = 1 := by
  norm_num [current, Dimension.div_charge, Dimension.C𝓭, Dimension.T𝓭_charge]

end Dim

/-! ## Example dimensioned kinds and the dimension-1 capstone

Each kind below is declared as an open-world `def`. The four dimensionless
soil-moisture / radiative kinds all forget to `dim = 1`, so PhysLib's
`Dimension` — and any dimension-only model — collapses them; their pairwise
distinctness as *kinds* is what the kind layer adds. -/

/-- Length, a dimensionful ratio kind. -/
def lengthKind : DimensionedKind :=
  { kind := { id := "length", scale := .ratio }, dim := Dim.length }

/-- Volumetric water content (water volume per soil volume, `m³/m³`): a *ratio*
kind, dimension one. -/
def vwc : DimensionedKind :=
  { kind := { id := "volumetric water content", scale := .ratio }, dim := 1 }

/-- Gravimetric water content (water mass per dry-soil mass, `kg/kg`): a *ratio*
kind, dimension one — the same dimension as `vwc`, a different kind. -/
def gwc : DimensionedKind :=
  { kind := { id := "gravimetric water content", scale := .ratio }, dim := 1 }

/-- Relative permittivity: a *ratio* kind, dimension one. -/
def permittivity : DimensionedKind :=
  { kind := { id := "relative permittivity", scale := .ratio }, dim := 1 }

/-- Reflectivity: a *ratio* kind, dimension one. -/
def reflectivity : DimensionedKind :=
  { kind := { id := "reflectivity", scale := .ratio }, dim := 1 }

/-- `vwc` and `gwc` are distinct kinds. -/
theorem vwc_ne_gwc : vwc.kind ≠ gwc.kind := by decide

/-- **The dimension-1 disambiguation — the motivating capstone.** `dim` is *not
injective*: there are distinct kinds with the same dimension, both equal to the
dimensionless `1`. Volumetric and gravimetric water content witness it. PhysLib's
`Dimension`, and any dimension-only type system, cannot separate them; the kind
layer does. -/
theorem dim_not_injective :
    ∃ a b : DimensionedKind,
      a.kind ≠ b.kind ∧ a.toDimension = b.toDimension ∧ a.toDimension = 1 :=
  ⟨vwc, gwc, vwc_ne_gwc, rfl, rfl⟩

end PropertyKindCalculus
