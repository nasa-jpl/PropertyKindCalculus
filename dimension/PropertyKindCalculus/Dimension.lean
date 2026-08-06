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

## Provenance — what PKC uses, and what it contributed

The dimensional substrate this library sits on is not a fixed external given: the
**basis-parametric `Dimension B`** (and its unit twin) is this project's own contribution
to PhysLib, made because the layer PKC needs did not exist. PhysLib's `Dimension` was
hardwired to a single five-generator base; the parametrization was designed here, upstreamed
as PR #1447 (with the v4.32.0 toolchain bump #1445), merged, and is now consumed from
`leanprover-community/physlib` master — not from a fork. The same contribution line carries:

  * `Physlib.Units.Dimension` — the parametric `Dimension B` itself, with `extend`
    (change of basis by generator reindexing) and its exponent-faithfulness lemma;
  * `Physlib.Units.ParametricUnits` — `UnitScale B` and `UnitScale.dimScale`, the *unit*
    twin parametrized in the same basis (`PropertyKindCalculus.UnitConversion` exhibits the
    VIM4 §1.22 prefix factor as its single-generator instance);
  * `Physlib.Units.ISQDimensionBase` + `ISQBridge` — the seven-generator ISQ basis and the
    embedding/projection pair between it and `LTMCTDimensionBase`
    (`PropertyKindCalculus.IsqBase` consumes them).

The division of labour is deliberate and worth stating: what belongs upstream is the
*dimensional algebra* — bases, homs between bases, unit scaling; what stays here is the
*kind* layer above it, together with the catalogue's **stances** (the mole/candela
reduction, the SI plane-angle convention, the charge-vs-current citation choice). PhysLib
now offers the coordinates; PKC chooses among them and says why.
-/
import Physlib.Units.LTMCTDimensionBase
import PropertyKindCalculus

open Dimension

namespace PropertyKindCalculus

/-- A **dimensioned kind** (Dybkær Ch. 19): a {kind-of-property} together with
the physical `Dimension` of its quantities. Pairing the dimension *with* the
kind — rather than storing it on `KindOfProperty` — keeps the core spine
Mathlib-free and matches the open-world convention (an application declares a
dimensioned kind with a `def`, never by editing a central type).

It is **parametric in the base-dimension basis** `B`: `dim` is a PhysLib
`Dimension B`, so a dimensioned kind can be typed over any generating set — the
SI/PhysLib default (`LTMCTDimensionBase`), Gaussian–CGS, natural units, or an
angle-augmented basis. The basis parameter defaults to `LTMCTDimensionBase`, so a bare
`DimensionedKind` is the familiar five-generator instance and every existing
declaration reads unchanged; the parametricity is exercised where a different
basis is wanted (see `DimensionExamples`). Crucially the *kind* component does not
mention `B` at all: re-coordinatizing the dimension into another basis leaves the
kind fixed (`DimensionedKind.extend_kind`), the formal content of the base choice
living strictly *below* the kind layer. -/
structure DimensionedKind (B : Type := LTMCTDimensionBase) where
  /-- The underlying kind-of-property (the richer datum). -/
  kind : KindOfProperty
  /-- The physical dimension of the kind's quantities, over the base-dimension
  basis `B` (PhysLib `Dimension B`; `B` defaults to `LTMCTDimensionBase`). -/
  dim : Dimension B

namespace DimensionedKind

variable {B : Type}

/-- The **forgetful functor** on objects: drop the kind identity, keep only the
dimension. Naming it as a standalone map is what lets the central fact — that it
is *not injective* — be stated and proved. Generic in the basis `B`. -/
def toDimension (dk : DimensionedKind B) : Dimension B := dk.dim

@[simp] theorem toDimension_eq (dk : DimensionedKind B) : dk.toDimension = dk.dim := rfl

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
load-bearing for the coherence laws below. Generic in the basis `B`. -/
def times (a b : DimensionedKind B) : DimensionedKind B :=
  { kind := { id := a.kind.id ++ "·" ++ b.kind.id, scale := .ratio }
    dim := a.dim * b.dim }

/-- The dimensionless unit dimensioned kind (`dim = 1`), generic in the basis `B`
(inferred from the use site; `LTMCTDimensionBase` in the catalogue). -/
def unitless : DimensionedKind B :=
  { kind := { id := "1", scale := .ratio }, dim := 1 }

/-- **Coherence (multiplicativity).** `dim` carries products to products — it is
a homomorphism into the multiplicative `Dimension` group. -/
@[simp] theorem toDimension_times (a b : DimensionedKind B) :
    (a.times b).toDimension = a.toDimension * b.toDimension := rfl

/-- **Coherence (unit).** `dim` carries the unit dimensioned kind to the
dimensionless `1`. -/
@[simp] theorem toDimension_unitless : (unitless : DimensionedKind B).toDimension = 1 := rfl

/-! ## Change of basis and the invariance of kinds

The base-dimension basis `B` lives strictly *below* the kind layer. Re-coordinatizing
a dimensioned kind's dimension into another basis `B'` (via PhysLib's basis-change
map `Dimension.extend`) leaves the **kind** component untouched. This is the formal
content of "the base choice is invisible at the layer where kinds live": the same
kind, however its dimension is written. -/

/-- **Change of basis** on a dimensioned kind: re-express its dimension over an
extending basis `B'` along `f : B → B'`, leaving the kind identity fixed. -/
def extend {B' : Type} [Fintype B] [DecidableEq B'] (f : B → B')
    (dk : DimensionedKind B) : DimensionedKind B' :=
  { kind := dk.kind, dim := Dimension.extend f dk.dim }

/-- **Kinds are invariant under change of basis.** Re-coordinatizing the dimension
does not change the kind — the base choice is invisible at the kind layer. -/
@[simp] theorem extend_kind {B' : Type} [Fintype B] [DecidableEq B'] (f : B → B')
    (dk : DimensionedKind B) : (dk.extend f).kind = dk.kind := rfl

/-- Change of basis acts on the forgotten dimension exactly by `Dimension.extend`. -/
@[simp] theorem toDimension_extend {B' : Type} [Fintype B] [DecidableEq B'] (f : B → B')
    (dk : DimensionedKind B) :
    (dk.extend f).toDimension = Dimension.extend f dk.toDimension := rfl

/-- **Faithfulness of an embedding.** Along an *injective* change of basis, every
base-dimension exponent is preserved: the dimension re-expresses without loss, so no
distinction is created or destroyed by re-coordinatizing (only new zero exponents are
added for the fresh generators). -/
theorem extend_toDimension_exponent {B' : Type} [Fintype B] [DecidableEq B']
    {f : B → B'} (hf : Function.Injective f) (dk : DimensionedKind B) (b : B) :
    (dk.extend f).toDimension.exponent (f b) = dk.toDimension.exponent b := by
  show (Dimension.extend f dk.dim).exponent (f b) = dk.dim.exponent b
  exact Dimension.extend_exponent_apply hf dk.dim b

/-- **Re-dimension along an arbitrary map of dimensions, fixing the kind.** Unlike
`extend` — which reindexes generators along `f : B → B'`, and so can only send a
*generator to a generator* — this accepts any `φ : Dimension B → Dimension B'`, including a
genuine change of basis that sends a generator to a *product* of generators (PhysLib's
charge to the ISQ `current · time`; see `IsqBase`). The kind component is untouched, so
kinds stay invariant under change of basis however the dimension is re-expressed
(`mapDim_kind`) — the same invariance `extend` gives, now for a non-reindexing hom. -/
def mapDim {B' : Type} (φ : Dimension B → Dimension B') (dk : DimensionedKind B) :
    DimensionedKind B' :=
  { kind := dk.kind, dim := φ dk.dim }

/-- **Kinds are invariant under any re-dimensioning.** The base choice, and how the
dimension is re-expressed, is invisible at the kind layer. -/
@[simp] theorem mapDim_kind {B' : Type} (φ : Dimension B → Dimension B')
    (dk : DimensionedKind B) : (dk.mapDim φ).kind = dk.kind := rfl

/-- Re-dimensioning acts on the forgotten dimension exactly by `φ`. -/
@[simp] theorem toDimension_mapDim {B' : Type} (φ : Dimension B → Dimension B')
    (dk : DimensionedKind B) : (dk.mapDim φ).toDimension = φ dk.dim := rfl

end DimensionedKind

/-! ## The canonical basis `LTMCTDimensionBase`, and its two deliberate departures from ISQ

PKC fixes **`LTMCTDimensionBase`** — PhysLib's five generators length, time, mass, *charge*,
temperature — as the catalogue's canonical basis (the default of `DimensionedKind`). This
is deliberately *not* the seven-generator ISQ base of ISO 80000-1, and the two differences
are of different kinds:

* **Charge vs. current — a coordinate choice.** ISQ takes electric *current* `I` as base;
  PhysLib takes *charge* `C = I·T` (the ampere-second). These span the *same* group, so the
  choice is only a lossless, invertible change of coordinates. It is invisible to the kinds
  and to every distinctness theorem; it surfaces only in how a dimension is *printed*. For
  citation fidelity the catalogue's renderer re-expresses the electromagnetic axis in
  current (`Iso80000.renderDimension`), and `IsqBase` consumes the contributed bridge
  `Dimension.toISQHom : Dimension LTMCTDimensionBase →* Dimension ISQDimensionBase` sending
  `charge ↦ current · time` — a map a mere generator reindexing (`Dimension.extend`) cannot
  express, since a generator goes to a *product*. Upstream it comes paired with its
  projection and a retraction law, so the change of coordinates is invertible in the strong
  sense, not merely injective.

* **The mole and candela reduced — a modeling stance.** ISQ carries amount of substance and
  luminous intensity as independent base quantities. PKC does **not**: following the
  Finkelstein–Whitehead *scale-spanning* analysis (`ScaleSpanning`, R13) the mole is a
  human-selected dimensionless count (`Dim.amountOfSubstance = 1`) and the candela is the
  dimension of *power* (`Dim.luminousIntensity = Dim.power`). This is a *considered choice*,
  not a limitation forced by `LTMCTDimensionBase`: even over a basis that offers the two generators
  (`ISQDimensionBase`), the catalogue declines them — the mole stays dimension one and the
  candela stays power under the lift — and the distinctions the reduced dimension conflates
  (the `J/mol` energies, luminous vs. radiant flux) are carried by the **kind** layer, which
  is the whole point of this development.

So the base choice lives strictly *below* the kind layer; `IsqBase` witnesses that the
catalogue is base-agnostic (kinds invariant under the lift) while citing faithfully in the
ISQ base quantities.

## Named dimensions

A handful of dimensions expressed in PhysLib's generators, enough to state the
capstone and to exercise the dimensional algebra. -/

namespace Dim

/-- Dimensionless (dimension one). -/
def one : Dimension LTMCTDimensionBase := 1
/-- Length, `L`. -/
def length : Dimension LTMCTDimensionBase := L𝓭
/-- Mass, `M`. -/
def mass : Dimension LTMCTDimensionBase := M𝓭
/-- Time, `T`. -/
def time : Dimension LTMCTDimensionBase := T𝓭
/-- Area, `L²`. -/
def area : Dimension LTMCTDimensionBase := L𝓭 * L𝓭
/-- Speed, `L·T⁻¹`. -/
def speed : Dimension LTMCTDimensionBase := L𝓭 / T𝓭
/-- Thermodynamic temperature, `Θ` — the SI base quantity ISO 80000-5
*Thermodynamics* is built on. -/
def temperature : Dimension LTMCTDimensionBase := Θ𝓭
/-- Electric charge, `C` (the coulomb). PhysLib's `Dimension` takes electric
*charge* as the electromagnetic base generator; the SI base quantity electric
current then appears as `charge · time⁻¹` (the ampere as coulomb per second), so
`charge` is the generator IEC 80000-6 *Electromagnetism* is built on. -/
def charge : Dimension LTMCTDimensionBase := C𝓭
/-- Electric current, `C·T⁻¹` (the ampere, coulomb per second). IEC 80000-6 takes
electric current as the SI base quantity; PhysLib takes charge as the generator, so
the two presentations of the electromagnetic dimension group are isomorphic. -/
def current : Dimension LTMCTDimensionBase := C𝓭 / T𝓭

/-- Force, `M·L·T⁻²` (Newton's second law) — the mechanical dimension that energy and
torque are both built from (`force · length`). Named here so the dimension/interaction
layers and the scale-spanning reductions share one definition. -/
def force : Dimension LTMCTDimensionBase := M𝓭 * L𝓭 / T𝓭 / T𝓭
/-- Energy and work, `M·L²·T⁻²` — force along a displacement. This is the mechanical
dimension the Finkelstein–Whitehead *scale-spanning* analysis (Eur. J. Phys. 46 (2025)
035701) assigns to the **kelvin** — thermodynamic temperature read as energy per
Boltzmann constant `k_B`. ISO 80000-7 *Light and radiation* uses it for radiant energy
(item 7-2.1). -/
def energy : Dimension LTMCTDimensionBase := force * length
/-- Power, `M·L²·T⁻³` (energy per time). This is the mechanical dimension the
Finkelstein–Whitehead *scale-spanning* analysis assigns to the **candela** — luminous
intensity read as radiant power weighted by the luminous-efficacy coefficient `K_cd`
(see `ScaleSpanning`). ISO 80000-7 uses it for radiant flux (item 7-4.1). -/
def power : Dimension LTMCTDimensionBase := energy / time
/-- **Luminous intensity, the candela — reduced to power `M·L²·T⁻³`.** PhysLib's
`Dimension` has no luminous-intensity generator, and — following the
Finkelstein–Whitehead *scale-spanning* analysis (and the spectral luminous efficiency
`V(λ)` being dimensionless) — none is needed: the candela is the dimension of *power*,
the radiant intensity it weights. The luminous quantities of ISO 80000-7 therefore
share the dimensions of their radiometric partners; what keeps them apart is the
{kind}, not the dimension. -/
def luminousIntensity : Dimension LTMCTDimensionBase := power
/-- **Amount of substance, the mole — reduced to dimension one.** Following the
Finkelstein–Whitehead *scale-spanning* analysis, the mole is a (human-selected)
dimensionless count of entities (`N_A` particles), so a quantity *per mole* drops the
mole entirely. ISO 80000-7's molar absorption coefficient (item 7-37, `m²/mol`) is
therefore an area, `L²`. -/
def amountOfSubstance : Dimension LTMCTDimensionBase := one

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
