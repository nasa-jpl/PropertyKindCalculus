/-
# Scale-spanning units — a third unit category beyond base and derived (requirement R13)

Finkelstein & Whitehead, *Proposed revision of SI unit classifications: how the
candela, mole, kelvin differ conceptually from the base units of kilogram, meter,
second, ampere*, Eur. J. Phys. **46** (2025) 035701.

The SI sorts its units into two categories: **base** (kg, m, s, A, K, cd, mol) and
**derived** (everything built from them). Finkelstein and Whitehead argue this
dichotomy is *insufficient*. Of the seven base units, only four — the kilogram,
metre, second, and ampere — are genuinely **dimensionally independent** (each fixed
by a natural constant: `h`, `c`, `Δν_Cs`, `e`). The other three are *not*
dimensionally independent of those four:

  * the **kelvin** has the dimension of *energy* (`M·L²·T⁻²`), via the Boltzmann
    constant `k_B`;
  * the **candela** has the dimension of *power* (`M·L²·T⁻³`), via the luminous
    efficacy `K_cd`;
  * the **mole** is a dimensionless *number*, via the Avogadro constant `N_A`.

Yet each is retained as a distinct, coherent unit because it carries a
**human-selected coefficient** (`k_B`, `K_cd`, `N_A`) — chosen for historical
significance and for a *size that spans vast scales* without scientific notation (a
temperature difference of 100 K rather than `1.38 × 10⁻²¹ J` per degree of freedom).
The authors propose a third category for them: **scale-spanning units**.

This module specifies that third category as a first-class classification — **R13**.
The thesis it makes provable is the unit-layer analogue of R1 (*a kind is more than
its dimension*):

> **Whether a unit is scale-spanning is not a function of its dimension alone.**

Two of the three scale-spanning units (the candela and the mole) *are* dimensionally
reducible to mechanics, and the dimension layer can detect that (`power_charge`,
`amountOfSubstance_eq_one`). The third — the kelvin — is *not* reducible in the
conventional dimension algebra this library uses (PhysLib keeps temperature `Θ` as an
independent generator, as ISO 80000-5 *Thermodynamics* needs): its scale-spanning
character is visible only once one adopts `k_B` as a defining coefficient, which the
dimension layer does not. So "scale-spanning" cannot be read off the dimension; it is
carried, like a kind, one layer up — exactly the point of the calculus.

The contrast unit is the **ampere** (ISO/IEC 80000-6): it carries the electromagnetic
generator (`current_charge = 1`), so it is genuinely dimensionally independent — a
true physical base unit, *not* scale-spanning.

No normative content is reproduced; only the paper's classification and the published
coefficient values (citation locators) are recorded.
-/

import PropertyKindCalculus.Dimension

namespace PropertyKindCalculus

/-! ## Dimensional reducibility -/

/-- A dimension is **mechanically reducible** iff it is expressible in mass, length,
and time alone — i.e. it carries no charge and no temperature exponent. This is the
Finkelstein–Whitehead criterion for "*not* dimensionally independent of the four
physical base units `{kg, m, s, A}`" specialized to the mechanical generators: a unit
whose dimension is mechanically reducible needs neither an electromagnetic, a
thermal, a luminous, nor a chemical base of its own. -/
def Dimension.MechanicallyReducible (d : Dimension PhyslibBase) : Prop :=
  d.charge = 0 ∧ d.temperature = 0

/-- Power is mechanically reducible — the candela's reduction. -/
theorem power_mechanicallyReducible : Dimension.MechanicallyReducible Dim.power :=
  ⟨Dim.power_charge, Dim.power_temperature⟩

/-- Energy is mechanically reducible — the kelvin's *proposed* reduction (via `k_B`). -/
theorem energy_mechanicallyReducible : Dimension.MechanicallyReducible Dim.energy :=
  ⟨Dim.energy_charge, Dim.energy_temperature⟩

/-- Dimension one is mechanically reducible — the mole's reduction. -/
theorem one_mechanicallyReducible : Dimension.MechanicallyReducible (1 : Dimension PhyslibBase) :=
  ⟨Dimension.one_charge, Dimension.one_temperature⟩

/-- **Electric current is *not* mechanically reducible.** The ampere carries the
electromagnetic generator, so it is a genuine physical base — the contrast with the
scale-spanning candela. -/
theorem current_not_mechanicallyReducible :
    ¬ Dimension.MechanicallyReducible Dim.current := by
  intro h
  have : (1 : ℚ) = 0 := Dim.current_charge ▸ h.1
  exact one_ne_zero this

/-- **Thermodynamic temperature is *not* mechanically reducible in the conventional
dimension algebra.** PhysLib keeps `Θ` as an independent generator (as ISO 80000-5
needs), so the dimension layer sees the kelvin as if it were a base unit — it *cannot*
detect that the kelvin is scale-spanning. That detection requires adopting `k_B`, a
human-selected coefficient the dimension layer does not carry. This is the sharp form
of R13: scale-spanning is not a function of dimension. -/
theorem temperature_not_mechanicallyReducible :
    ¬ Dimension.MechanicallyReducible Dim.temperature := by
  intro h
  have : (1 : ℚ) = 0 := Dim.temperature_temperature ▸ h.2
  exact one_ne_zero this

/-! ## The three unit categories (Finkelstein–Whitehead, Figure 1) -/

/-- The proposed three-way classification of SI units. The base/derived dichotomy is
*insufficient*; a third category is needed. -/
inductive UnitCategory
  /-- The four dimensionally independent physical base units `{kg, m, s, A}`, each
  fixed by a natural constant (`h`, `c`, `Δν_Cs`, `e`). -/
  | physicalBase
  /-- The kelvin, candela, and mole: *not* dimensionally independent, yet retained as
  distinct coherent units because each carries a human-selected coefficient that lets
  it span vast scales. -/
  | scaleSpanning
  /-- Every other unit (the newton, joule, watt, volt, ohm, …): a plain product of
  powers of the base units, with no special defining coefficient. -/
  | derived
deriving DecidableEq, Repr, BEq

/-! ## Scale-spanning units as data

Each scale-spanning unit pairs the unit with its mechanical-dimension reduction and
the human-selected coefficient that defines it. The coefficient and its value are
*citation locators* (the published constant), not reproduced normative text. -/

/-- A **scale-spanning unit**: a metrological unit that is dimensionally dependent on
the physical base, yet retained for its scale-spanning role, defined through a
human-selected coefficient. -/
structure ScaleSpanningUnit where
  /-- The metrological unit (e.g. the candela of luminous intensity). -/
  unit : MetrologicalUnit
  /-- The mechanical dimension the unit reduces to (power, energy, one). -/
  reducesTo : Dimension PhyslibBase
  /-- The human-selected defining coefficient (e.g. `K_cd`, `k_B`, `N_A`). -/
  coefficient : String
  /-- The coefficient's published value, a citation locator (e.g. `683 lm/W`). -/
  coefficientValue : String

namespace ScaleSpanningUnit

/-- The category of any scale-spanning unit is, by construction, `scaleSpanning`. -/
def category (_ : ScaleSpanningUnit) : UnitCategory := .scaleSpanning

end ScaleSpanningUnit

/-! ## The canonical SI units (the paper's worked set)

These live in the `ScaleSpanning` namespace so the canonical unit names (`candela`,
`kelvin`, `mole`, `ampere`) do not collide with the standards parts that also declare
them (ISO 80000-7's candela, ISO 80000-5's kelvin, IEC 80000-6's ampere). -/

namespace ScaleSpanning

/-- The kind of luminous intensity (ISO 80000-7 item 7-14), at the candela's
mechanical reduction (power). -/
def luminousIntensityKind : KindOfProperty :=
  { id := "luminous intensity", scale := .ratio }
/-- The kind of amount of substance (the mole's quantity), dimension one. -/
def amountOfSubstanceKind : KindOfProperty :=
  { id := "amount of substance", scale := .ratio }
/-- The kind of thermodynamic temperature (ISO 80000-5), the kelvin's quantity. -/
def thermodynamicTemperatureKind : KindOfProperty :=
  { id := "thermodynamic temperature", scale := .ratio }
/-- The kind of electric current (ISO/IEC 80000-6 item 6-1), the ampere's quantity —
the genuine physical base, for contrast. -/
def electricCurrentKind : KindOfProperty :=
  { id := "electric current", scale := .ratio }

/-- **The candela** — luminous intensity, a scale-spanning unit reduced to power
`M·L²·T⁻³`, defined through the luminous efficacy `K_cd = 683 lm/W` (at 540 THz). -/
def candela : ScaleSpanningUnit :=
  { unit := luminousIntensityKind.unit "cd", reducesTo := Dim.power,
    coefficient := "K_cd", coefficientValue := "683 lm/W" }
/-- **The mole** — amount of substance, a scale-spanning unit reduced to dimension
one, defined through the Avogadro constant `N_A ≈ 6.02 × 10²³`. -/
def mole : ScaleSpanningUnit :=
  { unit := amountOfSubstanceKind.unit "mol", reducesTo := Dim.amountOfSubstance,
    coefficient := "N_A", coefficientValue := "6.02214076e23" }
/-- **The kelvin** — thermodynamic temperature, a scale-spanning unit whose *proposed*
reduction is energy `M·L²·T⁻²`, defined through the Boltzmann constant
`k_B ≈ 1.38 × 10⁻²³ J/K`. (This library's dimension algebra nonetheless keeps `Θ`
independent for ISO 80000-5; see `kelvin_reduction_invisible_to_dimension`.) -/
def kelvin : ScaleSpanningUnit :=
  { unit := thermodynamicTemperatureKind.unit "K", reducesTo := Dim.energy,
    coefficient := "k_B", coefficientValue := "1.380649e-23 J/K" }

/-- The ampere — a *physical base* unit (electric current), for contrast: it is not a
scale-spanning unit. -/
def ampere : MetrologicalUnit := electricCurrentKind.unit "A"

/-! ## R13 — the requirement, proved

The classification is sound, and — the headline — *not derivable from the dimension
layer alone*. -/

/-- The candela's reduction is mechanically reducible — the dimension layer *can*
detect that luminous intensity is dimensionally dependent on the physical base. -/
theorem candela_reduction_reducible :
    Dimension.MechanicallyReducible candela.reducesTo :=
  power_mechanicallyReducible

/-- The mole's reduction is mechanically reducible (dimension one). -/
theorem mole_reduction_reducible :
    Dimension.MechanicallyReducible mole.reducesTo :=
  one_mechanicallyReducible

/-- **The kelvin's scale-spanning character is invisible to the dimension layer.**
Its *proposed* reduction (energy, via `k_B`) is mechanically reducible, yet the
dimension this library actually assigns thermodynamic temperature (`Θ`) is *not* — so
no amount of dimensional analysis reveals the kelvin to be scale-spanning. The fact is
carried at the unit-classification layer, through the coefficient `k_B`, not at the
dimension layer. -/
theorem kelvin_reduction_invisible_to_dimension :
    Dimension.MechanicallyReducible kelvin.reducesTo
      ∧ ¬ Dimension.MechanicallyReducible Dim.temperature :=
  ⟨energy_mechanicallyReducible, temperature_not_mechanicallyReducible⟩

/-- **The ampere is genuinely a physical base — not scale-spanning.** Electric current
is not mechanically reducible: it carries the electromagnetic generator. This is the
contrast that makes the third category non-empty *and* distinct from the first. -/
theorem ampere_is_physicalBase :
    ¬ Dimension.MechanicallyReducible (Dim.current) :=
  current_not_mechanicallyReducible

/-- **R13 — the base/derived dichotomy is insufficient: scale-spanning is a third
category, not a function of dimension.** There exist two scale-spanning units whose
dimensions disagree on mechanical reducibility — the candela's (reducible) and the
kelvin's actual dimension `Θ` (not reducible) — so one cannot decide scale-spanning
membership from the dimension. The classification is a genuine extra datum, the
unit-layer analogue of R1 (a kind is more than its dimension). -/
theorem scaleSpanning_not_determined_by_dimension :
    ∃ a b : ScaleSpanningUnit,
      Dimension.MechanicallyReducible a.reducesTo
        ∧ ¬ Dimension.MechanicallyReducible Dim.temperature
        ∧ b.unit = kelvin.unit :=
  ⟨candela, kelvin, candela_reduction_reducible,
    temperature_not_mechanicallyReducible, rfl⟩

end ScaleSpanning

end PropertyKindCalculus
