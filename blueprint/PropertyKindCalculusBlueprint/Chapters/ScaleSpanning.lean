import Verso
import VersoManual
import VersoBlueprint
-- The R13 nodes link real declarations (the unit-category classification, the
-- mechanical-reducibility criterion, the scale-spanning unit record, and the proofs
-- that the candela and mole reduce while the kelvin's reduction is invisible to the
-- dimension layer and the ampere is a genuine base), so this chapter imports the
-- `ScaleSpanning` module of the PhysLib-backed `Dimension` library.
import PropertyKindCalculus.ScaleSpanning

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Scale-spanning units — a third unit category (R13)" =>

The SI sorts its units into two categories — _base_ (the kilogram, metre, second,
ampere, kelvin, candela, mole) and _derived_ (everything built from them). Finkelstein
and Whitehead (_Eur. J. Phys._ *46* (2025) 035701) argue this two-way split is
_insufficient_. Of the seven base units, only four — the kilogram, metre, second, and
ampere — are genuinely _dimensionally independent_, each fixed by a natural constant
(`h`, `c`, `Δν_Cs`, `e`). The other three are _not_ dimensionally independent of those
four: the kelvin has the dimension of _energy_ (`M·L²·T⁻²`, via the Boltzmann constant
`k_B`); the candela has the dimension of _power_ (`M·L²·T⁻³`, via the luminous efficacy
`K_cd`); and the mole is a dimensionless _number_ (via the Avogadro constant `N_A`). Yet
each is kept as a distinct, coherent unit because it carries a _human-selected
coefficient_ — chosen for historical significance and a size that spans vast scales
without scientific notation (a temperature difference of 100 K, not `1.38 × 10⁻²¹ J` per
degree of freedom). The authors propose a third category for them: _scale-spanning
units_.

_R13_ specifies that third category. Its point is the unit-layer twin of _R1_ (a kind is
more than its dimension): _whether a unit is scale-spanning is not a function of its
dimension alone_. ISO 80000-7 (the _Light and radiation_ chapter) is where this lands on
the standard — the candela and the mole appear there, and are handled by reduction, not
by a new base generator.

# A criterion the dimension layer can apply — and one place it cannot

:::group "scale_spanning"
The dimension layer can detect _some_ scale-spanning units: a unit whose dimension is
_mechanically reducible_ — expressible in mass, length, and time alone — is by that fact
not dimensionally independent. The candela (power) and the mole (one) are reducible this
way. The kelvin is the sharp case: this work keeps thermodynamic temperature `Θ` as an
independent dimension (the _Thermodynamics_ chapter needs it), so the dimension layer
sees the kelvin as if it were a base — its scale-spanning character is visible only once
one adopts `k_B` as a defining coefficient, which the dimension layer does not. So
scale-spanning is carried, like a {uses "def_dim"}[kind's identity], _above_ the
dimension.
:::

:::definition "def_mechanically_reducible" (parent := "scale_spanning") (lean := "PropertyKindCalculus.Dimension.MechanicallyReducible")
A dimension is _mechanically reducible_ when it is expressible in mass, length, and time
alone — it carries no charge and no temperature exponent. This is the
Finkelstein–Whitehead test for "not dimensionally independent of the four physical base
units", specialized to the mechanical generators: such a unit needs no electromagnetic,
thermal, luminous, or chemical base of its own.
:::

:::proof "def_mechanically_reducible"
`Dimension.MechanicallyReducible d := d.charge = 0 ∧ d.temperature = 0`. Power and energy
are reducible (`power_mechanicallyReducible`, `energy_mechanicallyReducible`), as is
dimension one; electric current is _not_ (`current_not_mechanicallyReducible` — it carries
the electromagnetic generator), and neither is thermodynamic temperature in this work's
algebra (`temperature_not_mechanicallyReducible`).
:::

:::definition "def_unit_category" (parent := "scale_spanning") (lean := "PropertyKindCalculus.UnitCategory")
The proposed three-way classification of SI units: _physical base_ (the four
dimensionally independent units `kg, m, s, A`), _scale-spanning_ (the kelvin, candela,
and mole), and _derived_ (every plain product of powers, with no special coefficient).
The {uses "def_scale_spanning_unit"}[scale-spanning units] are the new middle category
the two-way base/derived split omits.
:::

:::proof "def_unit_category"
`inductive UnitCategory | physicalBase | scaleSpanning | derived`. Realized as a plain
enumeration; a scale-spanning unit's `category` is `scaleSpanning` by construction.
:::

:::definition "def_scale_spanning_unit" (parent := "scale_spanning") (lean := "PropertyKindCalculus.ScaleSpanningUnit")
A _scale-spanning unit_ pairs a {uses "def_metrologicalUnit"}[metrological unit] with its
mechanical-dimension reduction and the human-selected coefficient that defines it. The
worked set is the candela (reducing to power, via `K_cd = 683 lm/W`), the mole (to
dimension one, via `N_A`), and the kelvin (to energy, via `k_B`). The coefficient and its
value are _citation locators_ — the published constants — not reproduced normative text.
:::

:::proof "def_scale_spanning_unit"
`structure ScaleSpanningUnit` carries the `unit`, the `reducesTo` dimension, and the
`coefficient` symbol and value. The three canonical instances `candela`, `mole`, `kelvin`
are declared in the `ScaleSpanning` namespace (so their names do not collide with the
standards parts that also declare them).
:::

# The requirement, proved

:::theorem "thm_r13_candela" (parent := "scale_spanning") (lean := "PropertyKindCalculus.ScaleSpanning.candela_reduction_reducible") (tags := "proved") (effort := "small")
*The candela reduces to power — the dimension layer can see it.* Luminous intensity
carries the dimension of power, which is mechanically reducible; so the dimension layer
correctly detects that the candela is not dimensionally independent. The mole is likewise
reducible (to dimension one). Uses {uses "def_mechanically_reducible"}[mechanical
reducibility].
:::

:::proof "thm_r13_candela"
`candela_reduction_reducible : Dimension.MechanicallyReducible candela.reducesTo`, from
`power_mechanicallyReducible` (`power.charge = 0`, `power.temperature = 0`, checked in the
PhysLib dimension group). The companion `mole_reduction_reducible` covers dimension one.
Axiom-free.
:::

:::theorem "thm_r13_kelvin" (parent := "scale_spanning") (lean := "PropertyKindCalculus.ScaleSpanning.kelvin_reduction_invisible_to_dimension") (tags := "proved") (effort := "small")
*The kelvin's scale-spanning character is invisible to the dimension layer.* Its proposed
reduction (energy, via `k_B`) is mechanically reducible, yet the dimension this work
assigns thermodynamic temperature (`Θ`) is _not_ — so no dimensional analysis reveals the
kelvin to be scale-spanning. The fact is carried at the unit-classification layer, through
the coefficient `k_B`, exactly as a {uses "def_dim"}[kind] carries more than its
dimension. Uses {uses "def_mechanically_reducible"}[mechanical reducibility].
:::

:::proof "thm_r13_kelvin"
`kelvin_reduction_invisible_to_dimension : Dimension.MechanicallyReducible kelvin.reducesTo
∧ ¬ Dimension.MechanicallyReducible Dim.temperature`, the first conjunct from
`energy_mechanicallyReducible`, the second from `temperature_not_mechanicallyReducible`
(`Dim.temperature.temperature = 1 ≠ 0`). Axiom-free.
:::

:::theorem "thm_r13_ampere" (parent := "scale_spanning") (lean := "PropertyKindCalculus.ScaleSpanning.ampere_is_physicalBase") (tags := "proved") (effort := "small")
*The ampere is a genuine physical base — not scale-spanning.* Electric current is not
mechanically reducible: it carries the electromagnetic generator, so it is dimensionally
independent. This is the contrast that makes the third category non-empty _and_ distinct
from the first — the ampere (IEC 80000-6) belongs to the base set, the candela (ISO
80000-7) does not. Uses {uses "def_mechanically_reducible"}[mechanical reducibility].
:::

:::proof "thm_r13_ampere"
`ampere_is_physicalBase : ¬ Dimension.MechanicallyReducible Dim.current`, from
`Dim.current_charge = 1 ≠ 0`. Axiom-free.
:::

:::theorem "thm_r13_capstone" (parent := "scale_spanning") (lean := "PropertyKindCalculus.ScaleSpanning.scaleSpanning_not_determined_by_dimension") (tags := "capstone, proved") (effort := "small") (priority := "high")
*R13 — the base/derived dichotomy is insufficient; scale-spanning is a third category,
not a function of dimension.* Two scale-spanning units disagree on mechanical
reducibility — the candela's dimension (reducible) and the kelvin's actual dimension `Θ`
(not reducible) — so membership in the third category cannot be decided from the dimension.
The classification is a genuine extra datum, the unit-layer analogue of R1. Uses
{uses "def_unit_category"}[the unit categories] and
{uses "def_scale_spanning_unit"}[the scale-spanning units].
:::

:::proof "thm_r13_capstone"
`scaleSpanning_not_determined_by_dimension : ∃ a b : ScaleSpanningUnit,
Dimension.MechanicallyReducible a.reducesTo ∧ ¬ Dimension.MechanicallyReducible
Dim.temperature ∧ b.unit = kelvin.unit`, witnessed by `⟨candela, kelvin, …⟩`. Axiom-free.
This is the requirement ISO 80000-7's candela and mole, and ISO 80000-5's kelvin,
exercise on the standard.
:::
