import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Units and the Dimension-1 Problem" =>

This chapter states the layer that originally motivated PropertyKindCalculus, and is
_planned, not yet formalized_. Its nodes carry informal statements and proof
sketches; they appear as in-progress goals in the dependency graph until a
`(lean := …)` declaration or a checked code block is attached.

PhysLib's `Dimension` (a ℚ-exponent free commutative group over the SI base
quantities) makes every dimension-one quantity equal. Volumetric water content
($`\mathrm{L^3/L^3}`), gravimetric water content ($`\mathrm{M/M}`), relative
permittivity, reflectivity, and emissivity are all dimension one — so a
dimension-only type system cannot tell them apart. In soil-moisture retrieval
that is precisely the class of confusion that silently corrupts a result. The
kind layer is what restores the distinction.

# Quantities and units (VIM, Dybkær §13.3.3)

:::group "units"
Following the VIM principle that a unit is a chosen value of a kind of quantity,
and Dybkær §13.3.3 (a unitary kind value is "a reference quantity multiplied by a
number"), units are indexed by the kind they measure.
:::

:::definition "def_quantity" (parent := "units")
A _quantity_ `Quantity k` is a magnitude of a fixed kind $`k`. It is indexed by
$`k`, a {uses "def_kindOfProperty"}[kind-of-property], so the type system forbids
forming or comparing a `Quantity k₁` with a `Quantity k₂` when $`k_1 \neq k_2` —
even if both kinds are dimension one. This indexing _is_ the fix for the
dimension-1 conflation.
:::

:::proof "def_quantity"
Planned. A `structure Quantity (k : KindOfProperty)` carrying a numeric
magnitude, with arithmetic gated by `k.scale` (per the proved operator
stratification, {uses "thm_operator_monotonicity"}[operator monotonicity]).
:::

:::definition "def_unit" (parent := "units")
A _unit_ `Unit k` is a distinguished {uses "def_quantity"}[quantity] of kind $`k`
chosen as the reference: measuring expresses any quantity of kind $`k` as
$`\text{number} \times \text{unit}`. Because `Unit` is indexed by the same $`k`,
"a metre" and "a unit of gravimetric water content" inhabit different types.
:::

:::proof "def_unit"
Planned. A `Unit k := { ref : Quantity k }` (or a chosen nonzero reference), with
`measure : Quantity k → Unit k → ℝ` giving the numeric value in that unit.
:::

:::theorem "thm_unit_conversion_roundtrip" (parent := "units") (tags := "capstone, planned") (effort := "medium") (priority := "high")
*Unit conversion is a faithful round-trip.* For two units $`u_1, u_2` of the same
kind $`k`, converting a quantity from $`u_1` to $`u_2` and back is the identity:
$$`\mathrm{convert}_{u_2 \to u_1}\bigl(\mathrm{convert}_{u_1 \to u_2}(q)\bigr) = q.`
Conversion is multiplication by the ratio $`u_1 / u_2`, defined only within a
kind. There is no conversion between units of different kinds — that is a type
error, not a runtime check. Builds on {uses "def_unit"}[the unit definition].
:::

:::proof "thm_unit_conversion_roundtrip"
Planned. The conversion factor is $`r = \mathrm{measure}(u_1, u_2)` and its
inverse $`r^{-1}`; the round-trip is $`r^{-1}\cdot(r \cdot q) = q`, requiring
$`r \neq 0` from the chosen-reference nonzeroness. Ratio formation is licensed by
the ratio scale.
:::

:::theorem "thm_dimensionless_kinds_distinct" (parent := "units") (tags := "capstone, planned") (effort := "small") (priority := "high")
*The dimension-1 disambiguation (the motivating capstone).* There exist distinct
kinds that map to the same dimension. Concretely, for volumetric and gravimetric
water content,
$$`\mathrm{vwc} \neq \mathrm{gwc} \qquad\text{yet}\qquad \dim(\mathrm{vwc}) = \dim(\mathrm{gwc}) = \mathbf{1},`
and likewise for permittivity, reflectivity, and emissivity. So the kind layer is
a strict refinement of the dimension layer: $`\dim` is not injective. This is the
statement PhysLib — and any dimension-only model, whether OWL2 or a
representation-rooted hierarchy like SysML v2's — structurally cannot make. Uses
{uses "def_kindOfProperty"}[kind-of-property] and {uses "def_dim"}[the dimension map].
:::

:::proof "thm_dimensionless_kinds_distinct"
Planned. `vwc` and `gwc` are declared as distinct `KindOfProperty` values
(distinct `id`, distinct examination principle), so `vwc ≠ gwc` is `by decide`.
Both have `dim = 1` once the dimension map is in place, giving a witnessed
$`\exists k_1\ k_2,\ k_1 \neq k_2 \wedge \dim k_1 = \dim k_2`.
:::
