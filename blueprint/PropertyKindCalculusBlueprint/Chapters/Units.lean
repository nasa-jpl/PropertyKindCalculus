import Verso
import VersoManual
import VersoBlueprint
-- The dimension-1 disambiguation capstone below now links a real declaration, so
-- this chapter imports the `Dimension` library (the one PhysLib + Mathlib
-- dependency); the rest of its nodes remain planned.
import PropertyKindCalculus.Dimension

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Units and the Dimension-1 Problem" =>

This chapter states the layer that originally motivated PropertyKindCalculus. Its
motivating capstone — the dimension-1 disambiguation — is now _proved_ (see the
_Dimension as a Forgetful Functor_ chapter for the forgetful map it rests on);
the unit-arithmetic nodes around it remain _planned_, carrying
informal statements and proof sketches that appear as in-progress goals in the
dependency graph until a `(lean := …)` declaration or checked code block is
attached.

PhysLib's `Dimension` (a ℚ-exponent free commutative group over the SI base
quantities) makes every dimension-one quantity equal. Volumetric water content
($`\mathrm{L^3/L^3}`), gravimetric water content ($`\mathrm{M/M}`), relative
permittivity, reflectivity, and emissivity are all dimension one — so a
dimension-only type system cannot tell them apart. In soil-moisture retrieval
that is precisely the class of confusion that silently corrupts a result. The
kind layer is what restores the distinction.

# Quantities and units (VIM4 2CD, Dybkær §13.3.3)

:::group "units"
Following the VIM4 2CD principle (measurement unit, 1.12: a "reference quantity
with which any other quantity of the same kind can be compared by ratio") and
Dybkær §13.3.3 (a unitary kind value is "a reference quantity multiplied by a
number"), units are indexed by the kind they measure.
:::

:::definition "def_carrier" (parent := "units") (lean := "PropertyKindCalculus.Carrier")
A _numeric carrier_ `Carrier R` is the minimal arithmetic a kind-indexed
magnitude needs, supplied once per representation type $`R` (a zero and an
addition; a `LawfulCarrier` adds the additive-monoid laws). In plain engineering
terms it is the _number type plug_: everything above it — kind discrimination,
scale gating, the dimension functor, the interaction algebra, extensivity — is
written against this class and so reused verbatim at every $`R`. This is the role
TorchLean's `Context α` typeclass plays for tensor element types; the kind index
is the layer _above_ the carrier that TorchLean does not have.
:::

:::proof "def_carrier"
Realized as the `Carrier` / `LawfulCarrier` classes. `Carrier R` bundles `zero`
and `add`; `LawfulCarrier R` extends it with associativity, commutativity, and the
unit laws. `Int` and (in the `Dimension` library) `ℝ` are lawful carriers; `Float`
is a `Carrier` but deliberately _not_ lawful (floating-point addition is not
associative).
:::

:::definition "def_quantity" (parent := "units") (lean := "PropertyKindCalculus.Quantity")
A _quantity_ `Quantity k R` is a magnitude of a fixed kind $`k`, carried at a
{uses "def_carrier"}[representation type] $`R` (R10). It is indexed by $`k`, a
{uses "def_kindOfProperty"}[kind-of-property], so the type system forbids forming
or comparing a `Quantity k₁ R` with a `Quantity k₂ R` when $`k_1 \neq k_2` — even
if both kinds are dimension one. This indexing _is_ the fix for the dimension-1
conflation. The second index $`R` is the numeric carrier: the same value type is
instantiated at $`\mathbb{R}` and `Int` to prove, at `Float` to run today, and (the
planned float carriers) at `FP32` to bound rounding and at `IEEE32Exec` to run with
NaN — the kind machinery above it written once for all of them.
:::

:::proof "def_quantity"
Realized as `structure Quantity (k : KindOfProperty) (R : Type)` carrying a
magnitude in $`R`, with same-kind addition `Quantity.add : Quantity k R → Quantity
k R → Quantity k R` (R4: the type forces both summands to share the kind). The
algebraic operations come from the {uses "def_carrier"}[carrier] typeclass on
$`R`; which operators are even _admissible_ is the orthogonal scale gate (the
proved operator stratification, {uses "thm_operator_monotonicity"}[operator
monotonicity]).
:::

:::theorem "thm_quantity_laws_parametric" (parent := "units") (lean := "PropertyKindCalculus.Quantity.laws_parametric") (tags := "capstone, proved") (effort := "medium")
*Representation-parametric additivity (R10).* The additivity laws on quantities —
commutativity, associativity, and the zero unit —
$$`q_1 + q_2 = q_2 + q_1, \quad (q_1+q_2)+q_3 = q_1+(q_2+q_3), \quad 0 + q = q`
hold over _every_ lawful carrier, established by a _single_ proof and so available
at each $`R` at once: at $`\mathbb{R}` (the proof carrier) and at `Int` with no
$`R`-specific argument. The very carrier where these laws are _absent_ — an
executable `Float`, a {uses "def_carrier"}[carrier] but not a lawful one — is what
the exec/spec refinement bridge below exists to reconcile. Builds on
{uses "def_quantity"}[the quantity layer].
:::

:::proof "thm_quantity_laws_parametric"
Proved in `PropertyKindCalculus.Quantity` (axiom-free). Each law unfolds
`Quantity.add` to its carrier operation and rewrites by the corresponding
`LawfulCarrier` field; `laws_parametric` bundles the four. Specializing to `Int`
(core) and `ℝ` (in the `Dimension` library) reuses the same proof verbatim, which
_is_ the R10 payoff.
:::

:::theorem "thm_representation_refinement" (parent := "units") (tags := "capstone, planned") (effort := "large") (priority := "high")
*Exec refines spec across representations (R10).* For a kind-$`k` quantity, the
executable float computation refines the real-number specification: applying an
operation in `IEEE32Exec` (or `FP32`) and forgetting to $`\mathbb{R}` equals
rounding the operation performed in $`\mathbb{R}`,
$$`\mathrm{toReal}\bigl(\mathrm{op}_{\mathrm{exec}}(x)\bigr) = \mathrm{round}\bigl(\mathrm{op}_{\mathbb{R}}(\mathrm{toReal}\,x)\bigr).`
So a law proved over the $`\mathbb{R}` carrier transfers to the executable run with
a bounded rounding error — the bridge that carries the
{uses "thm_quantity_laws_parametric"}[representation-parametric laws] from the
lawful carrier `ℝ` onto the executable `Float`/`IEEE32Exec` that is not lawful, so
one kind-indexed value serves both proof and execution.
:::

:::proof "thm_representation_refinement"
Planned. The refinement is the TorchLean bridge pattern (`BridgeFP32`): each
arithmetic and transcendental operation on `IEEE32Exec`/`FP32` is specified as
"compute in $`\mathbb{R}`, then round", so the equation holds by the rounding
specification, and laws lift along `toReal`.
:::

:::definition "def_unit" (parent := "units")
A _unit_ `Unit k` is a distinguished {uses "def_quantity"}[quantity] of kind $`k`
chosen as the reference: measuring expresses any quantity of kind $`k` as
$`\text{number} \times \text{unit}`. Because `Unit` is indexed by the same $`k`,
"a metre" and "a unit of gravimetric water content" inhabit different types. This
is the real-valued refinement of the proved {uses "def_metrologicalUnit"}[metrological unit]: it replaces the symbolic numeral-and-reference form with a magnitude in
$`\mathbb{R}`, so that conversion _ratios_ become arithmetic.
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

:::theorem "thm_dimensionless_kinds_distinct" (parent := "units") (lean := "PropertyKindCalculus.dim_not_injective") (tags := "capstone, proved") (effort := "small") (priority := "high")
*The dimension-1 disambiguation (the motivating capstone).* There exist distinct
kinds that map to the same dimension. Concretely, for volumetric and gravimetric
water content,
$$`\mathrm{vwc} \neq \mathrm{gwc} \qquad\text{yet}\qquad \dim(\mathrm{vwc}) = \dim(\mathrm{gwc}) = \mathbf{1},`
and likewise for permittivity and reflectivity. So the kind layer is a strict
refinement of the dimension layer: $`\dim` is not injective. This is the statement
PhysLib — and any dimension-only model, whether OWL2 or a representation-rooted
hierarchy like SysML v2's — structurally cannot make. Uses
{uses "def_kindOfProperty"}[kind-of-property] and {uses "def_dim"}[the dimension map].
:::

:::proof "thm_dimensionless_kinds_distinct"
Proved in the `Dimension` library. `vwc` and `gwc` are declared as dimensioned
kinds with distinct kind `id`s, so `vwc.kind ≠ gwc.kind` is `by decide`; both
carry `dim = 1`, so their dimensions agree by `rfl`. Together they witness
$`\exists a\ b,\ a.\mathrm{kind} \neq b.\mathrm{kind} \wedge \dim a = \dim b \wedge \dim a = 1`.
:::
