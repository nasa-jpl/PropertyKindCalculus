import Verso
import VersoManual
import VersoBlueprint
-- Every node below links a real declaration, so this chapter imports the `Dimension`
-- library (the one PhysLib + Mathlib dependency) for the dimension-1 disambiguation
-- capstone, and `UnitReal` for the real-valued chosen-reference unit.
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.UnitReal

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

:::definition "def_carrier_refinement" (parent := "units") (lean := "PropertyKindCalculus.CarrierRefinement")
A _carrier refinement_ `CarrierRefinement E S` specifies how an _exec_ carrier
$`E` (fast, lossy) stands in for a _spec_ carrier $`S` (exact): a forgetful map
`toSpec : E → S` (the analogue of TorchLean's `toReal`) and a spec-side
`round : S → S`, with the single law that forgetting an exec addition equals
rounding the spec addition,
$$`\mathrm{toSpec}(x +_E y) = \mathrm{round}\,(\mathrm{toSpec}\,x +_S \mathrm{toSpec}\,y).`
In plain engineering terms it is the _rounding contract_ between a slow exact
number type and the fast machine number that stands in for it. Builds on the
{uses "def_carrier"}[carrier].
:::

:::proof "def_carrier_refinement"
Realized as the `CarrierRefinement` class (core, axiom-free). TorchLean's `FP32`
gives an _unconditional_ instance over $`\mathbb{R}`, and `IEEE32Exec` refines
$`\mathbb{R}` on the finite path — both in the separately built `Torch` library.
:::

:::theorem "thm_representation_refinement" (parent := "units") (lean := "PropertyKindCalculus.Quantity.add_refines") (tags := "capstone, proved") (effort := "large") (priority := "high")
*Exec refines spec across representations (R10).* For a kind-$`k` quantity, the
exec sum _viewed in the spec carrier_ is the rounding of the spec sum,
$$`\mathrm{toSpec}(x +_E y) = \mathrm{round}\,(\mathrm{toSpec}\,x +_S \mathrm{toSpec}\,y),`
established over _any_ {uses "def_carrier_refinement"}[carrier refinement] and so
holding at each at once. A law proved over the lawful spec carrier therefore
transfers to the executable run with one rounding step — the bridge that carries
the {uses "thm_quantity_laws_parametric"}[representation-parametric laws] from the
lawful `ℝ` onto a float that is _not_ lawful, so one kind-indexed value serves both
proof and execution.
:::

:::proof "thm_representation_refinement"
Proved as `Quantity.add_refines` (core, axiom-free): the `CarrierRefinement` bridge
law lifted along the kind index. It is instantiated concretely in the separately
built `Torch` library at TorchLean's binary32 — an _unconditional_
`CarrierRefinement FP32 ℝ` (the rounding spec has no overflow, so the law holds by
computation) and a _conditional_ `IEEE32Exec` refinement on the finite/no-overflow
path (`Quantity.add_refines_exec`), where overflow is an explicit hypothesis rather
than a silent failure. This is TorchLean's `Bridge/FP32` pattern ("compute in
$`\mathbb{R}`, then round").
:::

:::definition "def_vector_carrier" (parent := "units") (lean := "PropertyKindCalculus.instLawfulCarrierPi")
*Vector quantities: numerical array × one scalar unit (R11, ISO 80000-2 §18).* A
vector (or tensor) quantity is a _numerical_ array carried at one kind with one
_scalar_ {uses "def_metrologicalUnit"}[unit] — not a per-coordinate collection of
`number × unit` values; "all units are scalars". This is the
{uses "def_carrier"}[carrier] taken at a function-space type: `Fin n → R` is a
(lawful) carrier whenever $`R` is, pointwise, so a vector quantity is
`Quantity k (Fin n → R)` and the
{uses "thm_quantity_laws_parametric"}[additivity laws] transfer to it by the same
parametric proof. The quantity is coordinate-independent; only its numerical
components depend on the frame.
:::

:::proof "def_vector_carrier"
Realized as the pointwise `Carrier (ι → R)` / `LawfulCarrier (ι → R)` instances
(core). The fuller structural apparatus — coordinate frames, tensor variance,
transforms — remains a separate, owed axis.
:::

:::definition "def_unit" (parent := "units") (lean := "PropertyKindCalculus.RealUnit")
A _unit_ `RealUnit k` is a distinguished {uses "def_quantity"}[quantity] of kind $`k`
chosen as the reference: measuring expresses any quantity of kind $`k` as
$`\text{number} \times \text{unit}`. Because it is indexed by the same $`k`,
"a metre" and "a unit of gravimetric water content" inhabit different types. This
is the real-valued refinement of the proved {uses "def_metrologicalUnit"}[metrological unit]: it replaces the symbolic numeral-and-reference form with a magnitude in
$`\mathbb{R}`, so that conversion _ratios_ become arithmetic.
:::

:::proof "def_unit"
Realized as `RealUnit k`, a `Quantity k ℝ` chosen as the reference together with the one
condition the choice must satisfy: `ref_ne_zero`. That field is what the phrase "express the
ratio of the two quantities as a number" presupposes and the symbolic layer never has to
state — a reference of magnitude zero expresses no ratio — and carrying it makes a degenerate
unit not a term of the type. Measuring is `measure : Quantity k ℝ → RealUnit k → ℝ`, division
by the reference; `ofNumber` is the multiplication back; and the §13.3.3 number-and-reference
round-trip is then a bijection in both directions (`measure_ofNumber`, `ofNumber_measure`)
rather than a definitional unfolding. `ratio` is the §1.22 conversion factor for an _arbitrary_
chosen reference, nonzero from the two licenses and reciprocal in the two directions, of which
the {uses "thm_unit_conversion_roundtrip"}[power-of-radix factor] is the special case. The
refinement inherits the §9.13.4 exclusions rather than widening them: `WellFormed` is the
symbolic layer's `BearsUnit`, so a nominal or ordinal kind bears no real-valued unit either.
:::

:::theorem "thm_unit_conversion_roundtrip" (parent := "units") (lean := "PropertyKindCalculus.PrefixedUnit.convertExp_roundtrip") (tags := "capstone, proved") (effort := "medium") (priority := "high")
*Unit conversion is a faithful round-trip.* For two commensurable units $`u_1, u_2`
of the same kind $`k`, converting a magnitude from $`u_1` to $`u_2` and back is the
identity:
$$`\mathrm{convert}_{u_2 \to u_1}\bigl(\mathrm{convert}_{u_1 \to u_2}(x)\bigr) = x.`
This is proved for the realized case: the {uses "def_si_prefix"}[SI-prefixed] (decimal)
and {uses "def_binary_prefix"}[binary-prefixed] (IEC 80000-13) units, where the §1.22
conversion factor is a *power of the radix* — ten for SI, two for binary. That factor is
kept as its integer *exponent*, so the two directions are reciprocal on the nose
($`+5` then $`-5` for $`\mathrm{km}\leftrightarrow\mathrm{cm}`; $`+10` then $`-10` for
$`\mathrm{MiB}\leftrightarrow\mathrm{KiB}`) — exact over $`\mathbb{Z}`
(`convertExp_roundtrip`) and, numerically, over $`\mathbb{R}` via a power-of-radix
factor that is *structurally* nonzero (`convertReal_roundtrip`). The exponent
bookkeeping is blind to the radix, so *one* proof serves both prefix families, gated
to a common radix; conversion across radices (a power of ten is never a power of two)
and across kinds is simply undefined — a type-level fact, not a runtime check. The
fully general conversion by an arbitrary chosen-reference ratio, over the
{uses "def_unit"}[real-valued unit], remains the deeper refinement below.
:::

:::proof "thm_unit_conversion_roundtrip"
Because the conversion factor is a power of ten, its exponent is an `Int` — an
element of an additive group — so the shift $`u_1\to u_2` (`shift`, the difference of
the prefix exponents) and the shift back sum to zero (`shift_add_symm`). The
round-trip on the decimal exponent is then $`x + (e_1 - e_2) + (e_2 - e_1) = x`,
closed by `omega` with no rounding. The numeric $`\mathbb{R}` companion multiplies by
$`10^{e_1-e_2}` then $`10^{e_2-e_1}`; `zpow_add₀` on $`10\neq 0` collapses the
exponents to $`10^0 = 1`. Neither needs a chosen-reference nonzeroness hypothesis —
that is what the general real-valued case (planned) must still supply.
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

:::definition "def_si_prefix" (parent := "units") (lean := "PropertyKindCalculus.SIPrefix")
A _decimal SI prefix_ `SIPrefix` is a name and symbol denoting a power-of-ten
factor (e.g. _centi_ = $`10^{-2}`). Applied to a unit it produces a multiple
(VIM4 2CD 1.20) or submultiple (1.21) of that unit.
:::

:::proof "def_si_prefix"
A `structure SIPrefix` carrying `name`, `symbol`, and an integer `exponent` (the
factor is $`10^{\text{exponent}}`); the full SI set (quetta … quecto) is
enumerated as `def`s.
:::

:::definition "def_binary_prefix" (parent := "units") (lean := "PropertyKindCalculus.BinaryPrefix")
A _binary prefix_ `BinaryPrefix` (IEC 80000-13) is the information-technology
counterpart of an SI prefix, denoting a power-of-_two_ factor: _kibi_ = $`2^{10}`,
_mebi_ = $`2^{20}`, …. IEC 80000-13 introduced these to disambiguate the "kilobyte"
between $`10^3` and $`2^{10}` bytes — _kibi_ names the binary one. They are *not* SI
prefixes (the SI is decimal-only), so they are a distinct type; but they form the same
multiples/submultiples and bear the same §1.22 conversion factor, and so reuse one
prefixed-unit and one {uses "thm_unit_conversion_roundtrip"}[conversion round-trip].
:::

:::proof "def_binary_prefix"
A `structure BinaryPrefix` carrying `name`, `symbol`, and an integer `exponent` (the
factor is $`2^{\text{exponent}}`); the eight prefixes kibi … yobi are enumerated as
`def`s. A `PrefixedUnit` records the resolved `radix` (10 or 2) so that a single
`convertExp_roundtrip` serves both families, gated to a common radix.
:::

# Verified classification and instantiable kind-laws (R12)

A quantity `Quantity k R` records its kind `k` as a _tag_:
the magnitude is an arbitrary `R`, so a value can be labelled with a kind it has not
earned (`⟨999⟩` type-checks as an area). R12 upgrades a classification from an
_assertion_ to a _certificate_: a quantity is classified under a kind by a proof that
it satisfies the kind's _defining relation_ — the formalized ISO 80000 _Remark_ — to
quantities of the kinds it is built from. The kind becomes a _refinement_ (a tag plus
its earned proof), not a label.

The payoff is _instantiation_. Every kind-law is stated as a carrier-parametric
universal over quantities with the kind-relation as a premise; "instantiating it at
the quantity level" is then ordinary application, and any property of a kind's defining
relation transports to _every_ quantity certified under it. This is the inter-kind
generalization of the carrier-parametric laws of R10.

:::group "classification"
The canonical pattern is the _product_, which covers a large fraction of the ISQ
(area = length · length, volume = area · length, energy = force · length). The
general machinery lives in the Mathlib-free core; the dimensional refinement
(`k.dim = k₁.dim · k₂.dim`) lives in the dimension layer, and analysis-shaped
relations (area as a surface integral) in the Mathlib-backed layer.
:::

:::definition "def_product_kind" (parent := "classification") (lean := "PropertyKindCalculus.ProductKind")
A _product kind-law_ `ProductKind k₁ k₂ k` records that `k` is the product kind of
`k₁` and `k₂`. In the core it carries the scale precondition — all three are
ratio-scale, since only ratio quantities multiply (Dybkær §13.3.5); the dimension
layer refines it with the dimensional equation $`k.\dim = k_1.\dim \cdot k_2.\dim`.
:::

:::proof "def_product_kind"
Realized as `structure ProductKind` with three `IsRational` fields. A concrete law
such as area = length · length is the value `⟨rfl, rfl, rfl⟩`.
:::

:::definition "def_is_product" (parent := "classification") (lean := "PropertyKindCalculus.Quantity.IsProduct")
The _certificate_ `q.IsProduct h a b` states that `q` (of kind `k`) is the product of
`a` (of `k₁`) and `b` (of `k₂`): its magnitude is the product of theirs. A proof of
this certifies `q`'s classification, rather than asserting it. It is a separate
proposition, so {uses "def_quantity"}[`Quantity`] stays a clean tag and certificates
are carried only when needed. The smart constructor `Quantity.mul` yields a quantity
whose certificate holds by construction.
:::

:::proof "def_is_product"
`Quantity.IsProduct h q a b := q.magnitude = a.magnitude * b.magnitude` over a carrier
with multiplication; `Quantity.mul h a b := ⟨a.magnitude * b.magnitude⟩`, and
`mul_isProduct` is `rfl`.
:::

:::theorem "thm_isproduct_unique" (parent := "classification") (lean := "PropertyKindCalculus.Quantity.isProduct_unique") (tags := "proved") (effort := "small")
*A kind-law that instantiates at the quantity level.* A quantity certified as the
product of `a` and `b` is unique — and any certified product equals the
smart-constructed one (`eq_mul_of_isProduct`, canonicity). Supplying concrete
quantities gives the quantity-level fact by application. Axiom-free.
:::

:::proof "thm_isproduct_unique"
`isProduct_unique` rewrites both magnitudes to `a.magnitude * b.magnitude` and closes
by structure η; `eq_mul_of_isProduct` is `isProduct_unique` against `mul_isProduct`.
Both depend on no axioms.
:::

:::definition "def_quotient_kind" (parent := "classification") (lean := "PropertyKindCalculus.QuotientKind")
A _quotient kind-law_ `QuotientKind k₁ k₂ k` records that `k` is the quotient kind
`k = k₁ / k₂` (speed = length / duration; plane angle = arc / radius, where the lengths
cancel). Like the product, it carries the ratio-scale precondition in the core and is
refined by `k.dim = k₁.dim / k₂.dim` in the dimension layer. Its certificate
`Quantity.IsQuotient` and smart constructor `Quantity.div` mirror the product family
exactly, over the core `Div` class.
:::

:::proof "def_quotient_kind"
`structure QuotientKind` with three `IsRational` fields; `Quantity.div h a b :=
⟨a.magnitude / b.magnitude⟩`, `div_isQuotient` is `rfl`, and `isQuotient_unique` /
`eq_div_of_isQuotient` are the product family's proofs transcribed. Axiom-free.
:::

:::definition "def_reciprocal_kind" (parent := "classification") (lean := "PropertyKindCalculus.ReciprocalKind")
A _reciprocal kind-law_ `ReciprocalKind k₁ k` records that `k = 1 / k₁` (frequency =
1 / period; curvature = 1 / radius; repetency = 1 / wavelength) — the unary special
case, over the core `Inv` class, refined by `k.dim = (k₁.dim)⁻¹`. All three families
(product, quotient, reciprocal) stay Mathlib-free, using only toolchain-level
arithmetic classes.
:::

:::proof "def_reciprocal_kind"
`structure ReciprocalKind` with two `IsRational` fields; `Quantity.recip h a :=
⟨a.magnitude⁻¹⟩`, `recip_isReciprocal` is `rfl`, with `isReciprocal_unique` /
`eq_recip_of_isReciprocal` as before. Axiom-free.
:::
