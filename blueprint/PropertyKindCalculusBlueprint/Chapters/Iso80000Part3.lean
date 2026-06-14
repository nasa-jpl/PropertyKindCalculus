import Verso
import VersoManual
import VersoBlueprint
-- The Part-3 nodes link real declarations (dimensioned kinds and checked
-- dimensional facts), so this chapter imports the Part-3 module of the `Iso80000`
-- library (PhysLib-backed, via `PropertyKindCalculus.Dimension`). The prefix nodes
-- link the core unit-prefix layer, and the surface-element nodes link the analytic
-- `AreaElement` module.
import PropertyKindCalculus.UnitPrefix
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part3.AreaElement
import PropertyKindCalculus.Iso80000.Part3.AreaClassification

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "ISO 80000-3 — Space and Time" =>

The first part whose quantity-kinds and units are specified here is ISO 80000-3,
_Space and time_. It is a reviewable seed: a few quantity-kinds — length, duration,
area, volume, speed, and the vector quantity displacement — and a few coherent SI
units — the metre, second, square metre, and so on — each carrying its exact
source, the part and the printed item designation, as data. Only *citation
locators* (item number, symbol, coherent SI unit name) are
recorded; no normative content from the licensed standard is reproduced. This is
the pattern each further part will follow, added as a chapter as its coverage
becomes available.

# Quantity-kinds and units of ISO 80000-3

:::group "iso80000_part3"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over
PhysLib's `Dimension`, so the standard's dimensional facts — area is `L²`, speed is
`L·T⁻¹` — are _checked computations_ rather than annotations. Each unit is a
{uses "def_metrologicalUnit"}[metrological unit] of its kind; commensurability is a
type-level fact, so a metre and a second are not interchangeable.
:::

:::definition "def_part3_catalogued_kind" (parent := "iso80000_part3") (lean := "PropertyKindCalculus.Iso80000.Part3.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with
its exact source in the series — the part, the printed item designation (e.g.
"3-2.1"), and the principal quantity symbol. The citation travels with the kind as
data, so the source of each definition can be rendered or audited downstream rather
than kept in a comment.
:::

:::proof "def_part3_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite`
rendering e.g. `ISO 80000-3, Second edition, 2019-10 item 3-2.1`. The seed
catalogues length (3-1.1), duration (3-9.1), area (3-2.1), volume (3-3.1), speed
(3-10.2), and displacement (3-1.11), each paired with its coherent SI unit.
:::

:::theorem "thm_part3_area_dim" (parent := "iso80000_part3") (lean := "PropertyKindCalculus.Iso80000.Part3.area_dim_length") (tags := "proved") (effort := "small")
*Area is `L²` (item 3-2.1).* The catalogued area kind carries length-exponent two
in PhysLib's dimension group — the standard's dimensional statement reproduced as a
checked computation, not an annotation. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part3_area_dim"
Proved as `area_dim_length : area.dim.length = 2` in the `Iso80000` library,
discharged by `Dim.area_length` from the `Dimension` layer.
:::

:::theorem "thm_part3_speed_dim" (parent := "iso80000_part3") (lean := "PropertyKindCalculus.Iso80000.Part3.speed_dim") (tags := "proved") (effort := "small")
*Speed is `L·T⁻¹` (item 3-10.2).* The catalogued speed kind's dimension equals
length divided by time — again a checked computation in the dimension group, not a
written-down assertion. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part3_speed_dim"
Proved as `speed_dim : speed.dim = Dim.length / Dim.time`, discharged by
`Dim.speed_eq`.
:::

:::theorem "thm_part3_metre_wellformed" (parent := "iso80000_part3") (lean := "PropertyKindCalculus.Iso80000.Part3.metre_wellFormed") (tags := "proved") (effort := "small")
*The metre is a well-formed unit (item 3-1.1).* Length is a ratio-scale kind, so it
bears a {uses "def_metrologicalUnit"}[unit] (Dybkær §13.3.5); the metre is one such
chosen reference.
:::

:::proof "thm_part3_metre_wellformed"
Proved as `metre_wellFormed : metre.WellFormed` via
`KindOfProperty.rational_bears_unit`.
:::

:::theorem "thm_part3_metre_second_incommensurable" (parent := "iso80000_part3") (lean := "PropertyKindCalculus.Iso80000.Part3.metre_second_not_commensurable") (tags := "proved") (effort := "small")
*A metre and a second are not commensurable.* Length and duration are distinct
kinds, so their units cannot be compared by ratio — a type-level fact, not a
runtime check. This is the same kind-keeps-them-apart discipline as the dimension-1
disambiguation, here across two _different_ dimensions. Uses
{uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part3_metre_second_incommensurable"
Proved as `metre_second_not_commensurable : ¬ metre.Commensurable second` by
unfolding `Commensurable` to the underlying kinds and `decide` (length's kind `id`
differs from time's).
:::

Displacement (item 3-1.11) is catalogued as a _vector_ quantity-kind. Its
vector-ness lives in the numeric carrier — a numerical vector `Fin n → R` under one
scalar unit (the metre), the ISO 80000-2 §18 reading specified as R11 (the vector
carrier of the _Units_ chapter) — while the kind and its unit are the scalar data
catalogued here. The worked vector quantity is exercised in the `DimensionExamples`
library.

# Standard prefixes: the centimetre as _centi_ · _metre_

A unit is rarely used alone — a length is reported in millimetres, kilometres, or
centimetres, all _the same kind_ as the metre but differing by a decimal factor. The
VIM4 records this directly: §1.19 lists the SI prefixes (a factor `10ⁿ` with a name
and a symbol), §1.20 and §1.21 define a _multiple_ and a _submultiple_ of a unit, and
§1.22 the _conversion factor_ between two units of the same kind. So the centimetre is
not an independent unit named `"cm"`: it is the _centi_ submultiple of the metre, and
its symbol and its `10⁻²` factor should _follow_ from that, not be asserted by hand.

:::group "iso80000_part3_prefix"
The prefix layer is added _beside_ the metrological-unit layer, not inside it: a
prefixed unit carries its provenance — which prefix, which base — and _projects_ to an
ordinary {uses "def_metrologicalUnit"}[metrological unit] of the same kind. So every
fact already proved about units (commensurability, well-formedness) transfers to the
projection unchanged, while the provenance lets the conversion factor and the
multiple/submultiple distinction be _read off_ rather than restated.
:::

:::definition "def_prefixed_unit" (parent := "iso80000_part3_prefix") (lean := "PropertyKindCalculus.PrefixedUnit")
A _prefixed unit_ is an `SIPrefix` (a decimal factor `10ⁿ` with its name and symbol,
the VIM4 §1.19 table) applied to a base {uses "def_metrologicalUnit"}[unit]. It
projects to a metrological unit of the _same kind_ with the prefix symbol prepended
(`"c"` ++ `"m"` = `"cm"`), and exposes its §1.22 conversion factor as the exponent and
its §1.20/§1.21 status as a multiple or submultiple.
:::

:::proof "def_prefixed_unit"
Realized as `structure SIPrefix` (`name`, `symbol`, `exponent : Int`) with the full
§1.19 table, and `structure PrefixedUnit` (`siPrefix`, `base`) with `toUnit`
(the projection), `conversionExponent`, `IsMultiple`, and `IsSubmultiple`. The
projection preserves the kind, so `toUnit_wellFormed` and `commensurable_base` follow
by reflexivity.
:::

:::theorem "thm_part3_centimetre_conversion" (parent := "iso80000_part3_prefix") (lean := "PropertyKindCalculus.Iso80000.Part3.centimetre_conversionExponent") (tags := "proved") (effort := "small")
*The centimetre is the _centi_ submultiple of the metre, factor `10⁻²`.* Its symbol
`"cm"` and its conversion exponent `-2` are checked computations from the prefix and
the base, and it stays commensurable with the metre. Uses
{uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part3_centimetre_conversion"
`centimetre` is now `(metre.withPrefix SIPrefix.centi).toUnit`. The facts
`centimetre_symbol = "cm"`, `centimetre_conversionExponent = -2`,
`centimetre_isSubmultiple`, and `centimetre_wellFormed` are discharged by `rfl` /
`decide`; `metre_centimetre_commensurable` holds because the prefix leaves the kind
unchanged.
:::

# Capturing a Remark's mathematics: the surface element of an area

Each ISO 80000 item carries a _Remarks_ field, and those remarks often hold the
quantity's defining mathematics. Item 3-2.1 (area) is the example: its remark gives
the _surface element_ of a surface in terms of the Gaussian coordinates `u`, `v` and
the determinant `g` of the metric tensor (ISO 80000-2). Rather than transcribe the
licensed text or reduce it to a dimensional annotation, this work _formalizes the
relation_ — as real differential-geometric objects with proved properties — so the
mathematics behind the kind is itself checked.

:::group "iso80000_part3_area"
The metric tensor is realized as the Gram matrix of the two tangent vectors `∂r/∂u`,
`∂r/∂v` (its entries are the classical `E`, `F`, `G`); its determinant is `g`; and the
surface element is `dA = √g`. The standard writes the element with `g`; the
area-consistent Riemannian element is its _square root_, and the formalization makes
that convention explicit by _proving_ that a flat patch then recovers its Euclidean
area. The kind whose magnitudes these areas are is the catalogued
{uses "def_quantity"}[quantity]-kind area, dimension `L²`.
:::

:::definition "def_first_fundamental_form" (parent := "iso80000_part3_area") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaElement.firstFundamentalForm")
The _first fundamental form_ (the metric tensor of ISO 80000-2) at a point is the
`2 × 2` Gram matrix `⟪tᵢ, tⱼ⟫` of the surface's two tangent vectors. It is symmetric
and positive-semidefinite, so its determinant `g` is non-negative.
:::

:::proof "def_first_fundamental_form"
Realized as `firstFundamentalForm t := Matrix.gram ℝ t` over Mathlib's Gram-matrix
library; symmetry is `isHermitian_gram` and `metricDet_nonneg` is the determinant of a
positive-semidefinite matrix.
:::

:::definition "def_area_element" (parent := "iso80000_part3_area") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaElement.areaElement")
The _surface element_ `dA = √g` is the area-element density at a point, and the _area_
of a surface patch is its integral over the parameter region (`A = ∬ √g du dv`). Uses
{uses "def_dim"}[the dimension map] for the `L²` reading of the resulting kind.
:::

:::proof "def_area_element"
`areaElement t := Real.sqrt (metricDet t)` and `surfaceArea t s := ∫ x in s,
areaElement (t x)`. `surfaceArea_const` shows a uniformly-parametrized patch has area
`element × (area of the parameter region)`.
:::

:::theorem "thm_area_element_sq" (parent := "iso80000_part3_area") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaElement.areaElement_sq") (tags := "proved") (effort := "small")
*The element squares back to the determinant: `(dA)² = g`.* The `√` in `dA = √g` is
faithful — the element is exactly the square root of the determinant of the metric
tensor.
:::

:::proof "thm_area_element_sq"
`areaElement_sq : areaElement t ^ 2 = metricDet t`, from `Real.sq_sqrt` and the
non-negativity of `g`.
:::

:::theorem "thm_area_element_flat" (parent := "iso80000_part3_area") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaElement.areaElement_eq_abs_det") (tags := "proved") (effort := "medium")
*A flat patch recovers its Euclidean area.* For a surface lying in the plane the
element equals `|det A|`, the change-of-variables area density of the parametrization —
so the `√g` reading computes the _actual_ area. This is the correctness anchor that
pins the convention the prose remark leaves implicit.
:::

:::proof "thm_area_element_flat"
`areaElement_eq_abs_det : areaElement t = |(Matrix.of fun i j => t j i).det|`, via
`gram_eq_conjTranspose_mul` (so `g = (det A)²`) and `Real.sqrt_sq_eq_abs`.
:::

:::theorem "thm_area_element_regular" (parent := "iso80000_part3_area") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaElement.areaElement_pos_iff") (tags := "proved") (effort := "small")
*Regularity.* The element is strictly positive exactly when the two tangent vectors
are linearly independent — a non-degenerate (regular) point. A vanishing element marks
a degenerate parametrization.
:::

:::proof "thm_area_element_regular"
`areaElement_pos_iff : 0 < areaElement t ↔ LinearIndependent ℝ t`, from
`Real.sqrt_pos` and `det_gram_ne_zero_iff_linearIndependent`.
:::

# Why it matters: classification and metrological consistency at the quantity level

Formalizing a remark's mathematics is not decoration. It earns its keep by turning the
quantity-kind into a working _classifier_ and by moving metrological checking down to
the _quantity level_, where the type system enforces it.

_Classifying quantities._ The surface-area formula does not return a bare real number:
its output is, by construction, a magnitude of the _one_ catalogued kind area. Any
quantity a downstream model computes this way — the area of a field, a footprint, a
cross-section — is automatically _classified_ as the same kind, dimension `L²`, unit
the square metre. The kind is the genus under which every such quantity falls, and the
defining relation is what places it there. So formalizing the remark gives users a
principled answer to "what _is_ this quantity?" — it is a value of area, because the
relation that produced it is area's defining relation.

_Verifying metrological consistency._ Because the kind carries its dimension and its
own scalar unit, the consistency checks happen at the quantity level and cannot be
skipped. Two areas combine — addition is defined on the area carrier — but an area and
a length are _different types_, so adding them does not type-check: the dimensionless
numeric conflation a spreadsheet would silently allow is rejected. An area is not
measurable in metres, because the square metre and the metre are not commensurable, a
fact of the types rather than a runtime guard. And the dimensional invariant `L²`
travels with _every_ value of the kind. The remark's mathematics, the kind, and these
consistency guarantees are thus one chain: the relation anchors the kind, the kind
classifies the quantity, and the classification _is_ the metrological check.

These claims are exercised as checked facts in the `DimensionExamples` library: a
surface area built from the analytic element and classified as an area quantity, the
`L²` invariant, the area-plus-area combination, and the rejected area-versus-length and
square-metre-versus-metre conflations.

This is the *verified instantiation* requirement (R12): a classification is a
certificate that a quantity satisfies its kind's defining relation, not a bare tag. For
area, the defining relation is the surface element above, and it yields two concrete
certificate forms.

:::group "iso80000_part3_classified"
The closed-form certificate is the product (a rectangle's area is width × height); the
general certificate is the integral (an area is the area of an actual surface). Both
classify the *one* area kind, and a property of the defining relation transports to
every quantity certified under it.
:::

:::theorem "thm_rectangle_area_isproduct" (parent := "iso80000_part3_classified") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaClassification.rectangleArea_isProduct") (tags := "proved") (effort := "small")
*A rectangle's area is verified-classified by construction.* `rectangleArea w h` is
built as the product of two lengths (area = length · length), so its
area-classification certificate holds by construction.
:::

:::proof "thm_rectangle_area_isproduct"
`rectangleArea w h := Quantity.mul area_is_length_times_length w h`, and
`rectangleArea_isProduct` is `rfl` — the certificate of the constructed product.
:::

:::theorem "thm_certified_area_nonneg" (parent := "iso80000_part3_classified") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaClassification.certified_surfaceArea_nonneg") (tags := "proved") (effort := "medium")
*Property transport.* Every certified surface area is non-negative — the surface
element is `≥ 0` (a property of area's defining relation), instantiated at the quantity
level through the certificate.
:::

:::proof "thm_certified_area_nonneg"
`certified_surfaceArea_nonneg` rewrites the certificate `q.magnitude = surfaceArea t s`
and applies `surfaceArea_nonneg` (the integral of a non-negative element, by
`setIntegral_nonneg` and `areaElement_nonneg`).
:::
