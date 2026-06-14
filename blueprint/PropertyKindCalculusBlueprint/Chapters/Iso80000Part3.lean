import Verso
import VersoManual
import VersoBlueprint
-- The Part-3 nodes link real declarations (dimensioned kinds and checked
-- dimensional facts), so this chapter imports the Part-3 module of the `Iso80000`
-- library (PhysLib-backed, via `PropertyKindCalculus.Dimension`).
import PropertyKindCalculus.Iso80000.Part3

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
