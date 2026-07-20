import Verso
import VersoManual
import VersoBlueprint
-- The Part-3 nodes link real declarations (dimensioned kinds, checked dimensional
-- facts, the specialization lattice, and the formalized remarks), so this chapter
-- imports the Part-3 modules of the `Iso80000` library (PhysLib-backed). The prefix
-- nodes link the core unit-prefix layer; the surface- and volume-element nodes link
-- the analytic `AreaElement` / `VolumeElement` modules; the algebraic-remark nodes
-- link `DefiningRelations`.
import PropertyKindCalculus.UnitPrefix
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part3.AreaElement
import PropertyKindCalculus.Iso80000.Part3.AreaClassification
import PropertyKindCalculus.Iso80000.Part3.VolumeElement
import PropertyKindCalculus.Iso80000.Part3.DefiningRelations
import PropertyKindCalculusBlueprint.ItemIndex
-- The plane-angle / radian-vs-steradian nodes engage the live metrology debate over
-- whether angle should have its own dimension, so this chapter cites those sources.
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint.ItemIndex

/-- Default blueprint node for ISO/IEC 80000-3 item-index rows (editorial). -/
def part3Default : String := "def_part3_catalogued_kind"

/-- Per-item blueprint cross-reference overrides for the ISO/IEC 80000-3 item
index (editorial; items not listed link to `part3Default`). Every other column
is generated from `PropertyKindCalculus.Iso80000.Part3.catalogue`. -/
def part3Refs : List (String × String) := [
  ("3-1.1", "def_part3_length_species"),
  ("3-1.2", "thm_part3_width_ne_distance"),
  ("3-1.3", "def_part3_length_species"),
  ("3-1.4", "def_part3_length_species"),
  ("3-1.5", "def_part3_length_species"),
  ("3-1.6", "thm_part3_radius_specializes_length"),
  ("3-1.7", "def_part3_length_species"),
  ("3-1.8", "thm_part3_width_ne_distance"),
  ("3-1.9", "def_part3_length_species"),
  ("3-1.10", "def_part3_length_species"),
  ("3-1.11", "def_part3_length_species"),
  ("3-1.12", "def_part3_length_species"),
  ("3-3", "thm_part3_area_dim"),
  ("3-4", "def_volume_element"),
  ("3-5", "thm_part3_plane_angle_dimensionless"),
  ("3-6", "thm_part3_dim_one_collision"),
  ("3-7", "thm_part3_dim_one_collision"),
  ("3-8", "thm_part3_radian_steradian"),
  ("3-9", "thm_part3_metre_second_incommensurable"),
  ("3-10.1", "thm_part3_dim_collision"),
  ("3-10.2", "thm_part3_speed_dim"),
  ("3-12", "thm_part3_dim_collision"),
  ("3-14", "thm_part3_frequency_reciprocal"),
  ("3-16", "thm_part3_dim_one_collision"),
  ("3-17.1", "thm_part3_frequency_reciprocal"),
  ("3-17.2", "thm_part3_dim_collision"),
  ("3-18", "thm_part3_dim_collision"),
  ("3-19", "def_part3_length_species"),
  ("3-24", "thm_part3_dim_collision"),
  ("3-25", "thm_part3_dim_one_collision")
]

/-- The ISO/IEC 80000-3 item index, generated live from the catalogue. -/
def part3IndexTable : DocTable :=
  standardIndex PropertyKindCalculus.Iso80000.Part3.catalogue part3Default part3Refs

#doc (Manual) "ISO 80000-3 — Space and Time" =>

The first part whose quantity-kinds and units are specified in full is ISO 80000-3,
_Space and time_. Every item — all of 3-1.1 … 3-26.3 — is catalogued: length, the
width/height/distance/radius family, area, volume, the angles, duration, the
frequencies, velocity and speed, acceleration, the wave quantities, and the rest,
each carrying its exact source as data: the part, the printed item designation, the
principal quantity symbol, and the coherent SI unit symbol. Only *citation locators*
are recorded; no normative content (definitions, remarks) from the licensed standard
is reproduced. The defining _mathematics_ of selected remarks is formalized in its own
right, in the sibling modules linked below.

Part 3 turns out to be an unusually good proving ground for the calculus, because the
standard itself is full of distinctions that a dimension-only or representation-only
model cannot make: a dozen different length quantities, several dimensionless angles,
and three families of quantities that share a dimension while remaining distinct kinds.

# Quantity-kinds and units of ISO 80000-3

:::group "iso80000_part3"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over
PhysLib's `Dimension`, so the standard's dimensional facts — area is `L²`, volume is
`L³`, speed is `L·T⁻¹` — are _checked computations_ rather than annotations. Each unit
is a {uses "def_metrologicalUnit"}[metrological unit] of its kind; commensurability is a
type-level fact, so a metre and a second are not interchangeable.
:::

:::definition "def_part3_catalogued_kind" (parent := "iso80000_part3") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "3-3"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with
the kind as data, so the source of each definition can be rendered or audited
downstream rather than kept in a comment.
:::

:::proof "def_part3_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `ISO 80000-3, Second edition, 2019-10 item 3-3`. The `catalogue` lists all 42
items in item order — length (3-1.1), area (3-3), volume (3-4), duration (3-9), speed
(3-10.2), frequency (3-17.1), … — each paired with its coherent SI unit symbol.
:::

:::theorem "thm_part3_area_dim" (parent := "iso80000_part3") (lean := "PropertyKindCalculus.Iso80000.Part3.area_dim_length") (tags := "proved") (effort := "small")
*Area is `L²` (item 3-3).* The catalogued area kind carries length-exponent two in
PhysLib's dimension group — the standard's dimensional statement reproduced as a checked
computation, not an annotation. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part3_area_dim"
Proved as `area_dim_length : area.dim.length = 2` in the `Iso80000` library, discharged
by `Dim.area_length` from the `Dimension` layer. The companion `volume_dim_length`
(item 3-4) gives length-exponent three.
:::

:::theorem "thm_part3_speed_dim" (parent := "iso80000_part3") (lean := "PropertyKindCalculus.Iso80000.Part3.speed_dim") (tags := "proved") (effort := "small")
*Speed is `L·T⁻¹` (item 3-10.2).* The catalogued speed kind's dimension equals length
divided by time — a checked computation in the dimension group. Uses
{uses "def_dim"}[the dimension map].
:::

:::proof "thm_part3_speed_dim"
Proved as `speed_dim : speed.dim = Dim.length / Dim.time`, discharged by `Dim.speed_eq`.
The catalogue also records `curvature_dim_length = -1` (item 3-2, `L⁻¹`),
`frequency_dim_time = -1` (item 3-17.1, `T⁻¹`), and `acceleration_dim_time = -2`
(item 3-11, `L·T⁻²`).
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
*A metre and a second are not commensurable.* Length and duration are distinct kinds,
so their units cannot be compared by ratio — a type-level fact, not a runtime check.
Uses {uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part3_metre_second_incommensurable"
Proved as `metre_second_not_commensurable : ¬ metre.Commensurable second` by unfolding
`Commensurable` to the underlying kinds and `decide` (length's kind `id` differs from
duration's).
:::

# The length family: distinguishing kinds by measurement principle

ISO 80000-3 lists width (3-1.2), height (3-1.3), thickness (3-1.4), diameter (3-1.5),
radius (3-1.6), path length (3-1.7), distance (3-1.8), and more as _separate items_ —
yet every one of them has dimension `L` and ratio scale. The standard distinguishes
them only in _prose_: a width is a transverse extent, a distance is a shortest path,
and so on. A dimension-only or representation-only model cannot capture the
difference at all; it sees one type, "a real number of metres", for all of them.

This is exactly requirement _R2_, and Part 3 is where it earns its keep on the real
standard. Item 3-1.1, _length_, is the broad genus. Each later item is specified as a
_species_ of length, distinguished *not by fiat* (not merely by a different name) but
by an explicit _measurement principle_ — Dybkær's examination principle (§7.5), a
genuine defining aspect. The species are then provably distinct kinds, while remaining
_mutually comparable_ as lengths; and the specialization edges mirror the standard's
own "defined in terms of" links (a diameter is a width of a circle, a radius is half a
diameter, a distance is a shortest path length).

:::group "iso80000_part3_length"
The length species are individuated by an {uses "def_examination"}[examination
principle] and arranged as a {uses "def_specializes"}[specialization] lattice over the
general length kind. This is what lets the calculus answer the question the standard
leaves to prose — _why_ is a width not a distance? — with a proof rather than a naming
convention, while keeping the two comparable so an explicit up-cast to length is still
available.
:::

:::definition "def_part3_length_species" (parent := "iso80000_part3_length") (lean := "PropertyKindCalculus.Iso80000.Part3.lengthSpecies")
A _length species_ is a ratio-scale {uses "def_quantity"}[quantity]-kind of dimension
`L` carrying an {uses "def_examination"}[examination principle] — this work's own terse
descriptor of the measurement principle that distinguishes it (transverse extent,
shortest path, centre-to-rim, …), never the standard's normative definition. Width,
height, thickness, diameter, radius, path length, distance, radial distance, the
position and displacement vectors, the radius of curvature, and the wavelength are all
species of the general length kind (item 3-1.1).
:::

:::proof "def_part3_length_species"
`lengthSpecies id p := { kind := { id, scale := .ratio, examPrinciple := some p.id },
dim := Dim.length }`. The general `length` carries no examination principle; the
direct-parent edges of the family are collected in an `Edge` relation mirroring the
standard's definitional links (thickness and diameter via width, radius via diameter,
distance via path length, …).
:::

:::theorem "thm_part3_width_ne_distance" (parent := "iso80000_part3_length") (lean := "PropertyKindCalculus.Iso80000.Part3.width_ne_distance") (tags := "proved") (effort := "small")
*Width and distance are distinct kinds — by measurement principle, not by fiat.* A
width (transverse extent) and a distance (shortest path) are different kinds _because
they are examined by different principles_, proved through `distinct_of_examPrinciple`
(§7.5) rather than by appealing to their `id` strings. Same dimension `L`, same scale,
different kind. Uses {uses "def_examination"}[the examination principle].
:::

:::proof "thm_part3_width_ne_distance"
`width_ne_distance : width.kind ≠ distance.kind`, from
`KindOfProperty.distinct_of_examPrinciple` applied to the differing examination
principles `transverse-extent` and `shortest-path` (a `decide` on the `Option String`
links). The companion `width_examinedBy` checks the kind-to-principle link. Axiom-free.
:::

:::theorem "thm_part3_radius_specializes_length" (parent := "iso80000_part3_length") (lean := "PropertyKindCalculus.Iso80000.Part3.radius_specializes_length") (tags := "proved") (effort := "small")
*A radius specializes length — transitively.* Through the chain radius ⊑ diameter ⊑
width ⊑ length, a radius is a length: specialization is the reflexive-transitive
closure of the family's edges, a genuine preorder (a lattice, not just direct edges).
Uses {uses "def_specializes"}[specialization].
:::

:::proof "thm_part3_radius_specializes_length"
`radius_specializes_length`, built from `Specializes.of_edge` on
`radius_diameter`, `diameter_width`, `width_length` composed by `Specializes.trans`.
Axiom-free.
:::

:::theorem "thm_part3_width_distance_comparable" (parent := "iso80000_part3_length") (lean := "PropertyKindCalculus.Iso80000.Part3.width_distance_comparable") (tags := "proved") (effort := "small")
*Comparability is preserved.* Width and distance, though distinct kinds, remain
_mutually comparable_ — they share the super-kind length, so combining them is possible
but only via an explicit up-cast, never silently. Uses
{uses "def_specializes"}[specialization].
:::

:::proof "thm_part3_width_distance_comparable"
`width_distance_comparable : MutuallyComparable Edge width.kind distance.kind`, with
witness `length.kind`, `width` reaching it by one edge and `distance` by two
(distance ⊑ path length ⊑ length). Axiom-free.
:::

# Dimension does not classify; the kind does

Part 3 alone is dense with _dimension collisions_ — distinct kinds that the dimension
functor cannot tell apart. Plane angle, rotational displacement, phase angle, solid
angle, rotation, and the logarithmic decrement are _all_ dimension one. Frequency,
rotational frequency, angular frequency, angular velocity, and the damping coefficient
are _all_ `T⁻¹`. Velocity and speed are both `L·T⁻¹`. The dimension is the same; the
kind is not — and so the units differ too, a radian is not a steradian and a hertz is
not a radian-per-second, though each pair shares a dimension.

:::group "iso80000_part3_collision"
These are the dimension-1 disambiguation capstone, now on _standard_ quantities rather
than a constructed example: the {uses "def_dim"}[dimension map] identifies the members
of each pair, while the kind layer keeps them apart, both as kinds and as
{uses "def_metrologicalUnit"}[units].
:::

:::theorem "thm_part3_dim_one_collision" (parent := "iso80000_part3_collision") (lean := "PropertyKindCalculus.Iso80000.Part3.iso80000_3_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard.* There exist distinct ISO 80000-3
kinds with the same dimension one — plane angle and solid angle witness it. No
dimension-only type system can separate them; the kind layer does. This generalizes
the calculus's `dim_not_injective` capstone to the published standard. Uses
{uses "def_dim"}[the dimension map].
:::

:::proof "thm_part3_dim_one_collision"
`iso80000_3_dim_one_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim =
b.dim ∧ a.dim = 1`, witnessed by `⟨planeAngle, solidAngle, …⟩` with
`planeAngle_ne_solidAngle` (a `decide`) and reflexivity. Axiom-free.
:::

:::theorem "thm_part3_radian_steradian" (parent := "iso80000_part3_collision") (lean := "PropertyKindCalculus.Iso80000.Part3.radian_steradian_not_commensurable") (tags := "proved") (effort := "small")
*A radian is not a steradian, though both are dimension one.* The SI units of plane and
solid angle are not commensurable, because their kinds differ — a type-level fact the
dimension cannot see. This is exactly the separation the angle-reform literature seeks to
install _in the dimension layer_ — Leonard
{Manual.citep leonard_dimensionally_consistent_treatment_of_angle_and_solid_angle}[]
would give angle its own dimension and make solid angle its square. PKC secures it _at the
kind layer_ — so it holds whether or not the SI ever assigns angle a dimension — and,
having made PhysLib's `Dimension` parametric in its basis, now realizes the reform itself
in an angle-augmented basis where plane angle is a base dimension and solid angle its
square.
The hertz and the radian-per-second are separated the same way (both `T⁻¹`). Uses
{uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part3_radian_steradian"
`radian_steradian_not_commensurable : ¬ radian.Commensurable steradian` by unfolding to
the underlying kinds and `decide`; `hertz_radianPerSecond_not_commensurable` is the
`T⁻¹` companion.
:::

:::theorem "thm_part3_dim_collision" (parent := "iso80000_part3_collision") (lean := "PropertyKindCalculus.Iso80000.Part3.iso80000_3_dim_collision") (tags := "proved") (effort := "small")
*Dimension is not a classifier even away from dimension one.* Distinct ISO 80000-3 kinds
also share _dimensionful_ dimensions — frequency and angular frequency are both `T⁻¹`,
velocity and speed both `L·T⁻¹`. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part3_dim_collision"
`iso80000_3_dim_collision`, witnessed by `⟨frequency, angularFrequency, …⟩` with
`frequency_ne_angularFrequency` (a `decide`) and reflexivity; `velocity_ne_speed` is the
`L·T⁻¹` companion. Axiom-free.
:::

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
A _prefixed unit_ is a decimal (SI, §1.19) or binary (IEC 80000-13) prefix applied to a
base {uses "def_metrologicalUnit"}[unit]. It projects to a metrological unit of the
_same kind_ with the prefix symbol prepended (`"c"` ++ `"m"` = `"cm"`), and exposes its
§1.22 conversion factor as the exponent and its §1.20/§1.21 status as a multiple or
submultiple.
:::

:::proof "def_prefixed_unit"
Realized as `structure SIPrefix` (`name`, `symbol`, `exponent : Int`) with the full
§1.19 table (and a sibling `BinaryPrefix` for IEC 80000-13), and `structure
PrefixedUnit` (`radix`, `exponent`, `symbol`, `base`) with `toUnit` (the projection),
`conversionExponent`, `IsMultiple`, and `IsSubmultiple`. Recording the resolved `radix`
lets both prefix families share one prefixed unit; the projection preserves the kind, so
`toUnit_wellFormed` and `commensurable_base` follow by reflexivity.
:::

:::theorem "thm_part3_centimetre_conversion" (parent := "iso80000_part3_prefix") (lean := "PropertyKindCalculus.Iso80000.Part3.centimetre_conversionExponent") (tags := "proved") (effort := "small")
*The centimetre is the _centi_ submultiple of the metre, factor `10⁻²`.* Its symbol
`"cm"` and its conversion exponent `-2` are checked computations from the prefix and the
base, and it stays commensurable with the metre. Uses
{uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part3_centimetre_conversion"
`centimetre` is `(metre.withPrefix SIPrefix.centi).toUnit`. The facts `centimetre_symbol
= "cm"`, `centimetre_conversionExponent = -2`, `centimetre_isSubmultiple`, and
`centimetre_wellFormed` are discharged by `rfl` / `decide`;
`metre_centimetre_commensurable` holds because the prefix leaves the kind unchanged.
:::

# Capturing a Remark's mathematics: the surface element of an area (item 3-3)

Each ISO 80000 item carries a _Remarks_ field, and those remarks often hold the
quantity's defining mathematics. Item 3-3 (area) is the example: its remark gives the
_surface element_ of a surface in terms of the Gaussian coordinates `u`, `v` and the
determinant `g` of the metric tensor (ISO 80000-2). Rather than transcribe the licensed
text or reduce it to a dimensional annotation, this work _formalizes the relation_ — as
real differential-geometric objects with proved properties — so the mathematics behind
the kind is itself checked.

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
The _surface element_ `dA = √g` is the area-element density at a point, and the _area_ of
a surface patch is its integral over the parameter region (`A = ∬ √g du dv`). Uses
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
*A flat patch recovers its Euclidean area.* For a surface lying in the plane the element
equals `|det A|`, the change-of-variables area density of the parametrization — so the
`√g` reading computes the _actual_ area. This is the correctness anchor that pins the
convention the prose remark leaves implicit.
:::

:::proof "thm_area_element_flat"
`areaElement_eq_abs_det : areaElement t = |(Matrix.of fun i j => t j i).det|`, via
`gram_eq_conjTranspose_mul` (so `g = (det A)²`) and `Real.sqrt_sq_eq_abs`.
:::

:::theorem "thm_area_element_regular" (parent := "iso80000_part3_area") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaElement.areaElement_pos_iff") (tags := "proved") (effort := "small")
*Regularity.* The element is strictly positive exactly when the two tangent vectors are
linearly independent — a non-degenerate (regular) point. A vanishing element marks a
degenerate parametrization.
:::

:::proof "thm_area_element_regular"
`areaElement_pos_iff : 0 < areaElement t ↔ LinearIndependent ℝ t`, from `Real.sqrt_pos`
and `det_gram_ne_zero_iff_linearIndependent`.
:::

# The volume element of a region (item 3-4)

The volume item carries the analogous remark — the _volume element_ `dV = √g` for the
`3 × 3` metric tensor of a three-parameter region. It is the three-dimensional analogue
of the area construction, the same Gram-determinant raised one rank, and it is
formalized the same way.

:::group "iso80000_part3_volume"
The metric tensor of a region is the `3 × 3` Gram matrix of its three tangent vectors;
its determinant is `g`; the volume element is `dV = √g`, and the volume is its integral.
The kind is the catalogued {uses "def_quantity"}[quantity]-kind volume, dimension `L³`.
:::

:::definition "def_volume_element" (parent := "iso80000_part3_volume") (lean := "PropertyKindCalculus.Iso80000.Part3.VolumeElement.volumeElement")
The _volume element_ `dV = √g` is the volume-element density of a three-parameter region,
and the _volume_ is its integral over the parameter region (`V = ∭ √g du dv dw`). It
squares back to `g`, is positive exactly at regular points, and (the correctness anchor)
equals `|det A|` for a flat region — so it integrates to the actual Euclidean volume.
:::

:::proof "def_volume_element"
`volumeElement t := Real.sqrt (metricDet t)` over the `3 × 3` `metricTensor t :=
Matrix.gram ℝ t` for `t : Fin 3 → E`; `regionVolume t s := ∫ x in s, volumeElement (t
x)` with `regionVolume_const` the constant-frame case. The proofs mirror `AreaElement`
at one higher rank.
:::

:::theorem "thm_volume_element_flat" (parent := "iso80000_part3_volume") (lean := "PropertyKindCalculus.Iso80000.Part3.VolumeElement.volumeElement_eq_abs_det") (tags := "proved") (effort := "medium")
*A flat region recovers its Euclidean volume.* For a region in Euclidean 3-space the
element equals `|det A|`, the change-of-variables volume density — the three-dimensional
correctness anchor, confirming the `√g` reading against the volume it must reproduce.
:::

:::proof "thm_volume_element_flat"
`volumeElement_eq_abs_det : volumeElement t = |(Matrix.of fun i j => t j i).det|` for
`t : Fin 3 → EuclideanSpace ℝ (Fin 3)`, via `gram_eq_conjTranspose_mul` and
`Real.sqrt_sq_eq_abs`. The companion `volumeElement_sq` gives `(dV)² = g`.
:::

# The algebraic Remarks as kind-laws

Many Part-3 remarks state a quantity's defining relation _algebraically_ — as a
quotient or a reciprocal of other quantities. Curvature is `1/ρ` (item 3-2); repetency
is `1/λ` (3-20); frequency is `1/T` (3-17.1); speed is `ds/dt`, path length per duration
(3-10.2); a plane angle is `s/r`, arc length per radius (3-5). Each is formalized as an
R12 kind-law over the catalogued kinds, using the quotient and reciprocal families.

:::group "iso80000_part3_relations"
The {uses "def_quotient_kind"}[quotient] and {uses "def_reciprocal_kind"}[reciprocal]
families generalize the {uses "def_product_kind"}[product] kind-law. Two payoffs on the
standard's own remarks: the _dimension follows from the relation_ as a checked
computation, and a verified-by-construction quantity carries its classification
certificate, instantiable at the quantity level.
:::

:::theorem "thm_part3_plane_angle_dimensionless" (parent := "iso80000_part3_relations") (lean := "PropertyKindCalculus.Iso80000.Part3.DefiningRelations.planeAngle_dim_from_arc_over_radius") (tags := "proved") (effort := "small")
*Under the SI's `α = s/r`, a plane angle computes to dimension one.* Taking arc and
radius as plain lengths, the remark `α = s/r` cancels the dimension — a checked
computation that reproduces the _current SI convention_, not one that settles it. That
the relation _forces_ dimensionlessness is exactly what the metrology reform disputes:
Quincey, Mohr and Phillips {Manual.citep quincey_angles_neither_length_ratios_nor_dimensionless}[]
argue an angle is inherently _neither_ a length ratio _nor_ dimensionless. PKC
formalizes the standard as published and leaves the dimensional stance open — plane
angle remains a distinct kind from every other dimension-one quantity (the collision
capstone above), which is what keeps the radian and steradian apart whatever dimension
the SI assigns. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part3_plane_angle_dimensionless"
`planeAngle_dim_from_arc_over_radius : planeAngle.dim = pathLength.dim / radius.dim`, by
reducing both sides to `Dim.length / Dim.length` and the lemma `length_div_length`
(`a / a = 1`, by `ext` and `simp`).
:::

:::theorem "thm_part3_frequency_reciprocal" (parent := "iso80000_part3_relations") (lean := "PropertyKindCalculus.Iso80000.Part3.DefiningRelations.frequencyOf_isReciprocal") (tags := "proved") (effort := "small")
*Verified construction at the quantity level.* A frequency built as the reciprocal of a
period duration carries its classification certificate by construction, over the `ℝ`
carrier — and canonicity makes that certificate determine the quantity. Uses
{uses "def_reciprocal_kind"}[the reciprocal kind-law].
:::

:::proof "thm_part3_frequency_reciprocal"
`frequencyOf T := Quantity.recip frequency_recip_periodDuration T`, and
`frequencyOf_isReciprocal` is `rfl`; `frequency_certificate_canonical` is
`eq_recip_of_isReciprocal`. The kind-law `frequency_recip_periodDuration` is `⟨rfl,
rfl⟩` (both kinds ratio-scale). The same families give `speedOf` (speed = path length /
duration) and `planeAngleOf` (plane angle = arc / radius).
:::

# Why it matters: classification and metrological consistency at the quantity level

Formalizing a remark's mathematics is not decoration. It earns its keep by turning the
quantity-kind into a working _classifier_ and by moving metrological checking down to
the _quantity level_, where the type system enforces it.

_Classifying quantities._ The surface-area formula does not return a bare real number:
its output is, by construction, a magnitude of the _one_ catalogued kind area. Any
quantity a downstream model computes this way — the area of a field, a footprint, a
cross-section — is automatically _classified_ as the same kind, dimension `L²`, unit the
square metre. The kind is the genus under which every such quantity falls, and the
defining relation is what places it there. So formalizing the remark gives users a
principled answer to "what _is_ this quantity?" — it is a value of area, because the
relation that produced it is area's defining relation.

_Verifying metrological consistency._ Because the kind carries its dimension and its own
scalar unit, the consistency checks happen at the quantity level and cannot be skipped.
Two areas combine — addition is defined on the area carrier — but an area and a length
are _different types_, so adding them does not type-check: the dimensionless numeric
conflation a spreadsheet would silently allow is rejected. An area is not measurable in
metres, because the square metre and the metre are not commensurable, a fact of the
types rather than a runtime guard. And the dimensional invariant `L²` travels with
_every_ value of the kind. The remark's mathematics, the kind, and these consistency
guarantees are thus one chain: the relation anchors the kind, the kind classifies the
quantity, and the classification _is_ the metrological check.

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
*A rectangle's area is verified-classified by construction.* `rectangleArea w h` is built
as the product of two lengths (area = length · length), so its area-classification
certificate holds by construction.
:::

:::proof "thm_rectangle_area_isproduct"
`rectangleArea w h := Quantity.mul area_is_length_times_length w h`, and
`rectangleArea_isProduct` is `rfl` — the certificate of the constructed product.
:::

:::theorem "thm_certified_area_nonneg" (parent := "iso80000_part3_classified") (lean := "PropertyKindCalculus.Iso80000.Part3.AreaClassification.certified_surfaceArea_nonneg") (tags := "proved") (effort := "medium")
*Property transport.* Every certified surface area is non-negative — the surface element
is `≥ 0` (a property of area's defining relation), instantiated at the quantity level
through the certificate.
:::

:::proof "thm_certified_area_nonneg"
`certified_surfaceArea_nonneg` rewrites the certificate `q.magnitude = surfaceArea t s`
and applies `surfaceArea_nonneg` (the integral of a non-negative element, by
`setIntegral_nonneg` and `areaElement_nonneg`).
:::

# Item index — ISO 80000-3

Every catalogued item of ISO 80000-3, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it. Each item number links to the formalized result it participates in — the
length-family lattice, a dimension collision, a formalized remark, or the catalogue
itself. Symbols and unit strings are *citation locators*; nothing normative is reproduced.

:::iso_doc_table part3IndexTable
:::
