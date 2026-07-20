import Verso
import VersoManual
import VersoBlueprint
-- The Part-6 nodes link real declarations (dimensioned kinds over the electric-current
-- base axis, checked dimensional facts, the scale-type distinction, the AC-power
-- specialization lattice, the power/resistance dimension collisions, and the
-- defining-relation kind-laws), so this chapter imports the Part-6 modules of the
-- `Iso80000` library (PhysLib-backed).
import PropertyKindCalculus.Iso80000.Part6
import PropertyKindCalculus.Iso80000.Part6.DefiningRelations
import PropertyKindCalculusBlueprint.ItemIndex

open Verso.Genre
open Verso.Genre.Manual
open Informal

open PropertyKindCalculusBlueprint.ItemIndex

/-- Default blueprint node for ISO/IEC 80000-6 item-index rows (editorial). -/
def part6Default : String := "def_part6_catalogued_kind"

/-- Per-item blueprint cross-reference overrides for the ISO/IEC 80000-6 item
index (editorial; items not listed link to `part6Default`). Every other column
is generated from `PropertyKindCalculus.Iso80000.Part6.catalogue`. -/
def part6Refs : List (String × String) := [
  ("6-1", "thm_part6_current_dim"),
  ("6-2.1", "thm_part6_current_dim"),
  ("6-2.2", "thm_part6_current_dim"),
  ("6-10", "thm_part6_ampere_volt"),
  ("6-11.1", "thm_part6_scale_collision"),
  ("6-11.2", "thm_part6_scale_collision"),
  ("6-11.3", "thm_part6_scale_collision"),
  ("6-11.4", "thm_part6_scale_collision"),
  ("6-13", "thm_part6_current_dim"),
  ("6-15", "thm_part6_dim_one"),
  ("6-16", "thm_part6_dim_one"),
  ("6-21", "thm_part6_current_dim"),
  ("6-22.1", "thm_part6_current_dim"),
  ("6-27", "thm_part6_dim_one"),
  ("6-28", "thm_part6_dim_one"),
  ("6-32", "thm_part6_current_dim"),
  ("6-36", "thm_part6_scale_collision"),
  ("6-38", "thm_part6_dim_one"),
  ("6-40", "thm_part6_ohm"),
  ("6-42.1", "thm_part6_dim_one"),
  ("6-42.2", "thm_part6_dim_one"),
  ("6-43", "thm_part6_ohm"),
  ("6-44", "thm_part6_ohm"),
  ("6-45", "thm_part6_power_factor"),
  ("6-46", "thm_part6_ohm"),
  ("6-47", "thm_part6_ohm"),
  ("6-48", "thm_part6_dim_one"),
  ("6-50", "thm_part6_ampere_volt"),
  ("6-51.1", "thm_part6_power_collision"),
  ("6-51.3", "thm_part6_power_collision"),
  ("6-51.4", "thm_part6_power_collision"),
  ("6-52.1", "thm_part6_ohm"),
  ("6-53", "thm_part6_dim_one"),
  ("6-54", "thm_part6_dim_one"),
  ("6-55", "thm_part6_dim_one"),
  ("6-56", "thm_part6_active_reactive"),
  ("6-57", "thm_part6_power_collision"),
  ("6-58", "thm_part6_power_factor"),
  ("6-59", "thm_part6_power_collision"),
  ("6-60", "thm_part6_active_reactive"),
  ("6-61", "thm_part6_power_collision")
]

/-- The ISO/IEC 80000-6 item index, generated live from the catalogue. -/
def part6IndexTable : DocTable :=
  standardIndex PropertyKindCalculus.Iso80000.Part6.catalogue part6Default part6Refs

#doc (Manual) "IEC 80000-6 — Electromagnetism" =>

The fourth part specified in full is IEC 80000-6, _Electromagnetism_ — the one
_IEC_-published part of the series. Every item — all of 6-1 … 6-62, including every
sub-suffixed item (6-2.1/6-2.2, 6-11.1 … 6-11.4, 6-14.1/6-14.2, 6-19.1/6-19.2,
6-22.1 … 6-22.4, 6-26.1/6-26.2, 6-35.1/6-35.2, 6-37.1 … 6-37.3, 6-41.1/6-41.2,
6-42.1/6-42.2, 6-51.1 … 6-51.5, 6-52.1 … 6-52.5) — is catalogued: electric current and
charge, the charge and current distributions, the electric field and potential, the
capacitances and permittivities, the magnetic field, flux, and potentials, the magnetic
circuit, conductivity and resistivity, impedance and admittance, and the AC power
quantities — each carrying its exact source as data: the part, the printed item
designation, the principal quantity symbol, and the coherent SI unit symbol. Only
_citation locators_ are recorded; no normative content (definitions, remarks) from the
licensed standard is reproduced. The defining _mathematics_ of selected remarks is
formalized in the sibling module `Part6.DefiningRelations`.

Electromagnetism brings the last SI base quantity the earlier parts did not exercise —
_electric current_ — and sharpens the two axes the calculus already pressed. The base
axis enters as the ampere; PhysLib's `Dimension` takes electric _charge_ `C` as its
generator, so electric current appears as `C·T⁻¹` (coulomb per second). The
_scale-type_ distinction recurs — electric potential is gauge-dependent, fixed only up
to an arbitrary additive reference, hence interval-scale, while electric potential
difference, of the very same dimension `V`, is ratio-scale (requirement _R6_). And the
AC power quantities give the sharpest _dimension does not classify_ case yet: active,
reactive, and apparent power are all `M·L²·T⁻³`, yet the standard spends _three_
different unit strings on that one dimension — the watt, the var, and the volt-ampere —
and arranges them as a specialization lattice over power (requirement _R2_).

# Quantity-kinds and units of IEC 80000-6

:::group "iso80000_part6"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, now over the charge generator `C` (with electric current as `C·T⁻¹`), so the
standard's dimensional facts — a capacitance is `C²·M⁻¹·L⁻²·T²`, a resistance
`M·L²·T⁻¹·C⁻²`, a magnetic flux `M·L²·T⁻¹·C⁻¹` — are _checked computations_ rather than
annotations. The kinds are dimensioned internally over this charge generator — so the checked
facts read in `C` (a capacitance's charge-exponent is `2`) — but the item-index tables _cite_
each dimension in the ISQ base quantity current via the change of basis `C = I·T`, so the
printed capacitance is `M⁻¹·L⁻²·T⁴·I²` exactly as IEC 80000-6 tabulates it. Each unit is a
{uses "def_metrologicalUnit"}[metrological unit] of its kind; commensurability is a type-level
fact, so an ampere and a volt are not interchangeable.
:::

:::definition "def_part6_catalogued_kind" (parent := "iso80000_part6") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "6-51.1"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with the
kind as data, so the source of each definition can be rendered or audited downstream
rather than kept in a comment.
:::

:::proof "def_part6_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `IEC 80000-6, Edition 2.0, 2022-11 item 6-51.1` (the one IEC-published part of the
catalogue). The `catalogue` lists all 85 items in item order — electric current (6-1),
electric charge (6-2.1), magnetic flux (6-22.1), the impedance family (6-51.1 … 6-51.5),
the AC power quantities (6-56 … 6-61), active energy (6-62), … — each paired with its
coherent SI unit symbol.
:::

:::theorem "thm_part6_current_dim" (parent := "iso80000_part6") (lean := "PropertyKindCalculus.Iso80000.Part6.capacitance_dim_charge") (tags := "proved") (effort := "small")
*A capacitance carries the charge generator squared (item 6-13).* The catalogued
capacitance kind has charge-exponent two in PhysLib's dimension group — the farad's
`C²·M⁻¹·L⁻²·T²` reproduced as a checked computation over the new electric-current base
axis, not an annotation. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part6_current_dim"
Proved as `capacitance_dim_charge : capacitance.dim.charge = 2` in the `Iso80000`
library, discharged by `norm_num` over the PhysLib dimension lemmas for the charge
generator. The companions `electricCurrent_dim_charge = 1` and `electricCurrent_dim_time
= -1` (item 6-1, the ampere as `C·T⁻¹`), `resistance_dim_charge = -2` (item 6-46, the
ohm), and `magneticFlux_dim_charge = -1` (item 6-22.1, the weber) record the rest of the
electromagnetic algebra.
:::

:::theorem "thm_part6_ampere_volt" (parent := "iso80000_part6") (lean := "PropertyKindCalculus.Iso80000.Part6.ampere_voltPotential_not_commensurable") (tags := "proved") (effort := "small")
*An ampere and a volt are not commensurable.* Electric current and electric potential are
distinct kinds, so their units cannot be compared by ratio — a type-level fact, not a
runtime check. Uses {uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part6_ampere_volt"
Proved as `ampere_voltPotential_not_commensurable : ¬ ampere.Commensurable voltPotential`
by unfolding `Commensurable` to the underlying kinds and `decide`. The ampere and the ohm
are each `WellFormed` (electric current and resistance are ratio-scale).
:::

# Electric potential: one dimension, two scales

IEC 80000-6 lists _electric potential_ (6-11.1) and _electric potential difference_
(6-11.2) as separate items of the _same_ dimension `V`. But they are not the same kind of
quantity. Electric potential is fixed only up to an arbitrary additive reference — the
choice of where "zero potential" sits (the ground, infinity) is a gauge, so the standard
notes the potential "is not unique". Only its _differences_ are physically meaningful, so
it is _interval-scale_: a ratio of two electric potentials is not a defined operation.
Electric potential difference is a genuine difference, so it is _ratio-scale_. A
dimension-only model sees one type, "a real number of volts", for both.

This is requirement _R6_ — the scale type fixes which operations are even _defined_ —
recurring on electromagnetism exactly as it appeared on thermodynamics. The
gauge-dependent electric potential is electromagnetism's Celsius temperature: same
dimension as its companion, separated from it _neither_ by dimension _nor_ by an
examination principle, but by _scale type_ alone.

:::group "iso80000_part6_scale"
The volt of electric potential and the volt of electric potential difference are _both_
well-formed {uses "def_metrologicalUnit"}[metrological units] — a kind bears a unit from
the differential (interval) scale upward, not only from ratio scale, so the
gauge-dependent potential still bears the volt even though `×`,`÷` are undefined on it.
What separates the two kinds is the {uses "def_scaleType"}[scale type]: interval versus
ratio — and so the two volts, the same string over the same dimension, are not
commensurable.
:::

:::theorem "thm_part6_potential_scale" (parent := "iso80000_part6_scale") (lean := "PropertyKindCalculus.Iso80000.Part6.electricPotential_not_allowsRatio") (tags := "proved") (effort := "small")
*Electric potential does not admit `×`,`÷`.* It is interval-scale (gauge freedom — fixed
only up to an arbitrary additive reference), so a ratio of electric potentials is not a
meaningful operation — the scale layer refuses it where the dimension would not. Electric
potential difference, being ratio-scale, does admit it. Uses {uses "def_scaleType"}[the
scale type].
:::

:::proof "thm_part6_potential_scale"
`electricPotential_not_allowsRatio : ¬ ScaleType.AllowsRatio electricPotential.kind.scale`,
with the companion `electricPotentialDifference_allowsRatio` for the ratio case. The volt
of electric potential is nonetheless `WellFormed` (`voltPotential_wellFormed`, via the
differential scale), and `voltPotential_voltDifference_not_commensurable` records that the
two volts — same symbol, same dimension — are not commensurable, because the kinds differ
in scale.
:::

:::theorem "thm_part6_scale_collision" (parent := "iso80000_part6_scale") (lean := "PropertyKindCalculus.Iso80000.Part6.iec80000_6_scale_collision") (tags := "proved") (effort := "small")
*The scale disambiguation, on the standard.* There exist distinct IEC 80000-6 kinds with
the same dimension `V` that are separated by scale type alone — electric potential
(interval, gauge-dependent) and electric potential difference (ratio) witness it. Neither
the dimension nor an examination principle tells them apart; the scale layer does. This is
requirement R6 on the standard, the electromagnetic counterpart of thermodynamic versus
Celsius temperature. Uses {uses "def_scaleType"}[the scale type].
:::

:::proof "thm_part6_scale_collision"
`iec80000_6_scale_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
a.kind.scale ≠ b.kind.scale`, witnessed by `⟨electricPotential, electricPotentialDifference,
…⟩` with reflexivity on the dimension and a `decide` on the differing scales. Axiom-free.
:::

# The AC power family: distinguishing kinds by defining construction

IEC 80000-6 lists _power_ (6-45) as a genus and the AC power quantities — active power
(6-56), apparent power (6-57), complex power (6-59), reactive power (6-60), and non-active
power (6-61) — as items of one dimension `M·L²·T⁻³`. The standard distinguishes them by
_which component of the periodic process each isolates_: active power is the time-averaged
real (resistive) component; reactive power the imaginary part of the complex power;
apparent power the product of RMS voltage and current; and so on. Tellingly, it spends
_three different unit strings_ on this single dimension — the watt for active power, the
var for reactive power, the volt-ampere for apparent power — precisely to keep the kinds
apart in print. A dimension-only model sees one type, "a real number of watts", for all
of them.

This is requirement _R2_ again, now on the AC power quantities — the pattern Part 3 set on
the length family, Part 4 on the force family, and Part 5 on the thermodynamic potentials.
Item 6-45 is the broad genus; each AC quantity is a _species_ of power, distinguished *not
by fiat* but by an explicit defining construction (Dybkær's examination principle, §7.5).
The species are then provably distinct kinds while remaining _mutually comparable_ as
powers — comparable enough to combine into the complex power `P + jQ`.

:::group "iso80000_part6_power"
The power species are individuated by an {uses "def_examination"}[examination principle] —
here which component of the periodic process the quantity isolates — and arranged as a
{uses "def_specializes"}[specialization] lattice over the general power kind. The sharpest
case is active versus reactive power: both "powers" of the same dimension, they are
nonetheless different kinds — and the calculus proves it from their differing defining
constructions, not from a naming convention, while the standard itself separates their
units, `W` from `var`.
:::

:::definition "def_part6_power_species" (parent := "iso80000_part6_power") (lean := "PropertyKindCalculus.Iso80000.Part6.powerSpecies")
A _power species_ is a ratio-scale {uses "def_quantity"}[quantity]-kind of dimension
`M·L²·T⁻³` carrying an {uses "def_examination"}[examination principle] — this work's own
terse descriptor of the defining construction that distinguishes it (the time-averaged
real part, the RMS product, the complex sum `P + jQ`, the imaginary part, the residual
`√(S² − P²)`), never the standard's normative definition. Active, apparent, complex,
reactive, and non-active power are all species of the general power kind (item 6-45).
:::

:::proof "def_part6_power_species"
`powerSpecies id p := { kind := { id, scale := .ratio, examPrinciple := some p.id },
dim := EDim.power }`. The general `power` carries no examination principle; the
direct-parent edges of the family are collected in an `Edge` relation, each species an edge
to `power` (mirroring the standard's listing of the AC quantities beneath power).
:::

:::theorem "thm_part6_active_reactive" (parent := "iso80000_part6_power") (lean := "PropertyKindCalculus.Iso80000.Part6.activePower_ne_reactivePower") (tags := "proved") (effort := "small")
*Active and reactive power are distinct kinds — by defining construction, not by fiat.*
They share dimension `M·L²·T⁻³` and are both "powers", yet are different kinds _because
they isolate different components of the periodic process_ (the time-averaged real part vs
the imaginary part of the complex power), proved through `distinct_of_examPrinciple` (§7.5).
This is the AC-power analogue of width ≠ distance, static ≠ kinetic friction force, and
Helmholtz ≠ Gibbs energy. Uses {uses "def_examination"}[the examination principle].
:::

:::proof "thm_part6_active_reactive"
`activePower_ne_reactivePower : activePower.kind ≠ reactivePower.kind`, from
`KindOfProperty.distinct_of_examPrinciple` applied to the differing principles
`time-averaged-real` and `reactive-imaginary` (a `decide` on the `Option String` links).
The companion `apparentPower_ne_complexPower` separates two further species, and
`activePower_examinedBy` checks the kind-to-principle link. Axiom-free.
:::

:::theorem "thm_part6_power_comparable" (parent := "iso80000_part6_power") (lean := "PropertyKindCalculus.Iso80000.Part6.activePower_reactivePower_comparable") (tags := "proved") (effort := "small")
*Comparability is preserved.* Active and reactive power, though distinct kinds, remain
_mutually comparable_ — they share the super-kind power, so combining them (into the
complex power) is possible but only via an explicit up-cast, never silently. The companion
`activePower_specializes_power` records that active power specializes power. Uses
{uses "def_specializes"}[specialization].
:::

:::proof "thm_part6_power_comparable"
`activePower_reactivePower_comparable : MutuallyComparable Edge activePower.kind
reactivePower.kind`, with witness `power.kind`, each species reaching it by one edge.
Axiom-free.
:::

# Dimension does not classify; the kind does — the power and impedance cases

Part 6 holds the sharpest dimension collision in the series so far. _Active power_ (6-56),
_reactive power_ (6-60), and _apparent power_ (6-57) are _all_ `M·L²·T⁻³`, yet they are
distinct kinds — and the collision is sharper than Part 5's joule-per-kelvin, because there
even the unit string agreed, while here the standard itself spends three strings (`W`,
`var`, `VA`) on the one dimension. _Resistance_ (6-46) and _reactance_ (6-51.4) collide the
same way at the ohm — the real and imaginary parts of an impedance — and the relative
permittivity (6-15), relative permeability (6-27), the susceptibilities, the coupling and
leakage factors, and the quality, loss, and power factors fill out the dimension-one family.

:::group "iso80000_part6_collision"
These are the dimension-disambiguation capstone, on _standard_ quantities: the
{uses "def_dim"}[dimension map] identifies the members of each pair, while the kind layer
keeps them apart, both as kinds and as {uses "def_metrologicalUnit"}[units] — here even
where the standard spends a different unit string on each kind of one dimension.
:::

:::theorem "thm_part6_power_collision" (parent := "iso80000_part6_collision") (lean := "PropertyKindCalculus.Iso80000.Part6.iec80000_6_dim_collision") (tags := "proved") (effort := "small")
*Active power is not reactive power, though both are `M·L²·T⁻³`.* There exist distinct
IEC 80000-6 kinds with the same dimension — active and reactive power witness it, alongside
apparent, complex, and non-active power. No dimension-only type system can separate them;
the kind layer does. This is the electromagnetic case that a dimension does not classify a
quantity, sharper than Part 5's. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part6_power_collision"
`iec80000_6_dim_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim`,
witnessed by `⟨activePower, reactivePower, …⟩` with `activePower_ne_reactivePower` and
reflexivity. The companion `resistance_ne_reactance` is the ohm case (real vs imaginary
part of an impedance). Axiom-free.
:::

:::theorem "thm_part6_watt_var" (parent := "iso80000_part6_collision") (lean := "PropertyKindCalculus.Iso80000.Part6.wattActive_varReactive_not_commensurable") (tags := "proved") (effort := "small")
*The active-power watt is not the reactive-power var.* The units of active and reactive
power carry the same dimension `M·L²·T⁻³`, yet are not commensurable — and the standard
keeps them apart not only by kind but by _string_, `W` versus `var`, a sharper form of the
rule that neither a dimension nor a unit string determines a kind. Uses
{uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part6_watt_var"
`wattActive_varReactive_not_commensurable : ¬ wattActive.Commensurable varReactive` by
unfolding to the underlying kinds and `decide` (active power's kind differs from the
reactive-power kind; the units are written "W" and "var").
:::

:::theorem "thm_part6_dim_one" (parent := "iso80000_part6_collision") (lean := "PropertyKindCalculus.Iso80000.Part6.iec80000_6_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard.* There exist distinct IEC 80000-6 kinds
with the same dimension one — relative permittivity and relative permeability witness it,
alongside the susceptibilities, the coupling and leakage factors, and the quality, loss,
and power factors. Dimension cannot separate them; the kind layer does. Uses
{uses "def_dim"}[the dimension map].
:::

:::proof "thm_part6_dim_one"
`iec80000_6_dim_one_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
a.dim = 1`, witnessed by `⟨relativePermittivity, relativePermeability, …⟩` with
`relativePermittivity_ne_relativePermeability` (a `decide`) and reflexivity. Axiom-free.
:::

# The algebraic Remarks as kind-laws: electromagnetism built by the kind algebra

Many Part-6 definitions state a quantity's defining relation _algebraically_ — the
constitutive laws of circuit theory. Resistance is voltage per current (Ohm's law, 6-46);
conductance is `1/R` (6-47); capacitance is charge per voltage (6-13); power is voltage
times current (6-45); resistivity is `1/σ` (6-44); admittance is `1/Z` (6-52.1); permeance
is `1/Rₘ` (6-40); the power factor is active over apparent power (6-58). Electric current
itself is charge per time (6-1), crossing to ISO 80000-3 for its time factor. Each is
formalized as an R12 kind-law over the catalogued kinds.

:::group "iso80000_part6_relations"
The {uses "def_product_kind"}[product], {uses "def_quotient_kind"}[quotient], and
{uses "def_reciprocal_kind"}[reciprocal] families carry the kind-laws. Three payoffs on the
standard's own definitions: the constitutive structure of circuit theory is made explicit;
the _dimension follows from the relation_ as a checked computation; and a
verified-by-construction quantity carries its classification certificate.
:::

:::theorem "thm_part6_ohm" (parent := "iso80000_part6_relations") (lean := "PropertyKindCalculus.Iso80000.Part6.DefiningRelations.resistanceOf_isQuotient") (tags := "proved") (effort := "small")
*Resistance is voltage / current — a verified construction (Ohm's law).* A resistance built
as the quotient of a voltage by an electric current carries its quotient certificate by
construction, over the `ℝ` carrier, and canonicity makes the certificate determine the
quantity. Uses {uses "def_quotient_kind"}[the quotient kind-law].
:::

:::proof "thm_part6_ohm"
`resistanceOf u i := Quantity.div resistance_quot_voltage_current u i`, and
`resistanceOf_isQuotient` is `rfl`; `resistance_certificate_canonical` is
`eq_div_of_isQuotient`. The kind-law `resistance_quot_voltage_current : QuotientKind
voltage.kind electricCurrent.kind resistance.kind` is `⟨rfl, rfl, rfl⟩`, and
`resistance_dim_from_voltage_current` checks `M·L²·T⁻¹·C⁻²` follows from the relation. The
same families give `powerOf` (= voltage × current, a `ProductKind`), `conductanceOf` (=
`1/R`), and the cross-part `electricCurrent_quot_charge_duration` (= charge / time, the time
crossing to ISO 80000-3).
:::

:::theorem "thm_part6_power_factor" (parent := "iso80000_part6_relations") (lean := "PropertyKindCalculus.Iso80000.Part6.DefiningRelations.powerFactor_dim_from_powers") (tags := "proved") (effort := "small")
*The power factor is dimension one because it is a ratio of two powers.* From the relation
`λ = P/S`, the powers cancel and the dimension is _computed_ to be one — not stipulated, the
electromagnetic analogue of the plane angle being a ratio of two lengths and the
thermodynamic efficiency a ratio of two powers. Yet the power factor remains a distinct kind
from every other dimension-one quantity (the collision capstone above). Uses
{uses "def_dim"}[the dimension map].
:::

:::proof "thm_part6_power_factor"
`powerFactor_dim_from_powers : powerFactor.dim = activePower.dim / apparentPower.dim`, by
reducing both sides via `div_self` (`a / a = 1`). The kind-law
`powerFactor_quot_active_apparent` is `⟨rfl, rfl, rfl⟩`. The companion
`power_dim_from_voltage_current` checks `M·L²·T⁻³` follows from `P = U·I` (the charge
generator cancelling between voltage and current).
:::

# Item index — IEC 80000-6

Every catalogued item of IEC 80000-6, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it (over the charge generator `C`). Each item number links to the formalized
result it participates in — the scale-type distinction, the AC-power lattice, a dimension
collision, a defining relation, or the catalogue itself. Symbols and unit strings are
*citation locators*; nothing normative is reproduced.

:::iso_doc_table part6IndexTable
:::
