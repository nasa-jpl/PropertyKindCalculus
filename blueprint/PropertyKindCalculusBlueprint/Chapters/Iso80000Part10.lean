import Verso
import VersoManual
import VersoBlueprint
-- The Part-10 nodes link real declarations (the atomic/nuclear dimensioned kinds, the
-- gray/sievert collision, the becquerel collision, the dimension-one family, and the
-- defining-relation kind-laws), so this chapter imports the Part-10 modules of the
-- `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part10
import PropertyKindCalculus.Iso80000.Part10.DefiningRelations
import PropertyKindCalculusBlueprint.ItemIndex

open Verso.Genre
open Verso.Genre.Manual
open Informal

open PropertyKindCalculusBlueprint.ItemIndex

/-- Default blueprint node for ISO/IEC 80000-10 item-index rows (editorial). -/
def part10Default : String := "def_part10_catalogued_kind"

/-- Per-item blueprint cross-reference overrides for the ISO/IEC 80000-10 item
index (editorial; items not listed link to `part10Default`). Every other column
is generated from `PropertyKindCalculus.Iso80000.Part10.catalogue`. -/
def part10Refs : List (String × String) := [
  ("10-1.1", "thm_part10_dim_one"),
  ("10-1.2", "thm_part10_dim_one"),
  ("10-1.3", "thm_part10_dim_one"),
  ("10-5.2", "thm_part10_dim_one"),
  ("10-13.1", "thm_part10_dim_one"),
  ("10-13.2", "thm_part10_dim_one"),
  ("10-13.3", "thm_part10_dim_one"),
  ("10-13.4", "thm_part10_dim_one"),
  ("10-13.5", "thm_part10_dim_one"),
  ("10-13.6", "thm_part10_dim_one"),
  ("10-13.7", "thm_part10_dim_one"),
  ("10-13.8", "thm_part10_dim_one"),
  ("10-14.1", "thm_part10_dim_one"),
  ("10-14.2", "thm_part10_dim_one"),
  ("10-15.1", "thm_part10_becquerel"),
  ("10-15.2", "thm_part10_becquerel"),
  ("10-15.3", "thm_part10_becquerel"),
  ("10-16", "thm_part10_becquerel"),
  ("10-22.1", "thm_part10_dim_one"),
  ("10-22.2", "thm_part10_dim_one"),
  ("10-23.1", "thm_part10_dim_one"),
  ("10-23.2", "thm_part10_dim_one"),
  ("10-24", "thm_part10_becquerel"),
  ("10-25", "thm_part10_relations"),
  ("10-27", "thm_part10_becquerel"),
  ("10-28", "thm_part10_relations"),
  ("10-35", "thm_part10_dim_one"),
  ("10-36", "thm_part10_becquerel"),
  ("10-50", "thm_part10_relations"),
  ("10-59", "thm_part10_dim_one"),
  ("10-68", "thm_part10_dim_one"),
  ("10-69", "thm_part10_dim_one"),
  ("10-70", "thm_part10_dim_one"),
  ("10-74.1", "thm_part10_dim_one"),
  ("10-74.2", "thm_part10_dim_one"),
  ("10-75", "thm_part10_dim_one"),
  ("10-76", "thm_part10_dim_one"),
  ("10-77", "thm_part10_dim_one"),
  ("10-78.1", "thm_part10_dim_one"),
  ("10-78.2", "thm_part10_dim_one"),
  ("10-81.1", "thm_part10_collision"),
  ("10-81.2", "thm_part10_collision"),
  ("10-82", "thm_part10_dim_one"),
  ("10-83.1", "thm_part10_collision"),
  ("10-84", "thm_part10_relations"),
  ("10-86.1", "thm_part10_collision"),
  ("10-87", "thm_part10_relations")
]

/-- The ISO/IEC 80000-10 item index, generated live from the catalogue. -/
def part10IndexTable : DocTable :=
  standardIndex PropertyKindCalculus.Iso80000.Part10.catalogue part10Default part10Refs

#doc (Manual) "ISO 80000-10 — Atomic and nuclear physics" =>

The eighth part specified in full is ISO 80000-10, _Atomic and nuclear physics_. Every
item — all of 10-1.1 … 10-89, one hundred and twenty-five including every sub-suffixed
item — is catalogued: the nucleon numbers and masses, the atomic constants and magnetic
moments, the quantum numbers, the precession frequencies, the decay and activity
quantities, the cross sections, the fluences, the attenuation and stopping powers, the
transport-in-matter and reactor quantities, and the dosimetry family — each carrying its
exact source as data. Only _citation locators_ are recorded; no normative content from the
licensed standard is reproduced. The defining _mathematics_ of selected remarks is
specified in the sibling module `Part10.DefiningRelations`.

Atomic and nuclear physics holds the series' clearest external confirmation of the
_dimension does not classify the kind_ thesis — the standard itself coins _two unit names
for one dimension_. The absorbed dose, specific energy imparted, and kerma (all the gray)
and the dose equivalent (the sievert) all carry dimension `L²·T⁻²` (energy per mass), and
the standard separates them by unit name _because the kinds differ_: the gray for the
physical doses, the sievert for the biologically-weighted one. This is the
entropy-versus-heat-capacity `J/K` collision of ISO 80000-5, made sharper. A second case
is the becquerel, the special name SI reserves for `s⁻¹` _as the unit of activity_, a kind
the dimension cannot tell from the decay constant.

# Quantity-kinds and units of ISO 80000-10

:::group "iso80000_part10"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, here over mass, length, time, and charge (the steradian and the mole are
dimension one). The standard's dimensional facts — an absorbed dose is `L²·T⁻²` with
mass-exponent zero, an activity `T⁻¹`, a cross section an area — are _checked computations_.
Each unit is a {uses "def_metrologicalUnit"}[metrological unit] of its kind;
commensurability is a type-level fact, so the gray and the sievert are not interchangeable
though they share one dimension.
:::

:::definition "def_part10_catalogued_kind" (parent := "iso80000_part10") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "10-81.1"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with the
kind as data, so the source of each definition can be rendered or audited downstream.
:::

:::proof "def_part10_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `ISO 80000-10, Second edition, 2019-08 item 10-81.1`. The `catalogue` lists all 125
items in item order — the nucleon numbers (10-1.1 … 10-1.3), the activity (10-27), the
cross sections (10-38.1 … 10-42.2), the dosimetry family (10-80.1 … 10-89), … — each
paired with its coherent SI unit symbol.
:::

# The gray/sievert collision — the standard's own `J/kg` disambiguation

Four quantities of ISO 80000-10 carry the dimension `L²·T⁻²` (energy per mass): the
absorbed dose (10-81.1), the specific energy imparted (10-81.2), the kerma (10-86.1) — all
in _grays_ — and the dose equivalent (10-83.1) — in _sieverts_. The gray and the sievert
are the _same_ coherent unit, `J/kg`; the standard gives them different special names
_precisely because the kinds differ_: the physical energy deposited per mass, versus that
energy weighted for biological effect.

This is requirement _R1_ (the dimension does not classify the kind) confirmed by the
standard's own hand. A dimension-only model sees one type, "a real number of joules per
kilogram", for absorbed dose and dose equivalent — and would let a gray be silently read as
a sievert, the exact error the two unit names exist to prevent. It is the
entropy-versus-heat-capacity `J/K` collision of ISO 80000-5, made sharper: here the
collision is between two _named_ units, not two uses of one.

:::group "iso80000_part10_collision"
The dimension-collision capstone, on _standard_ quantities: the {uses "def_dim"}[dimension
map] identifies absorbed dose with dose equivalent, while the kind layer keeps them apart,
both as kinds and as {uses "def_metrologicalUnit"}[units] (the gray and the sievert). The
becquerel collision (`T⁻¹`) is the companion.
:::

:::theorem "thm_part10_collision" (parent := "iso80000_part10_collision") (lean := "PropertyKindCalculus.Iso80000.Part10.iso80000_10_dim_collision") (tags := "capstone, proved") (effort := "small")
*Absorbed dose is not dose equivalent, though both are `J/kg` and `L²·T⁻²` (items 10-81.1,
10-83.1).* There exist distinct ISO 80000-10 kinds with the same dimension — absorbed dose
and dose equivalent witness it, alongside the specific energy imparted and the kerma. The
standard assigns two unit names (gray, sievert) to one dimension; no dimension-only type
system can separate them, the kind layer — and the unit — does. Uses {uses "def_dim"}[the
dimension map].
:::

:::proof "thm_part10_collision"
`iso80000_10_dim_collision`, witnessed by `⟨absorbedDose, doseEquivalent, …⟩`. The unit fact
`gray_sievert_not_commensurable` is a `decide`. Axiom-free.
:::

:::theorem "thm_part10_becquerel" (parent := "iso80000_part10_collision") (lean := "PropertyKindCalculus.Iso80000.Part10.becquerel_perSecond_not_commensurable") (tags := "proved") (effort := "small")
*The becquerel of activity and the reciprocal second of the decay constant are not
commensurable, though both are `T⁻¹` (items 10-27, 10-24).* The becquerel is the special
name SI reserves for `s⁻¹` as the unit of activity — a kind distinction the dimension
cannot see, shared also with the particle emission rate and the Larmor and cyclotron
frequencies. Uses {uses "def_metrologicalUnit"}[the metrological unit].
:::

:::proof "thm_part10_becquerel"
`becquerel_perSecond_not_commensurable`, by `decide` after unfolding
`MetrologicalUnit.Commensurable`. The underlying kind distinction is `activity_ne_decayConstant`,
and `activity_dim_eq_decayConstant_dim` records the shared dimension. Axiom-free.
:::

# The dimension-one family — the widest in the physical parts

ISO 80000-10 carries the largest dimension-one family of the physical parts: the atomic,
neutron, and nucleon numbers; the eight quantum numbers (10-13.1 … 10-13.8); the two
g-factors; the relative mass excess and defect; the packing and binding fractions; the
internal conversion and quality factors; the total ionization; and the reactor factors
(resonance escape, fast fission, thermal utilization, non-leakage, multiplication). All
share the dimension one; what tells them apart is the kind.

:::theorem "thm_part10_dim_one" (parent := "iso80000_part10_collision") (lean := "PropertyKindCalculus.Iso80000.Part10.iso80000_10_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard — the widest in the physical parts.* There
exist distinct ISO 80000-10 kinds with the same dimension one — the atomic and neutron
numbers witness it, alongside the quantum numbers, the g-factors, and the reactor factors.
Dimension cannot separate them; the kind layer does. Uses {uses "def_dim"}[the dimension
map].
:::

:::proof "thm_part10_dim_one"
`iso80000_10_dim_one_collision`, witnessed by `⟨atomicNumber, neutronNumber, …⟩` with the
kind distinction a `decide` and reflexivity. Axiom-free.
:::

# The algebraic Remarks as kind-laws: dosimetry built by the kind algebra

Several Part-10 definitions state a quantity's defining relation _algebraically_. Dose
equivalent is the _product_ of absorbed dose with the dimensionless quality factor (10-83.1,
`H = D·Q`); mean life is the _reciprocal_ of the decay constant (10-25, `τ = 1/λ`); specific
activity is activity per mass (10-28); the absorbed-dose rate is absorbed dose per time
(10-84); the mass attenuation coefficient is linear attenuation per mass density (10-50).
Each is specified as an R12 kind-law, several crossing to ISO 80000-3 and -4.

:::group "iso80000_part10_relations"
The product, {uses "def_quotient_kind"}[quotient], and reciprocal families carry the
kind-laws. Two payoffs: dosimetry is built from the other parts, and the gray/sievert
distinction holds under the algebra — dose equivalent keeps the dimension of absorbed dose
_because_ the quality factor is dimension one, a checked computation.
:::

:::theorem "thm_part10_relations" (parent := "iso80000_part10_relations") (lean := "PropertyKindCalculus.Iso80000.Part10.DefiningRelations.doseEquivalentOf_isProduct") (tags := "proved") (effort := "small")
*Dose equivalent is absorbed dose × quality factor — a verified construction (item
10-83.1).* A dose equivalent built as the product of an absorbed dose and the dimensionless
quality factor carries its product certificate by construction, over the `ℝ` carrier. The
companion `doseEquivalent_dim_from_dose_quality` shows it keeps the dimension of absorbed
dose `L²·T⁻²` _because_ the quality factor is dimension one — the gray/sievert collision as
a checked computation. Uses {uses "def_quotient_kind"}[the quotient kind-law].
:::

:::proof "thm_part10_relations"
`doseEquivalentOf d q := Quantity.mul doseEquivalent_prod_dose_quality d q`, and
`doseEquivalentOf_isProduct` is `rfl`. The same families give `specificActivityOf` (= `A/m`)
and the reciprocal/quotient kind-laws `meanLife_recip_decayConstant`,
`absorbedDoseRate_quot_dose_duration`, and `massAttenuation_quot_linear_density`, crossing
to ISO 80000-3 and -4.
:::

# Item index — ISO 80000-10

Every catalogued item of ISO 80000-10, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it. Each item number links to the formalized result it participates in. Symbols and
unit strings are _citation locators_; nothing normative is reproduced.

:::iso_doc_table part10IndexTable
:::
