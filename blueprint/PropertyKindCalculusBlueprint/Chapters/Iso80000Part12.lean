import Verso
import VersoManual
import VersoBlueprint
-- The Part-12 nodes link real declarations (the condensed-matter dimensioned kinds, the
-- seven-energy collision, the five-temperature and thirteen-length families, the
-- dimension-one family, and the thermoelectric defining-relation kind-laws), so this
-- chapter imports the Part-12 modules of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part12
import PropertyKindCalculus.Iso80000.Part12.DefiningRelations
import PropertyKindCalculusBlueprint.ItemIndex

open Verso.Genre
open Verso.Genre.Manual
open Informal

open PropertyKindCalculusBlueprint.ItemIndex

/-- Default blueprint node for ISO/IEC 80000-12 item-index rows (editorial). -/
def part12Default : String := "def_part12_catalogued_kind"

/-- Per-item blueprint cross-reference overrides for the ISO/IEC 80000-12 item
index (editorial; items not listed link to `part12Default`). Every other column
is generated from `PropertyKindCalculus.Iso80000.Part12.catalogue`. -/
def part12Refs : List (String × String) := [
  ("12-3", "thm_part12_collision"),
  ("12-4", "thm_part12_dim_one"),
  ("12-5.1", "thm_part12_dim_one"),
  ("12-5.2", "thm_part12_dim_one"),
  ("12-5.3", "thm_part12_dim_one"),
  ("12-5.4", "thm_part12_dim_one"),
  ("12-6", "thm_part12_collision"),
  ("12-8", "thm_part12_dim_one"),
  ("12-11", "thm_part12_temperatures"),
  ("12-13", "thm_part12_dim_one"),
  ("12-14", "thm_part12_dim_one"),
  ("12-20", "thm_part12_relations"),
  ("12-21", "thm_part12_relations"),
  ("12-22", "thm_part12_relations"),
  ("12-23", "thm_part12_relations"),
  ("12-24.1", "thm_part12_collision"),
  ("12-24.2", "thm_part12_collision"),
  ("12-25", "thm_part12_collision"),
  ("12-27.1", "thm_part12_collision"),
  ("12-27.2", "thm_part12_collision"),
  ("12-28", "thm_part12_temperatures"),
  ("12-31", "thm_part12_dim_one"),
  ("12-34", "thm_part12_collision"),
  ("12-35.1", "thm_part12_temperatures"),
  ("12-35.2", "thm_part12_temperatures"),
  ("12-35.3", "thm_part12_temperatures"),
  ("12-37", "thm_part12_collision")
]

/-- The ISO/IEC 80000-12 item index, generated live from the catalogue. -/
def part12IndexTable : DocTable :=
  standardIndex PropertyKindCalculus.Iso80000.Part12.catalogue part12Default part12Refs

#doc (Manual) "ISO 80000-12 — Condensed matter physics" =>
%%%
tag := "iso80000-part12"
%%%

The ninth part specified in full is ISO 80000-12, _Condensed matter physics_. Every item —
all of 12-1.1 … 12-38.2, sixty including every sub-suffixed item — is catalogued: the
lattice geometry, the reciprocal lattice and wavenumbers, the Debye and Grüneisen
quantities, the transport and thermoelectric coefficients, the work functions and band
energies, the carrier densities, and the magnetism and superconductivity quantities — each
carrying its exact source as data. Only _citation locators_ are recorded; no normative
content from the licensed standard is reproduced. The defining _mathematics_ of selected
remarks is specified in the sibling module `Part12.DefiningRelations`.

Condensed matter physics is where _dimension does not classify the kind_ stops being the
exception and becomes the rule: nearly every quantity collides in dimension with several
others. Five families dominate, and each is one big collision — _thirteen lengths_ on `L`,
_seven energies_ on `M·L²·T⁻²`, _five temperatures_ on `Θ`, _five carrier densities_ on
`L⁻³`, and _five reciprocal lengths_ on `L⁻¹`. The five named temperatures are especially
striking: the Debye, Fermi, Curie, Néel, and superconduction-transition temperatures share
one dimension _and_ one unit (the kelvin), and only the kind tells them apart.

# Quantity-kinds and units of ISO 80000-12

:::group "iso80000_part12"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, here over mass, length, time, temperature, and charge. The standard's
dimensional facts — a Fermi energy is `M·L²·T⁻²`, a lattice plane spacing `L`, a Debye
temperature `Θ` — are _checked computations_. Each unit is a
{uses "def_metrologicalUnit"}[metrological unit] of its kind; commensurability is a
type-level fact, so the joule of Fermi energy and the joule of gap energy are not
interchangeable though they share one dimension.
:::

:::definition "def_part12_catalogued_kind" (parent := "iso80000_part12") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "12-27.1"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with the
kind as data, so the source of each definition can be rendered or audited downstream.
:::

:::proof "def_part12_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `ISO 80000-12, Second edition, 2019-08 item 12-27.1`. The `catalogue` lists all 60
items in item order — the lattice geometry (12-1.1 … 12-8), the band energies (12-24.1 …
12-27.2), the carrier densities (12-29.1 … 12-29.5), the superconductivity quantities
(12-35.1 … 12-38.2), … — each paired with its coherent SI unit symbol.
:::

# Collisions everywhere — the kind classifies where the dimension cannot

ISO 80000-12 makes the catalogue's thesis the norm. Five families each collapse to one
dimension:

- _Seven energies_ — work function, ionization energy, electron affinity, Fermi energy,
  gap energy, exchange integral, superconductor energy gap — all `M·L²·T⁻²`.
- _Five temperatures_ — Debye, Fermi, Curie, Néel, superconduction-transition — all `Θ`,
  and all in the kelvin.
- _Thirteen lengths_ — lattice and position vectors, spacings, mean free paths, the
  penetration and coherence lengths — all `L`.
- _Five carrier densities_ and _five reciprocal lengths_ — all `L⁻³` and `L⁻¹`.

A dimension-only model sees one type per family; the kind layer keeps the Fermi energy from
the gap energy, the Curie temperature from the Néel temperature, the lattice spacing from
the Burgers vector. The five _named_ temperatures are the sharpest case: one dimension, one
unit symbol, five kinds.

:::group "iso80000_part12_collision"
The dimension-collision capstones, on _standard_ quantities: the {uses "def_dim"}[dimension
map] identifies the members of each family, while the kind layer keeps them apart, both as
kinds and as {uses "def_metrologicalUnit"}[units].
:::

:::theorem "thm_part12_collision" (parent := "iso80000_part12_collision") (lean := "PropertyKindCalculus.Iso80000.Part12.iso80000_12_dim_collision") (tags := "capstone, proved") (effort := "small")
*Fermi energy is not gap energy, though both are `J` and `M·L²·T⁻²` (items 12-27.1,
12-27.2).* There exist distinct ISO 80000-12 kinds with the same dimension — the seven
energies witness it. No dimension-only type system can separate them; the kind layer — and
the unit — does. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part12_collision"
`iso80000_12_dim_collision`, witnessed by `⟨fermiEnergy, gapEnergy, …⟩`. The unit fact
`jouleFermi_jouleGap_not_commensurable` is a `decide`; the companions
`latticePlaneSpacing_dim_eq_burgersVector_dim` (the length family) and
`curieTemperature_dim_eq_neelTemperature_dim` (the temperature family) record the other
collisions. Axiom-free.
:::

:::theorem "thm_part12_temperatures" (parent := "iso80000_part12_collision") (lean := "PropertyKindCalculus.Iso80000.Part12.kelvinCurie_kelvinNeel_not_commensurable") (tags := "proved") (effort := "small")
*The kelvin of the Curie temperature and the kelvin of the Néel temperature are not
commensurable, though both are `Θ` (items 12-35.1, 12-35.2).* Five named temperatures — the
Debye, Fermi, Curie, Néel, and superconduction-transition — share one dimension and one
unit symbol, and only the kind tells them apart. Uses {uses "def_metrologicalUnit"}[the
metrological unit].
:::

:::proof "thm_part12_temperatures"
`kelvinCurie_kelvinNeel_not_commensurable`, by `decide` after unfolding
`MetrologicalUnit.Commensurable`. Axiom-free.
:::

:::theorem "thm_part12_dim_one" (parent := "iso80000_part12_collision") (lean := "PropertyKindCalculus.Iso80000.Part12.iso80000_12_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard.* There exist distinct ISO 80000-12 kinds
with the same dimension one — the Bragg angle and the structure factor witness it, alongside
the order parameters, the atomic scattering factor, the Debye-Waller factor, the Grüneisen
parameters, and the mobility ratio. Dimension cannot separate them; the kind layer does.
Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part12_dim_one"
`iso80000_12_dim_one_collision`, witnessed by `⟨braggAngle, structureFactor, …⟩` with the
kind distinction a `decide` and reflexivity. Axiom-free.
:::

# The algebraic Remarks as kind-laws: thermoelectricity built by the kind algebra

Two Part-12 definitions state the thermoelectric coefficients _algebraically_: the Seebeck
coefficient is the thermoelectric voltage per temperature (12-21, `S = dE/dT`), and the
Peltier coefficient is the Seebeck coefficient times temperature (12-22, `Π = S·T`, the
Kelvin relation). Both are specified as R12 kind-laws, crossing to ISO 80000-5 for the
thermodynamic temperature.

:::group "iso80000_part12_relations"
The {uses "def_quotient_kind"}[quotient] and product families carry the kind-laws. Two
payoffs: thermoelectricity is built from the kind algebra (crossing to ISO 80000-5), and the
Seebeck coefficient is `V/K` _because_ it is a voltage per temperature, a checked
computation.
:::

:::theorem "thm_part12_relations" (parent := "iso80000_part12_relations") (lean := "PropertyKindCalculus.Iso80000.Part12.DefiningRelations.peltierOf_isProduct") (tags := "proved") (effort := "small")
*Peltier coefficient is Seebeck coefficient × temperature — a verified construction (item
12-22).* A Peltier coefficient built as the product of a Seebeck coefficient and a
thermodynamic temperature carries its product certificate by construction, over the `ℝ`
carrier. The companion `seebeck_dim_from_voltage_temperature` shows the Seebeck coefficient
is `V/K` _because_ it is a voltage per temperature. Uses {uses "def_quotient_kind"}[the
quotient kind-law].
:::

:::proof "thm_part12_relations"
`peltierOf s t := Quantity.mul peltier_prod_seebeck_temperature s t`, and `peltierOf_isProduct`
is `rfl`. The companion `seebeckOf` (= thermoelectric voltage / temperature) carries the
quotient certificate, with `seebeck_certificate_canonical` its canonicity; both cross to
ISO 80000-5.
:::

# Item index — ISO 80000-12

Every catalogued item of ISO 80000-12, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it. Each item number links to the formalized result it participates in. Symbols and
unit strings are _citation locators_; nothing normative is reproduced.

:::iso_doc_table part12IndexTable
:::
