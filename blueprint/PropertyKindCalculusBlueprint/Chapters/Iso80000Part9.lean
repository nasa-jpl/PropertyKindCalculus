import Verso
import VersoManual
import VersoBlueprint
-- The Part-9 nodes link real declarations (the mole-reduced dimensioned kinds, the
-- molar-mass-is-a-mass reduction, the seven-fold J/mol collision, the dimension-one
-- family with the mole inside it, and the defining-relation kind-laws), so this chapter
-- imports the Part-9 modules of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part9
import PropertyKindCalculus.Iso80000.Part9.DefiningRelations
import PropertyKindCalculusBlueprint.ItemIndex

open Verso.Genre
open Verso.Genre.Manual
open Informal

open PropertyKindCalculusBlueprint.ItemIndex

/-- Default blueprint node for ISO/IEC 80000-9 item-index rows (editorial). -/
def part9Default : String := "thm_part9_dim_one"

/-- Per-item blueprint cross-reference overrides for the ISO/IEC 80000-9 item
index (editorial; items not listed link to `part9Default`). Every other column
is generated from `PropertyKindCalculus.Iso80000.Part9.catalogue`. -/
def part9Refs : List (String × String) := [
  ("9-2", "thm_part9_mole"),
  ("9-4", "thm_part9_mole"),
  ("9-5", "thm_part9_mole"),
  ("9-6.1", "thm_part9_collision"),
  ("9-6.2", "thm_part9_collision"),
  ("9-6.3", "thm_part9_collision"),
  ("9-6.4", "thm_part9_collision"),
  ("9-7", "thm_part9_collision"),
  ("9-8", "thm_part9_collision"),
  ("9-9.1", "thm_part9_mole"),
  ("9-9.2", "def_part9_catalogued_kind"),
  ("9-10", "def_part9_catalogued_kind"),
  ("9-12.1", "thm_part9_mole"),
  ("9-12.2", "def_part9_catalogued_kind"),
  ("9-15", "thm_part9_mole"),
  ("9-16", "thm_part9_collision"),
  ("9-17", "thm_part9_collision"),
  ("9-19", "def_part9_catalogued_kind"),
  ("9-20", "def_part9_catalogued_kind"),
  ("9-21", "thm_part9_collision"),
  ("9-28", "def_part9_catalogued_kind"),
  ("9-30", "thm_part9_collision"),
  ("9-37.1", "thm_part9_collision"),
  ("9-37.2", "def_part9_catalogued_kind"),
  ("9-38", "def_part9_catalogued_kind"),
  ("9-39", "def_part9_catalogued_kind"),
  ("9-41", "def_part9_catalogued_kind"),
  ("9-42", "thm_part9_mole"),
  ("9-44", "def_part9_catalogued_kind"),
  ("9-45", "thm_part9_mole"),
  ("9-48", "thm_part9_mole"),
  ("9-49", "def_part9_catalogued_kind")
]

/-- The ISO/IEC 80000-9 item index, generated live from the catalogue. -/
def part9IndexTable : DocTable :=
  standardIndex PropertyKindCalculus.Iso80000.Part9.catalogue part9Default part9Refs

#doc (Manual) "ISO 80000-9 — Physical chemistry and molecular physics" =>
%%%
tag := "iso80000-part9"
%%%

The seventh part specified in full is ISO 80000-9, _Physical chemistry and molecular
physics_. Every item — all of 9-1 … 9-49, sixty-two including every sub-suffixed item — is
catalogued: counting entities and the mole, the molar quantities, the concentrations and
fractions, the chemical potential and the activity ladder, the reaction and equilibrium
quantities, statistical mechanics, and the transport and electrochemical coefficients —
each carrying its exact source as data. Only _citation locators_ are recorded; no normative
content from the licensed standard is reproduced. The defining _mathematics_ of selected
remarks is specified in the sibling module `Part9.DefiningRelations`.

Physical chemistry is the home of the _mole_, and so the sharpest test in the series of
the Finkelstein–Whitehead _scale-spanning_ reduction (the _Scale-spanning units_ chapter,
requirement _R13_): the mole is a human-selected dimensionless count of entities, `N_A` of
them, so `Dim.amountOfSubstance = 1`, and every quantity _per mole_ drops the mole. One
reduction reorganizes the whole part. Amount of substance joins the dimensionless family.
Molar mass _is a mass_, molar volume _a volume_, the amount-of-substance concentration _a
number density_, molality _an inverse mass_. The seven `J/mol` quantities collide on one
dimension; the three `J/(mol·K)` quantities on another.

# Quantity-kinds and units of ISO 80000-9

:::group "iso80000_part9"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, here over mass, length, time, temperature, and charge — with the mole
_reduced_ to dimension one. The standard's dimensional facts — a molar mass is `M`, an
amount concentration `L⁻³`, a molar energy `M·L²·T⁻²` — are _checked computations_. Each
unit is a {uses "def_metrologicalUnit"}[metrological unit] of its kind; commensurability
is a type-level fact, so the joule-per-mole of molar internal energy and that of molar
Gibbs energy are not interchangeable though they share one dimension.
:::

:::definition "def_part9_catalogued_kind" (parent := "iso80000_part9") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "9-12.1"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with the
kind as data, so the source of each definition can be rendered or audited downstream.
:::

:::proof "def_part9_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `ISO 80000-9, Second edition, 2019-08 item 9-12.1`. The `catalogue` lists all 62
items in item order — the mole (9-2), the molar quantities (9-4 … 9-8), the concentrations
(9-9.1 … 9-12.2), the activities (9-18 … 9-27.3), the partition functions (9-35.1 …
9-35.4), the conductivities (9-44, 9-45), … — each paired with its coherent SI unit symbol.
:::

# The mole reduces to dimension one — R13 at its sharpest

ISO 80000-9 is built on the _mole_. In the scale-spanning reading (R13), the mole is not a
base dimension but a human-selected dimensionless _count_: `N_A` entities. So amount of
substance is _dimension one_, and the `/mol` in every molar quantity is invisible to the
dimension functor. Molar mass (`kg/mol`) carries the dimension of _mass_; molar volume
(`m³/mol`) the dimension of _volume_; the amount-of-substance concentration (`mol/m³`) the
dimension of a _number density_ `L⁻³` — the very same dimension as a particle concentration;
molality (`mol/kg`) the dimension of an _inverse mass_.

And amount of substance itself joins the dimensionless family, distinct in kind from the
number of entities it counts (`N = n·N_A`) — both dimension one, two kinds. This is
requirement _R13_ in the place that makes it unavoidable: a `mol` is no more a base unit
than a `cd` (ISO 80000-7) or a `Sh` (IEC 80000-13).

:::group "iso80000_part9_mole"
With `Dim.amountOfSubstance = 1`, the {uses "def_dim"}[dimension map] sends every molar
quantity to the dimension of its non-molar counterpart. The reduction is a _checked
computation_, not a stipulation.
:::

:::theorem "thm_part9_mole" (parent := "iso80000_part9_mole") (lean := "PropertyKindCalculus.Iso80000.Part9.molarMass_dim_eq_mass") (tags := "capstone, proved") (effort := "small")
*Molar mass is a mass — the mole reduces (item 9-4).* With the mole dimension one, `kg/mol`
carries the dimension of mass, `M`. The companion facts record the rest of the reduction:
the amount-of-substance concentration is a number density (equal to the particle
concentration), molality is an inverse mass, and amount of substance is itself dimension
one. This is the scale-spanning reduction (R13) at the place the mole lives. Uses
{uses "def_dim"}[the dimension map] and {uses "def_scale_spanning_unit"}[the scale-spanning
units].
:::

:::proof "thm_part9_mole"
`molarMass_dim_eq_mass : molarMass.dim = Dim.mass`, by reflexivity (the kind is declared at
`Dim.mass`). The companions `amountOfSubstance_dim_eq_one`,
`amountConcentration_dim_eq_particleConcentration`, and `molality_dim_eq_inverseMass`
record the rest; the defining-relation versions
(`molarMass_dim_from_mass_amount`, `amountConcentration_dim_from_amount_volume`) derive the
reduction _from_ `M = m/n` and `c = n/V` with `dim n = 1`. Axiom-free.
:::

:::theorem "thm_part9_dim_one" (parent := "iso80000_part9_mole") (lean := "PropertyKindCalculus.Iso80000.Part9.iso80000_9_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard — with the mole inside it.* There exist
distinct ISO 80000-9 kinds with the same dimension one — amount of substance (the mole,
reduced by R13) and the number of entities witness it, alongside the fractions, the
activities, and the partition functions. Dimension cannot separate them; the kind layer
does. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part9_dim_one"
`iso80000_9_dim_one_collision`, witnessed by `⟨amountOfSubstance, numberOfEntities, …⟩`
with the kind distinction a `decide` and reflexivity. Axiom-free.
:::

# The seven-fold `J/mol` collision

The mole reducing to dimension one, the seven energies-per-mole — molar internal energy,
molar enthalpy, molar Helmholtz and Gibbs energies (9-6.1 … 9-6.4), the chemical potential
(9-17), the standard chemical potential (9-21), and the affinity of a reaction (9-30) — all
carry the _same_ dimension `M·L²·T⁻²` and the _same_ unit string `J/mol`, yet are seven
distinct kinds. A dimension-only model sees one type, "a real number of joules per mole",
for all seven; the kind layer keeps the chemical potential from being read as an affinity.
Likewise the molar heat capacity (9-7), molar entropy (9-8), and molar gas constant
(9-37.1) all share `J/(mol·K)`.

:::group "iso80000_part9_collision"
The dimension-collision capstone, on _standard_ quantities: the {uses "def_dim"}[dimension
map] identifies the seven `J/mol` kinds, while the kind layer keeps them apart, both as
kinds and as {uses "def_metrologicalUnit"}[units].
:::

:::theorem "thm_part9_collision" (parent := "iso80000_part9_collision") (lean := "PropertyKindCalculus.Iso80000.Part9.iso80000_9_dim_collision") (tags := "proved") (effort := "small")
*Molar internal energy is not molar Gibbs energy, though both are `J/mol` and `M·L²·T⁻²`
(items 9-6.1, 9-6.4).* There exist distinct ISO 80000-9 kinds with the same dimension —
seven `J/mol` quantities witness it. The mole reduces to dimension one, so no
dimension-only type system can separate them; the kind layer — and the unit — does. Uses
{uses "def_dim"}[the dimension map].
:::

:::proof "thm_part9_collision"
`iso80000_9_dim_collision`, witnessed by `⟨molarInternalEnergy, molarGibbsEnergy, …⟩`. The
unit fact `jPerMol_internalEnergy_gibbs_not_commensurable` is a `decide`;
`molarHeatCapacity_dim_eq_molarEntropy_dim` records the parallel `J/(mol·K)` collision, and
`molPerKg_molality_ionicStrength_not_commensurable` the `mol/kg` one. Axiom-free.
:::

# The algebraic Remarks as kind-laws: physical chemistry built from the other parts

The molar quantities of ISO 80000-9 are defined as quotients _by the amount of substance_
— molar mass is `m/n` (9-4), molar volume `V/n` (9-5), the amount concentration `n/V`
(9-12.1), molality `n/m` (9-15), the molar energies `U/n` (9-6.1) — composing Part-9 kinds
out of ISO 80000-3 (volume), -4 (mass), and -5 (energy) kinds and the mole. Each is
specified as an R12 kind-law.

:::group "iso80000_part9_relations"
The {uses "def_quotient_kind"}[quotient] family carries the kind-laws. Two payoffs on the
standard's own definitions: physical chemistry is built from the other parts, and the mole
reduces _as a checked computation_ — molar mass is a mass because `M = m/n` and `dim n = 1`.
:::

:::theorem "thm_part9_relations" (parent := "iso80000_part9_relations") (lean := "PropertyKindCalculus.Iso80000.Part9.DefiningRelations.molarMassOf_isQuotient") (tags := "proved") (effort := "small")
*Molar mass is mass / amount of substance — a verified construction (item 9-4).* A molar
mass built as the quotient of a mass by an amount of substance carries its quotient
certificate by construction, over the `ℝ` carrier, and canonicity makes the certificate
determine the quantity. The companion `molarMass_dim_from_mass_amount` shows the result is a
mass _because_ the mole is dimension one. Uses {uses "def_quotient_kind"}[the quotient
kind-law].
:::

:::proof "thm_part9_relations"
`molarMassOf m n := Quantity.div molarMass_quot_mass_amount m n`, and `molarMassOf_isQuotient`
is `rfl`; `molarMass_certificate_canonical` is `eq_div_of_isQuotient`. The same family gives
`amountConcentrationOf` (= `n/V`) and the cross-part kind-laws
`molarVolume_quot_volume_amount`, `molarInternalEnergy_quot_energy_amount`, and
`molality_quot_amount_mass`, crossing to ISO 80000-3/-4/-5.
:::

# Item index — ISO 80000-9

Every catalogued item of ISO 80000-9, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it (the mole reduced). Each item number links to the formalized result it
participates in. Symbols and unit strings are _citation locators_; nothing normative is
reproduced.

:::iso_doc_table part9IndexTable
:::
