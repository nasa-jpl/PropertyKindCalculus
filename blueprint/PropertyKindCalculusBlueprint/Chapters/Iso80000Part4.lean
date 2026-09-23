import Verso
import VersoManual
import VersoBlueprint
-- The Part-4 nodes link real declarations (dimensioned kinds, checked dimensional
-- facts, the force-family specialization lattice, the torque/energy collision, and the
-- cross-part defining relations), so this chapter imports the Part-4 modules of the
-- `Iso80000` library (PhysLib-backed).
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.Iso80000.Part4.DefiningRelations
import PropertyKindCalculusBlueprint.ItemIndex

open Verso.Genre
open Verso.Genre.Manual
open Informal

open PropertyKindCalculusBlueprint.ItemIndex

/-- Default blueprint node for ISO/IEC 80000-4 item-index rows (editorial). -/
def part4Default : String := "def_part4_catalogued_kind"

/-- Per-item blueprint cross-reference overrides for the ISO/IEC 80000-4 item
index (editorial; items not listed link to `part4Default`). Every other column
is generated from `PropertyKindCalculus.Iso80000.Part4.catalogue`. -/
def part4Refs : List (String × String) := [
  ("4-2", "thm_part4_momentum"),
  ("4-3", "thm_part4_momentum"),
  ("4-4", "thm_part4_dim_one"),
  ("4-8", "thm_part4_momentum"),
  ("4-9.1", "def_part4_force_species"),
  ("4-9.2", "def_part4_force_species"),
  ("4-9.3", "thm_part4_static_kinetic"),
  ("4-9.4", "thm_part4_static_kinetic"),
  ("4-9.5", "def_part4_force_species"),
  ("4-9.6", "def_part4_force_species"),
  ("4-10", "thm_part4_torque_energy"),
  ("4-12.1", "thm_part4_torque_energy"),
  ("4-12.2", "thm_part4_torque_energy"),
  ("4-14.1", "thm_part4_momentum"),
  ("4-16.1", "thm_part4_momentum"),
  ("4-17.1", "thm_part4_dim_one"),
  ("4-17.2", "thm_part4_momentum"),
  ("4-17.3", "thm_part4_dim_one"),
  ("4-17.4", "thm_part4_dim_one"),
  ("4-18", "thm_part4_dim_one"),
  ("4-19.1", "thm_part4_momentum"),
  ("4-23.1", "thm_part4_dim_one"),
  ("4-23.2", "thm_part4_dim_one"),
  ("4-23.3", "thm_part4_dim_one"),
  ("4-23.4", "thm_part4_dim_one"),
  ("4-24", "thm_part4_momentum"),
  ("4-25", "thm_part4_momentum"),
  ("4-27", "thm_part4_efficiency"),
  ("4-28.1", "thm_part4_torque_energy"),
  ("4-28.2", "thm_part4_torque_energy"),
  ("4-28.3", "thm_part4_torque_energy"),
  ("4-28.4", "thm_part4_torque_energy"),
  ("4-29", "thm_part4_efficiency")
]

/-- The ISO/IEC 80000-4 item index, generated live from the catalogue. -/
def part4IndexTable : DocTable :=
  standardIndex PropertyKindCalculus.Iso80000.Part4.catalogue part4Default part4Refs

#doc (Manual) "ISO 80000-4 — Mechanics" =>
%%%
tag := "iso80000-part4"
%%%

The second part specified in full is ISO 80000-4, _Mechanics_. Every item — all of
4-1 … 4-32 — is catalogued: mass and the densities, momentum, the force family,
impulse and the moments, pressure and stress, the strains and elastic moduli, the
viscosities, power and the energies, the flows, and action — each carrying its exact
source as data: the part, the printed item designation, the principal quantity symbol,
and the coherent SI unit symbol. Only *citation locators* are recorded; no normative
content (definitions, remarks) from the licensed standard is reproduced. The defining
_mathematics_ of selected remarks is formalized in the sibling module
`Part4.DefiningRelations`.

Mechanics is where the two theses of the calculus bite hardest. The standard's own
quantities force the issues: a force family that is a specialization lattice; the
textbook torque-versus-energy dimension collision (both `M·L²·T⁻²`, the newton metre
reserved for one and the joule for the other); and a web of defining relations that
build mechanical quantities out of Part-3 _space-and-time_ quantities — momentum from
mass and velocity, pressure from force and area.

# Quantity-kinds and units of ISO 80000-4

:::group "iso80000_part4"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, so the standard's dimensional facts — force is `M·L·T⁻²`, energy `M·L²·T⁻²`,
pressure `M·L⁻¹·T⁻²`, power `M·L²·T⁻³` — are _checked computations_ rather than
annotations. Each unit is a {uses "def_metrologicalUnit"}[metrological unit] of its kind;
commensurability is a type-level fact, so a kilogram and a newton are not interchangeable.
:::

:::definition "def_part4_catalogued_kind" (parent := "iso80000_part4") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "4-9.1"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with
the kind as data, so the source of each definition can be rendered or audited downstream
rather than kept in a comment.
:::

:::proof "def_part4_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `ISO 80000-4, Second edition, 2019-08 item 4-9.1`. The `catalogue` lists all 54
items in item order — mass (4-1), momentum (4-8), force (4-9.1), torque (4-12.2),
pressure (4-14.1), power (4-27), action (4-32), … — each paired with its coherent SI
unit symbol.
:::

:::theorem "thm_part4_force_dim" (parent := "iso80000_part4") (lean := "PropertyKindCalculus.Iso80000.Part4.force_dim_time") (tags := "proved") (effort := "small")
*Force is `M·L·T⁻²` (item 4-9.1).* The catalogued force kind carries time-exponent
minus two in PhysLib's dimension group — the standard's dimensional statement reproduced
as a checked computation, not an annotation. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part4_force_dim"
Proved as `force_dim_time : force.dim.time = -2` in the `Iso80000` library, discharged by
`norm_num` over the PhysLib dimension lemmas. The companions `energy_dim_length = 2`
(item 4-28), `pressure_dim_length = -1` (item 4-14.1), and `power_dim_time = -3`
(item 4-27) record the rest of the mechanical algebra.
:::

:::theorem "thm_part4_kilogram_newton" (parent := "iso80000_part4") (lean := "PropertyKindCalculus.Iso80000.Part4.kilogram_newton_not_commensurable") (tags := "proved") (effort := "small")
*A kilogram and a newton are not commensurable.* Mass and force are distinct kinds, so
their units cannot be compared by ratio — a type-level fact, not a runtime check. Uses
{uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part4_kilogram_newton"
Proved as `kilogram_newton_not_commensurable : ¬ kilogram.Commensurable newton` by
unfolding `Commensurable` to the underlying kinds and `decide`. The kilogram and the
newton are each `WellFormed` (mass and force are ratio-scale).
:::

# The force family: distinguishing kinds by measurement principle

ISO 80000-4 lists weight (4-9.2), static friction force (4-9.3), kinetic friction force
(4-9.4), rolling resistance (4-9.5), and drag force (4-9.6) as _separate items_ — yet
every one has dimension `M·L·T⁻²` and ratio scale. The standard distinguishes them only
in _prose_: a weight acts in a gravitational field; a static friction force resists
motion _before_ a body slides; a kinetic friction force resists motion _while_ it slides.
A dimension-only or representation-only model cannot capture the difference; it sees one
type, "a real number of newtons", for all of them.

This is requirement _R2_ again, now on the force family — the exact pattern Part 3 set
on the length family. Item 4-9.1, _force_, is the broad genus; each later item is
specified as a _species_ of force, distinguished *not by fiat* but by an explicit
_measurement principle_ (Dybkær's examination principle, §7.5). The species are then
provably distinct kinds while remaining _mutually comparable_ as forces.

:::group "iso80000_part4_force"
The force species are individuated by an {uses "def_examination"}[examination principle]
and arranged as a {uses "def_specializes"}[specialization] lattice over the general force
kind. The sharpest case is static versus kinetic friction: physically the same dimension
and both "friction forces", they are nonetheless different kinds — and the calculus
proves it from their differing measurement conditions, not from a naming convention.
:::

:::definition "def_part4_force_species" (parent := "iso80000_part4_force") (lean := "PropertyKindCalculus.Iso80000.Part4.forceSpecies")
A _force species_ is a ratio-scale {uses "def_quantity"}[quantity]-kind of dimension
`M·L·T⁻²` carrying an {uses "def_examination"}[examination principle] — this work's own
terse descriptor of the measurement principle that distinguishes it (gravitational-field
action, pre-slip resistance, sliding resistance, …), never the standard's normative
definition. Weight, the static and kinetic friction forces, the rolling resistance, and
the drag force are all species of the general force kind (item 4-9.1).
:::

:::proof "def_part4_force_species"
`forceSpecies id p := { kind := { id, scale := .ratio, examPrinciple := some p.id },
dim := MDim.force }`. The general `force` carries no examination principle; the
direct-parent edges of the family are collected in an `Edge` relation, each species an
edge to `force` (mirroring the standard's "force (item 4-9.1) … acting/resisting …").
:::

:::theorem "thm_part4_static_kinetic" (parent := "iso80000_part4_force") (lean := "PropertyKindCalculus.Iso80000.Part4.staticFriction_ne_kineticFriction") (tags := "proved") (effort := "small")
*Static and kinetic friction forces are distinct kinds — by measurement principle, not by
fiat.* They share dimension `M·L·T⁻²` and are both "friction forces", yet are different
kinds _because they are examined under different conditions_ (resistance before sliding vs
during sliding), proved through `distinct_of_examPrinciple` (§7.5). This is the
force-family analogue of width ≠ distance. Uses {uses "def_examination"}[the examination
principle].
:::

:::proof "thm_part4_static_kinetic"
`staticFriction_ne_kineticFriction : staticFrictionForce.kind ≠ kineticFrictionForce.kind`,
from `KindOfProperty.distinct_of_examPrinciple` applied to the differing principles
`pre-slip-resistance` and `sliding-resistance` (a `decide` on the `Option String` links).
The companions `weight_ne_dragForce` and `weight_ne_force` separate the other species, and
`weight_examinedBy` checks the kind-to-principle link. Axiom-free.
:::

:::theorem "thm_part4_weight_comparable" (parent := "iso80000_part4_force") (lean := "PropertyKindCalculus.Iso80000.Part4.weight_dragForce_comparable") (tags := "proved") (effort := "small")
*Comparability is preserved.* Weight and the drag force, though distinct kinds, remain
_mutually comparable_ — they share the super-kind force, so combining them is possible but
only via an explicit up-cast, never silently. The companion `weight_specializes_force`
records that a weight specializes force. Uses {uses "def_specializes"}[specialization].
:::

:::proof "thm_part4_weight_comparable"
`weight_dragForce_comparable : MutuallyComparable Edge weight.kind dragForce.kind`, with
witness `force.kind`, each species reaching it by one edge. Axiom-free.
:::

# Dimension does not classify; the kind does — the torque/energy case

Part 4 holds the textbook example of a dimension collision. _Torque_ (moment of force,
4-12.1/4-12.2) and _energy_ (work, 4-28) are _both_ `M·L²·T⁻²` — yet they are distinct
kinds, measured in distinct units: the newton metre is reserved for torque, the joule for
energy, precisely because they are different kinds. And Part 4 is dense with such
collisions: momentum and impulse (`M·L·T⁻¹`); angular momentum, angular impulse, and
action (`M·L²·T⁻¹`); pressure, stress, and the three elastic moduli (`M·L⁻¹·T⁻²`); and a
whole dimension-one family — the relative densities, the strains, the Poisson number, the
friction factors, the drag coefficient, and the efficiency.

:::group "iso80000_part4_collision"
These are the dimension-disambiguation capstone, on _standard_ quantities: the
{uses "def_dim"}[dimension map] identifies the members of each pair, while the kind layer
keeps them apart, both as kinds and as {uses "def_metrologicalUnit"}[units].
:::

:::theorem "thm_part4_torque_energy" (parent := "iso80000_part4_collision") (lean := "PropertyKindCalculus.Iso80000.Part4.iso80000_4_dim_collision") (tags := "proved") (effort := "small")
*Torque is not energy, though both are `M·L²·T⁻²`.* There exist distinct ISO 80000-4 kinds
with the same dimension — torque and energy witness it. No dimension-only type system can
separate them; the kind layer does. This is the textbook case that a dimension does not
classify a quantity. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part4_torque_energy"
`iso80000_4_dim_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim`,
witnessed by `⟨torque, mechanicalEnergy, …⟩` with `torque_ne_energy` (a `decide`) and
reflexivity. The companion `momentum_ne_impulse` is the `M·L·T⁻¹` case. Axiom-free.
:::

:::theorem "thm_part4_nm_joule" (parent := "iso80000_part4_collision") (lean := "PropertyKindCalculus.Iso80000.Part4.newtonMetre_joule_not_commensurable") (tags := "proved") (effort := "small")
*A newton metre is not a joule, though both are `M·L²·T⁻²`.* The SI units of torque and
energy are not commensurable, because their kinds differ — the unit-level form of the
torque/energy collision, a type-level fact the dimension cannot see. Uses
{uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part4_nm_joule"
`newtonMetre_joule_not_commensurable : ¬ newtonMetre.Commensurable joule` by unfolding to
the underlying kinds and `decide` (torque's kind differs from the energy kind).
:::

:::theorem "thm_part4_dim_one" (parent := "iso80000_part4_collision") (lean := "PropertyKindCalculus.Iso80000.Part4.iso80000_4_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard.* There exist distinct ISO 80000-4 kinds
with the same dimension one — efficiency and the relative mass density witness it,
alongside the strains, the Poisson number, and the friction factors. Dimension cannot
separate them; the kind layer does. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part4_dim_one"
`iso80000_4_dim_one_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim
∧ a.dim = 1`, witnessed by `⟨efficiency, relativeMassDensity, …⟩` with
`efficiency_ne_relativeMassDensity` (a `decide`) and reflexivity. Axiom-free.
:::

# The algebraic Remarks as kind-laws: mechanics built from space and time

Many Part-4 remarks state a quantity's defining relation _algebraically_ — and, in
mechanics, the other quantities are often _space-and-time_ quantities from Part 3.
Momentum is mass × velocity (4-8); pressure is force / area (4-14.1); mass density is
mass / volume (4-2); specific volume is `1/ρ` (4-3); kinematic viscosity is `η/ρ` (4-25);
efficiency is output power / input power (4-29); a modulus of elasticity is stress /
strain (4-19.1). Each is formalized as an R12 kind-law over the catalogued kinds, several
composing a Part-4 kind out of Part-3 kinds.

:::group "iso80000_part4_relations"
The {uses "def_quotient_kind"}[quotient], {uses "def_reciprocal_kind"}[reciprocal], and
{uses "def_product_kind"}[product] families carry the kind-laws. Three payoffs on the
standard's own remarks: the cross-part dependency structure of the ISQ is made explicit;
the _dimension follows from the relation_ as a checked computation; and a
verified-by-construction quantity carries its classification certificate.
:::

:::theorem "thm_part4_momentum" (parent := "iso80000_part4_relations") (lean := "PropertyKindCalculus.Iso80000.Part4.DefiningRelations.momentumOf_isProduct") (tags := "proved") (effort := "small")
*Momentum is mass × velocity — a verified, cross-part construction.* A momentum built as
the product of a mass (Part 4) and a velocity (Part 3) carries its product certificate by
construction, over the `ℝ` carrier, and canonicity makes the certificate determine the
quantity. Uses {uses "def_product_kind"}[the product kind-law].
:::

:::proof "thm_part4_momentum"
`momentumOf m v := Quantity.mul momentum_prod_mass_velocity m v`, and `momentumOf_isProduct`
is `rfl`; `momentum_certificate_canonical` is `eq_mul_of_isProduct`. The kind-law
`momentum_prod_mass_velocity : ProductKind mass.kind Part3.velocity.kind momentum.kind` is
`⟨rfl, rfl, rfl⟩`, and `momentum_dim_from_mass_velocity` checks `M·L·T⁻¹` follows from the
relation. The same families give `pressureOf` (pressure = force / area) and `efficiencyOf`.
:::

:::theorem "thm_part4_efficiency" (parent := "iso80000_part4_relations") (lean := "PropertyKindCalculus.Iso80000.Part4.DefiningRelations.efficiency_dim_from_power_ratio") (tags := "proved") (effort := "small")
*Efficiency is dimension one because it is a ratio of two powers.* From the remark
`η = P_out/P_in`, the powers cancel and the dimension is _computed_ to be one — not
stipulated, the mechanics analogue of the plane angle being a ratio of two lengths. Yet
efficiency remains a distinct kind from every other dimension-one quantity (the collision
capstone above). Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part4_efficiency"
`efficiency_dim_from_power_ratio : efficiency.dim = power.dim / power.dim`, by reducing both
sides via `div_self'` (`a / a = 1`). The kind-law `efficiency_quot_power_power` is
`⟨rfl, rfl, rfl⟩` and `efficiencyOf` builds a certified efficiency from two powers.
:::

# Item index — ISO 80000-4

Every catalogued item of ISO 80000-4, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it. Each item number links to the formalized result it participates in — the
force-family lattice, the torque/energy collision, a cross-part defining relation, or the
catalogue itself. Symbols and unit strings are *citation locators*; nothing normative is
reproduced.

:::iso_doc_table part4IndexTable
:::
