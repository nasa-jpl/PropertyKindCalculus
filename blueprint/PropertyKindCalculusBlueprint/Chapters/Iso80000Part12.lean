import Verso
import VersoManual
import VersoBlueprint
-- The Part-12 nodes link real declarations (the condensed-matter dimensioned kinds, the
-- seven-energy collision, the five-temperature and thirteen-length families, the
-- dimension-one family, and the thermoelectric defining-relation kind-laws), so this
-- chapter imports the Part-12 modules of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part12
import PropertyKindCalculus.Iso80000.Part12.DefiningRelations

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "ISO 80000-12 — Condensed matter physics" =>

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

:::table +header (align := left)
*
  * Item
  * Quantity
  * Symbol
  * Unit
  * Dimension
*
  * {bpref "def_part12_catalogued_kind"}[12-1.1]
  * lattice vector
  * `R`
  * `m`
  * `L`
*
  * {bpref "def_part12_catalogued_kind"}[12-1.2]
  * fundamental lattice vectors
  * `a₁`
  * `m`
  * `L`
*
  * {bpref "def_part12_catalogued_kind"}[12-2.1]
  * angular reciprocal lattice vector
  * `G`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "def_part12_catalogued_kind"}[12-2.2]
  * fundamental reciprocal lattice vectors
  * `b₁`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "thm_part12_collision"}[12-3]
  * lattice plane spacing
  * `d`
  * `m`
  * `L`
*
  * {bpref "thm_part12_dim_one"}[12-4]
  * Bragg angle
  * `ϑ`
  * `1`
  * `1`
*
  * {bpref "thm_part12_dim_one"}[12-5.1]
  * short-range order parameter
  * `r`
  * `1`
  * `1`
*
  * {bpref "thm_part12_dim_one"}[12-5.2]
  * long-range order parameter
  * `R`
  * `1`
  * `1`
*
  * {bpref "thm_part12_dim_one"}[12-5.3]
  * atomic scattering factor
  * `f`
  * `1`
  * `1`
*
  * {bpref "thm_part12_dim_one"}[12-5.4]
  * structure factor
  * `F`
  * `1`
  * `1`
*
  * {bpref "thm_part12_collision"}[12-6]
  * Burgers vector
  * `b`
  * `m`
  * `L`
*
  * {bpref "def_part12_catalogued_kind"}[12-7.1]
  * particle position vector
  * `r`
  * `m`
  * `L`
*
  * {bpref "def_part12_catalogued_kind"}[12-7.2]
  * equilibrium position vector
  * `R₀`
  * `m`
  * `L`
*
  * {bpref "def_part12_catalogued_kind"}[12-7.3]
  * displacement vector
  * `u`
  * `m`
  * `L`
*
  * {bpref "thm_part12_dim_one"}[12-8]
  * Debye-Waller factor
  * `D`
  * `1`
  * `1`
*
  * {bpref "def_part12_catalogued_kind"}[12-9.1]
  * angular wavenumber
  * `k`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "def_part12_catalogued_kind"}[12-9.2]
  * Fermi angular wavenumber
  * `k_F`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "def_part12_catalogued_kind"}[12-9.3]
  * Debye angular wavenumber
  * `q_D`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "def_part12_catalogued_kind"}[12-10]
  * Debye angular frequency
  * `ω_D`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "thm_part12_temperatures"}[12-11]
  * Debye temperature
  * `Θ_D`
  * `K`
  * `Θ`
*
  * {bpref "def_part12_catalogued_kind"}[12-12]
  * density of vibrational states
  * `g`
  * `m⁻³·s`
  * `L⁻³·T`
*
  * {bpref "thm_part12_dim_one"}[12-13]
  * thermodynamic Grüneisen parameter
  * `γ_G`
  * `1`
  * `1`
*
  * {bpref "thm_part12_dim_one"}[12-14]
  * Grüneisen parameter
  * `γ`
  * `1`
  * `1`
*
  * {bpref "def_part12_catalogued_kind"}[12-15.1]
  * mean free path of phonons
  * `l_p`
  * `m`
  * `L`
*
  * {bpref "def_part12_catalogued_kind"}[12-15.2]
  * mean free path of electrons
  * `l_e`
  * `m`
  * `L`
*
  * {bpref "def_part12_catalogued_kind"}[12-16]
  * energy density of states
  * `n_E`
  * `J⁻¹·m⁻³`
  * `M⁻¹·L⁻⁵·T²`
*
  * {bpref "def_part12_catalogued_kind"}[12-17]
  * residual resistivity
  * `ρ₀`
  * `Ω·m`
  * `M·L³·T⁻¹·C⁻²`
*
  * {bpref "def_part12_catalogued_kind"}[12-18]
  * Lorenz coefficient
  * `L`
  * `V²/K²`
  * `M²·L⁴·T⁻⁴·C⁻²·Θ⁻²`
*
  * {bpref "def_part12_catalogued_kind"}[12-19]
  * Hall coefficient
  * `R_H`
  * `m³/C`
  * `L³·C⁻¹`
*
  * {bpref "thm_part12_relations"}[12-20]
  * thermoelectric voltage
  * `E_ab`
  * `V`
  * `M·L²·T⁻²·C⁻¹`
*
  * {bpref "thm_part12_relations"}[12-21]
  * Seebeck coefficient
  * `S_ab`
  * `V/K`
  * `M·L²·T⁻²·C⁻¹·Θ⁻¹`
*
  * {bpref "thm_part12_relations"}[12-22]
  * Peltier coefficient
  * `Π_ab`
  * `V`
  * `M·L²·T⁻²·C⁻¹`
*
  * {bpref "thm_part12_relations"}[12-23]
  * Thomson coefficient
  * `μ`
  * `V/K`
  * `M·L²·T⁻²·C⁻¹·Θ⁻¹`
*
  * {bpref "thm_part12_collision"}[12-24.1]
  * work function
  * `φ`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part12_collision"}[12-24.2]
  * ionization energy
  * `E_i`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part12_collision"}[12-25]
  * electron affinity
  * `χ`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "def_part12_catalogued_kind"}[12-26]
  * Richardson constant
  * `A`
  * `A·m⁻²·K⁻²`
  * `C·T⁻¹·L⁻²·Θ⁻²`
*
  * {bpref "thm_part12_collision"}[12-27.1]
  * Fermi energy
  * `E_F`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part12_collision"}[12-27.2]
  * gap energy
  * `E_g`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part12_temperatures"}[12-28]
  * Fermi temperature
  * `T_F`
  * `K`
  * `Θ`
*
  * {bpref "def_part12_catalogued_kind"}[12-29.1]
  * electron density
  * `n`
  * `m⁻³`
  * `L⁻³`
*
  * {bpref "def_part12_catalogued_kind"}[12-29.2]
  * hole density
  * `p`
  * `m⁻³`
  * `L⁻³`
*
  * {bpref "def_part12_catalogued_kind"}[12-29.3]
  * intrinsic carrier density
  * `n_i`
  * `m⁻³`
  * `L⁻³`
*
  * {bpref "def_part12_catalogued_kind"}[12-29.4]
  * donor density
  * `n_d`
  * `m⁻³`
  * `L⁻³`
*
  * {bpref "def_part12_catalogued_kind"}[12-29.5]
  * acceptor density
  * `n_a`
  * `m⁻³`
  * `L⁻³`
*
  * {bpref "def_part12_catalogued_kind"}[12-30]
  * effective mass
  * `m*`
  * `kg`
  * `M`
*
  * {bpref "thm_part12_dim_one"}[12-31]
  * mobility ratio
  * `b`
  * `1`
  * `1`
*
  * {bpref "def_part12_catalogued_kind"}[12-32.1]
  * relaxation time
  * `τ`
  * `s`
  * `T`
*
  * {bpref "def_part12_catalogued_kind"}[12-32.2]
  * carrier lifetime
  * `τ`
  * `s`
  * `T`
*
  * {bpref "def_part12_catalogued_kind"}[12-33]
  * diffusion length
  * `L`
  * `m`
  * `L`
*
  * {bpref "thm_part12_collision"}[12-34]
  * exchange integral
  * `J`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part12_temperatures"}[12-35.1]
  * Curie temperature
  * `T_C`
  * `K`
  * `Θ`
*
  * {bpref "thm_part12_temperatures"}[12-35.2]
  * Néel temperature
  * `T_N`
  * `K`
  * `Θ`
*
  * {bpref "thm_part12_temperatures"}[12-35.3]
  * superconduction transition temperature
  * `T_c`
  * `K`
  * `Θ`
*
  * {bpref "def_part12_catalogued_kind"}[12-36.1]
  * thermodynamic critical magnetic flux density
  * `B_c`
  * `T`
  * `M·T⁻¹·C⁻¹`
*
  * {bpref "def_part12_catalogued_kind"}[12-36.2]
  * lower critical magnetic flux density
  * `B_c1`
  * `T`
  * `M·T⁻¹·C⁻¹`
*
  * {bpref "def_part12_catalogued_kind"}[12-36.3]
  * upper critical magnetic flux density
  * `B_c2`
  * `T`
  * `M·T⁻¹·C⁻¹`
*
  * {bpref "thm_part12_collision"}[12-37]
  * superconductor energy gap
  * `Δ`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "def_part12_catalogued_kind"}[12-38.1]
  * London penetration depth
  * `λ_L`
  * `m`
  * `L`
*
  * {bpref "def_part12_catalogued_kind"}[12-38.2]
  * coherence length
  * `ξ`
  * `m`
  * `L`
:::
