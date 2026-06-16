import Verso
import VersoManual
import VersoBlueprint
-- The Part-10 nodes link real declarations (the atomic/nuclear dimensioned kinds, the
-- gray/sievert collision, the becquerel collision, the dimension-one family, and the
-- defining-relation kind-laws), so this chapter imports the Part-10 modules of the
-- `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part10
import PropertyKindCalculus.Iso80000.Part10.DefiningRelations

open Verso.Genre
open Verso.Genre.Manual
open Informal

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

:::table +header (align := left)
*
  * Item
  * Quantity
  * Symbol
  * Unit
  * Dimension
*
  * {bpref "thm_part10_dim_one"}[10-1.1]
  * atomic number
  * `Z`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-1.2]
  * neutron number
  * `N`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-1.3]
  * nucleon number
  * `A`
  * `1`
  * `1`
*
  * {bpref "def_part10_catalogued_kind"}[10-2]
  * rest mass
  * `m`
  * `kg`
  * `M`
*
  * {bpref "def_part10_catalogued_kind"}[10-3]
  * rest energy
  * `E₀`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-4.1]
  * atomic mass
  * `m_a`
  * `kg`
  * `M`
*
  * {bpref "def_part10_catalogued_kind"}[10-4.2]
  * nuclidic mass
  * `m`
  * `kg`
  * `M`
*
  * {bpref "def_part10_catalogued_kind"}[10-4.3]
  * unified atomic mass constant
  * `m_u`
  * `kg`
  * `M`
*
  * {bpref "def_part10_catalogued_kind"}[10-5.1]
  * elementary charge
  * `e`
  * `C`
  * `C`
*
  * {bpref "thm_part10_dim_one"}[10-5.2]
  * charge number
  * `c`
  * `1`
  * `1`
*
  * {bpref "def_part10_catalogued_kind"}[10-6]
  * Bohr radius
  * `a₀`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-7]
  * Rydberg constant
  * `R∞`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-8]
  * Hartree energy
  * `E_H`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-9.1]
  * magnetic dipole moment
  * `μ`
  * `m²·A`
  * `L²·C·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-9.2]
  * Bohr magneton
  * `μ_B`
  * `m²·A`
  * `L²·C·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-9.3]
  * nuclear magneton
  * `μ_N`
  * `m²·A`
  * `L²·C·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-10]
  * spin
  * `s`
  * `J·s`
  * `M·L²·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-11]
  * total angular momentum
  * `J`
  * `J·s`
  * `M·L²·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-12.1]
  * gyromagnetic ratio
  * `γ`
  * `A·m²·J⁻¹·s⁻¹`
  * `M⁻¹·C`
*
  * {bpref "def_part10_catalogued_kind"}[10-12.2]
  * gyromagnetic ratio of the electron
  * `γ_e`
  * `A·m²·J⁻¹·s⁻¹`
  * `M⁻¹·C`
*
  * {bpref "thm_part10_dim_one"}[10-13.1]
  * quantum number
  * `N`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-13.2]
  * principal quantum number
  * `n`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-13.3]
  * orbital angular momentum quantum number
  * `l`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-13.4]
  * magnetic quantum number
  * `m`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-13.5]
  * spin quantum number
  * `s`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-13.6]
  * total angular momentum quantum number
  * `j`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-13.7]
  * nuclear spin quantum number
  * `I`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-13.8]
  * hyperfine structure quantum number
  * `F`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-14.1]
  * Landé factor
  * `g`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-14.2]
  * g factor of nucleus
  * `g`
  * `1`
  * `1`
*
  * {bpref "thm_part10_becquerel"}[10-15.1]
  * Larmor angular frequency
  * `ω_L`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "thm_part10_becquerel"}[10-15.2]
  * Larmor frequency
  * `ν_L`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "thm_part10_becquerel"}[10-15.3]
  * nuclear precession angular frequency
  * `ω_N`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "thm_part10_becquerel"}[10-16]
  * cyclotron angular frequency
  * `ω_c`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-17]
  * gyroradius
  * `r_g`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-18]
  * nuclear quadrupole moment
  * `Q`
  * `m²`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-19.1]
  * nuclear radius
  * `R`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-19.2]
  * electron radius
  * `r_e`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-20]
  * Compton wavelength
  * `λ_C`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-21.1]
  * mass excess
  * `Δ`
  * `kg`
  * `M`
*
  * {bpref "def_part10_catalogued_kind"}[10-21.2]
  * mass defect
  * `B`
  * `kg`
  * `M`
*
  * {bpref "thm_part10_dim_one"}[10-22.1]
  * relative mass excess
  * `Δ_r`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-22.2]
  * relative mass defect
  * `B_r`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-23.1]
  * packing fraction
  * `f`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-23.2]
  * binding fraction
  * `b`
  * `1`
  * `1`
*
  * {bpref "thm_part10_becquerel"}[10-24]
  * decay constant
  * `λ`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "thm_part10_relations"}[10-25]
  * mean duration of life
  * `τ`
  * `s`
  * `T`
*
  * {bpref "def_part10_catalogued_kind"}[10-26]
  * level width
  * `Γ`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part10_becquerel"}[10-27]
  * activity
  * `A`
  * `Bq`
  * `T⁻¹`
*
  * {bpref "thm_part10_relations"}[10-28]
  * specific activity
  * `a`
  * `Bq/kg`
  * `M⁻¹·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-29]
  * activity density
  * `c_A`
  * `Bq/m³`
  * `L⁻³·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-30]
  * surface-activity density
  * `a_S`
  * `Bq/m²`
  * `L⁻²·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-31]
  * half life
  * `T_½`
  * `s`
  * `T`
*
  * {bpref "def_part10_catalogued_kind"}[10-32]
  * alpha disintegration energy
  * `Q_α`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-33]
  * maximum beta-particle energy
  * `E_β`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-34]
  * beta disintegration energy
  * `Q_β`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part10_dim_one"}[10-35]
  * internal conversion factor
  * `α`
  * `1`
  * `1`
*
  * {bpref "thm_part10_becquerel"}[10-36]
  * particle emission rate
  * `Ṅ`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-37.1]
  * reaction energy
  * `Q`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-37.2]
  * resonance energy
  * `E_r`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-38.1]
  * cross section
  * `σ`
  * `m²`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-38.2]
  * total cross section
  * `σ_tot`
  * `m²`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-39]
  * direction distribution of cross section
  * `σ_Ω`
  * `m²·sr⁻¹`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-40]
  * energy distribution of cross section
  * `σ_E`
  * `m²/J`
  * `M⁻¹·T²`
*
  * {bpref "def_part10_catalogued_kind"}[10-41]
  * direction and energy distribution of cross section
  * `σ_ΩE`
  * `m²/(J·sr)`
  * `M⁻¹·T²`
*
  * {bpref "def_part10_catalogued_kind"}[10-42.1]
  * macroscopic cross section
  * `Σ`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-42.2]
  * macroscopic total cross section
  * `Σ_tot`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-43]
  * particle fluence
  * `Φ`
  * `m⁻²`
  * `L⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-44]
  * particle fluence rate
  * `Φ̇`
  * `m⁻²·s⁻¹`
  * `L⁻²·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-45]
  * radiant energy
  * `R`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-46]
  * energy fluence
  * `Ψ`
  * `eV/m²`
  * `M·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-47]
  * energy fluence rate
  * `Ψ̇`
  * `W/m²`
  * `M·T⁻³`
*
  * {bpref "def_part10_catalogued_kind"}[10-48]
  * particle current density
  * `J`
  * `m⁻²·s⁻¹`
  * `L⁻²·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-49]
  * linear attenuation coefficient
  * `μ`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "thm_part10_relations"}[10-50]
  * mass attenuation coefficient
  * `μ_m`
  * `kg⁻¹·m²`
  * `M⁻¹·L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-51]
  * molar attenuation coefficient
  * `μ_c`
  * `m²·mol⁻¹`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-52]
  * atomic attenuation coefficient
  * `μ_a`
  * `m²`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-53]
  * half-value thickness
  * `d_½`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-54]
  * total linear stopping power
  * `S`
  * `eV/m`
  * `M·L·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-55]
  * total mass stopping power
  * `S_m`
  * `eV·m²/kg`
  * `L⁴·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-56]
  * mean linear range
  * `R`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-57]
  * mean mass range
  * `R_ρ`
  * `kg·m⁻²`
  * `M·L⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-58]
  * linear ionization
  * `N_il`
  * `m⁻¹`
  * `L⁻¹`
*
  * {bpref "thm_part10_dim_one"}[10-59]
  * total ionization
  * `N_i`
  * `1`
  * `1`
*
  * {bpref "def_part10_catalogued_kind"}[10-60]
  * average energy loss per elementary charge produced
  * `W_i`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-61]
  * mobility
  * `μ`
  * `m²/(V·s)`
  * `M⁻¹·T·C`
*
  * {bpref "def_part10_catalogued_kind"}[10-62.1]
  * particle number density
  * `n`
  * `m⁻³`
  * `L⁻³`
*
  * {bpref "def_part10_catalogued_kind"}[10-62.2]
  * ion number density
  * `n⁺`
  * `m⁻³`
  * `L⁻³`
*
  * {bpref "def_part10_catalogued_kind"}[10-63]
  * recombination coefficient
  * `α`
  * `m³·s⁻¹`
  * `L³·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-64]
  * diffusion coefficient
  * `D`
  * `m²·s⁻¹`
  * `L²·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-65]
  * diffusion coefficient for fluence rate
  * `D_φ`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-66]
  * particle source density
  * `S`
  * `m⁻³·s⁻¹`
  * `L⁻³·T⁻¹`
*
  * {bpref "def_part10_catalogued_kind"}[10-67]
  * slowing-down density
  * `q`
  * `m⁻³·s⁻¹`
  * `L⁻³·T⁻¹`
*
  * {bpref "thm_part10_dim_one"}[10-68]
  * resonance escape probability
  * `p`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-69]
  * lethargy
  * `u`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-70]
  * average logarithmic energy decrement
  * `ζ`
  * `1`
  * `1`
*
  * {bpref "def_part10_catalogued_kind"}[10-71]
  * mean free path
  * `l`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-72.1]
  * slowing-down area
  * `L²_s`
  * `m²`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-72.2]
  * diffusion area
  * `L²`
  * `m²`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-72.3]
  * migration area
  * `M²`
  * `m²`
  * `L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-73.1]
  * slowing-down length
  * `L_s`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-73.2]
  * diffusion length
  * `L`
  * `m`
  * `L`
*
  * {bpref "def_part10_catalogued_kind"}[10-73.3]
  * migration length
  * `M`
  * `m`
  * `L`
*
  * {bpref "thm_part10_dim_one"}[10-74.1]
  * neutron yield per fission
  * `ν`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-74.2]
  * neutron yield per absorption
  * `η`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-75]
  * fast fission factor
  * `ε`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-76]
  * thermal utilization factor
  * `f`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-77]
  * non-leakage probability
  * `Λ`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-78.1]
  * multiplication factor
  * `k`
  * `1`
  * `1`
*
  * {bpref "thm_part10_dim_one"}[10-78.2]
  * infinite multiplication factor
  * `k∞`
  * `1`
  * `1`
*
  * {bpref "def_part10_catalogued_kind"}[10-79]
  * reactor time constant
  * `T`
  * `s`
  * `T`
*
  * {bpref "def_part10_catalogued_kind"}[10-80.1]
  * energy imparted
  * `ε`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-80.2]
  * mean energy imparted
  * `ε̄`
  * `eV`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part10_collision"}[10-81.1]
  * absorbed dose
  * `D`
  * `Gy`
  * `L²·T⁻²`
*
  * {bpref "thm_part10_collision"}[10-81.2]
  * specific energy imparted
  * `z`
  * `Gy`
  * `L²·T⁻²`
*
  * {bpref "thm_part10_dim_one"}[10-82]
  * quality factor
  * `Q`
  * `1`
  * `1`
*
  * {bpref "thm_part10_collision"}[10-83.1]
  * dose equivalent
  * `H`
  * `Sv`
  * `L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-83.2]
  * dose equivalent rate
  * `Ḣ`
  * `Sv/s`
  * `L²·T⁻³`
*
  * {bpref "thm_part10_relations"}[10-84]
  * absorbed-dose rate
  * `Ḋ`
  * `Gy/s`
  * `L²·T⁻³`
*
  * {bpref "def_part10_catalogued_kind"}[10-85]
  * linear energy transfer
  * `L_Δ`
  * `eV/m`
  * `M·L·T⁻²`
*
  * {bpref "thm_part10_collision"}[10-86.1]
  * kerma
  * `K`
  * `Gy`
  * `L²·T⁻²`
*
  * {bpref "def_part10_catalogued_kind"}[10-86.2]
  * kerma rate
  * `K̇`
  * `Gy/s`
  * `L²·T⁻³`
*
  * {bpref "thm_part10_relations"}[10-87]
  * mass energy-transfer coefficient
  * `μ_tr/ρ`
  * `kg⁻¹·m²`
  * `M⁻¹·L²`
*
  * {bpref "def_part10_catalogued_kind"}[10-88]
  * exposure
  * `X`
  * `C/kg`
  * `M⁻¹·C`
*
  * {bpref "def_part10_catalogued_kind"}[10-89]
  * exposure rate
  * `Ẋ`
  * `C/(kg·s)`
  * `M⁻¹·T⁻¹·C`
:::
