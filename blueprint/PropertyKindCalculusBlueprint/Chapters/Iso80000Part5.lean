import Verso
import VersoManual
import VersoBlueprint
-- The Part-5 nodes link real declarations (dimensioned kinds, checked dimensional
-- facts, the scale-type distinction, the energy-family specialization lattice, the
-- entropy/heat-capacity collision, and the cross-part defining relations), so this
-- chapter imports the Part-5 modules of the `Iso80000` library (PhysLib-backed).
import PropertyKindCalculus.Iso80000.Part5
import PropertyKindCalculus.Iso80000.Part5.DefiningRelations

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "ISO 80000-5 — Thermodynamics" =>

The third part specified in full is ISO 80000-5, _Thermodynamics_. Every item — all
of 5-1 … 5-36, including every sub-suffixed item (5-3.1 … 5-3.3, 5-5.1/5-5.2,
5-6.1/5-6.2, 5-10.1/5-10.2, 5-16.1 … 5-16.4, 5-17.1/5-17.2, 5-20.1 … 5-20.5,
5-21.1 … 5-21.5, 5-25.1/5-25.2) — is catalogued: the temperatures, the expansion and
pressure coefficients, heat and the heat-transfer quantities, the heat capacities and
entropy, the energy family (the thermodynamic potentials), the specific energies, the
Massieu and Planck functions, efficiency, and the humidity quantities — each carrying
its exact source as data: the part, the printed item designation, the principal
quantity symbol, and the coherent SI unit symbol. Only *citation locators* are
recorded; no normative content (definitions, remarks) from the licensed standard is
reproduced. The defining _mathematics_ of selected remarks is formalized in the
sibling module `Part5.DefiningRelations`.

Thermodynamics brings the one axis Parts 3 and 4 could not show, and sharpens the two
the calculus already pressed. It introduces the temperature base quantity `Θ`, and
with it the _scale-type_ distinction — thermodynamic temperature is ratio-scale, but
Celsius temperature, of the very same dimension, is only interval-scale (requirement
_R6_, here on the standard). It holds the textbook _entropy-versus-heat-capacity_
dimension collision (both `J/K`, down to the same unit string). And item 5-20 lays out
the thermodynamic potentials — internal energy, enthalpy, the Helmholtz and Gibbs
energies — as a specialization lattice over energy, mirroring Part 3's length family
and Part 4's force family.

# Quantity-kinds and units of ISO 80000-5

:::group "iso80000_part5"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, now over the temperature generator `Θ`, so the standard's dimensional facts
— heat is `M·L²·T⁻²`, entropy `M·L²·T⁻²·Θ⁻¹`, a linear expansion coefficient `Θ⁻¹` — are
_checked computations_ rather than annotations. Each unit is a
{uses "def_metrologicalUnit"}[metrological unit] of its kind; commensurability is a
type-level fact, so a kelvin and a joule are not interchangeable.
:::

:::definition "def_part5_catalogued_kind" (parent := "iso80000_part5") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "5-20.3"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with
the kind as data, so the source of each definition can be rendered or audited downstream
rather than kept in a comment.
:::

:::proof "def_part5_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `ISO 80000-5, Second edition, 2019-08 item 5-18`. The `catalogue` lists all 54
items in item order — thermodynamic temperature (5-1), heat (5-6.1), entropy (5-18),
the thermodynamic potentials (5-20.1 … 5-20.5), the dew-point temperature (5-36), … —
each paired with its coherent SI unit symbol.
:::

:::theorem "thm_part5_entropy_dim" (parent := "iso80000_part5") (lean := "PropertyKindCalculus.Iso80000.Part5.entropy_dim_temperature") (tags := "proved") (effort := "small")
*Entropy is `M·L²·T⁻²·Θ⁻¹` (item 5-18).* The catalogued entropy kind carries
temperature-exponent minus one in PhysLib's dimension group — the standard's
dimensional statement reproduced as a checked computation over the temperature
generator `Θ`, not an annotation. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part5_entropy_dim"
Proved as `entropy_dim_temperature : entropy.dim.temperature = -1` in the `Iso80000`
library, discharged by `norm_num` over the PhysLib dimension lemmas for the temperature
generator. The companions `heatCapacity_dim_temperature = -1`, `heat_dim_length = 2`
(item 5-6.1), and `linearExpansionCoefficient_dim_temperature = -1` (item 5-3.1) record
the rest of the thermodynamic algebra.
:::

:::theorem "thm_part5_kelvin_joule" (parent := "iso80000_part5") (lean := "PropertyKindCalculus.Iso80000.Part5.kelvin_joule_not_commensurable") (tags := "proved") (effort := "small")
*A kelvin and a joule are not commensurable.* Thermodynamic temperature and energy are
distinct kinds, so their units cannot be compared by ratio — a type-level fact, not a
runtime check. Uses {uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part5_kelvin_joule"
Proved as `kelvin_joule_not_commensurable : ¬ kelvin.Commensurable joule` by unfolding
`Commensurable` to the underlying kinds and `decide`. The kelvin and the joule are each
`WellFormed` (thermodynamic temperature and energy are ratio-scale).
:::

# Temperature: one dimension, two scales

ISO 80000-5 lists _thermodynamic temperature_ (5-1) and _Celsius temperature_ (5-2) as
separate items of the _same_ dimension `Θ`. But they are not the same kind of quantity.
Thermodynamic temperature has an absolute zero, so it is _ratio-scale_: ratios of
temperatures are meaningful, and the kelvin admits `×` and `÷`. Celsius temperature is
measured from the arbitrary zero of the ice point (`t = T − T₀`), so it is
_interval-scale_: only its _differences_ are meaningful, and a ratio of Celsius
temperatures is not a defined operation. A dimension-only model sees one type, "a real
number of degrees", for both.

This is requirement _R6_ — the scale type fixes which operations are even _defined_ —
now on the real standard, the axis Part 3 and Part 4 (every quantity ratio-scale) could
not exercise. The two temperatures are distinct kinds separated _neither_ by dimension
_nor_ by an examination principle, but by their _scale type_ alone.

:::group "iso80000_part5_scale"
The kelvin and the degree Celsius are _both_ well-formed
{uses "def_metrologicalUnit"}[metrological units] — a kind bears a unit from the
differential (interval) scale upward, not only from ratio scale, so the degree Celsius
is a legitimate unit even though `×`,`÷` are undefined on Celsius temperatures. What
separates the two kinds is the {uses "def_scaleType"}[scale type]: ratio versus interval.
:::

:::theorem "thm_part5_celsius_scale" (parent := "iso80000_part5_scale") (lean := "PropertyKindCalculus.Iso80000.Part5.celsiusTemperature_not_allowsRatio") (tags := "proved") (effort := "small")
*Celsius temperature does not admit `×`,`÷`.* It is interval-scale (an arbitrary zero at
the ice point), so a ratio of Celsius temperatures is not a meaningful operation — the
scale layer refuses it where the dimension would not. Thermodynamic temperature, being
ratio-scale, does admit it. Uses {uses "def_scaleType"}[the scale type].
:::

:::proof "thm_part5_celsius_scale"
`celsiusTemperature_not_allowsRatio : ¬ ScaleType.AllowsRatio celsiusTemperature.kind.scale`,
with the companion `thermodynamicTemperature_allowsRatio` for the ratio case. The degree
Celsius is nonetheless `WellFormed` (`degreeCelsius_wellFormed`, via the differential
scale), and `thermodynamicTemperature_ne_celsiusTemperature` (a `decide`) records that
the two are distinct kinds.
:::

:::theorem "thm_part5_scale_collision" (parent := "iso80000_part5_scale") (lean := "PropertyKindCalculus.Iso80000.Part5.iso80000_5_scale_collision") (tags := "proved") (effort := "small")
*The scale disambiguation, on the standard.* There exist distinct ISO 80000-5 kinds with
the same dimension `Θ` that are separated by scale type alone — thermodynamic temperature
(ratio) and Celsius temperature (interval) witness it. Neither the dimension nor an
examination principle tells them apart; the scale layer does. This is requirement R6 on
the standard. Uses {uses "def_scaleType"}[the scale type].
:::

:::proof "thm_part5_scale_collision"
`iso80000_5_scale_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
a.kind.scale ≠ b.kind.scale`, witnessed by `⟨thermodynamicTemperature, celsiusTemperature, …⟩`
with reflexivity on the dimension and a `decide` on the differing scales. Axiom-free.
:::

# The energy family: distinguishing kinds by defining construction

ISO 80000-5 item 5-20 lists _energy_ `<thermodynamics>` (5-20.1) as a genus and the
_thermodynamic potentials_ — internal energy (5-20.2), enthalpy (5-20.3), the Helmholtz
energy (5-20.4), and the Gibbs energy (5-20.5) — as items beneath it. Every one has
dimension `M·L²·T⁻²` and ratio scale. The standard distinguishes them only in _prose_, by
_which thermodynamic variables are natural to the potential_: internal energy is a state
function of `S, V, N`; the enthalpy is `H = U + pV`; the Helmholtz energy is `A = U − TS`;
the Gibbs energy is `G = H − TS`. A dimension-only model sees one type, "a real number of
joules", for all of them — and cannot even separate them from a Part-4 torque.

This is requirement _R2_ again, now on the thermodynamic potentials — the pattern Part 3
set on the length family and Part 4 on the force family. Item 5-20.1 is the broad genus;
each later item is a _species_ of energy, distinguished *not by fiat* but by an explicit
defining construction (Dybkær's examination principle, §7.5). The species are then
provably distinct kinds while remaining _mutually comparable_ as energies.

:::group "iso80000_part5_energy"
The energy species are individuated by an {uses "def_examination"}[examination principle]
— here the potential's defining construction — and arranged as a
{uses "def_specializes"}[specialization] lattice over the general energy kind. The
sharpest case is the Helmholtz versus the Gibbs energy: both "free energies" of the same
dimension, they are nonetheless different kinds — and the calculus proves it from their
differing natural variables, not from a naming convention.
:::

:::definition "def_part5_energy_species" (parent := "iso80000_part5_energy") (lean := "PropertyKindCalculus.Iso80000.Part5.energySpecies")
An _energy species_ is a ratio-scale {uses "def_quantity"}[quantity]-kind of dimension
`M·L²·T⁻²` carrying an {uses "def_examination"}[examination principle] — this work's own
terse descriptor of the defining construction that distinguishes it (natural in S-V-N,
in S-p, in T-V, in T-p), never the standard's normative definition. Internal energy, the
enthalpy, and the Helmholtz and Gibbs energies are all species of the general energy kind
(item 5-20.1).
:::

:::proof "def_part5_energy_species"
`energySpecies id p := { kind := { id, scale := .ratio, examPrinciple := some p.id },
dim := TDim.energy }`. The general `energy` carries no examination principle; the
direct-parent edges of the family are collected in an `Edge` relation, each species an
edge to `energy` (mirroring the standard's "energy (item 5-20.1) … given by …").
:::

:::theorem "thm_part5_helmholtz_gibbs" (parent := "iso80000_part5_energy") (lean := "PropertyKindCalculus.Iso80000.Part5.helmholtzEnergy_ne_gibbsEnergy") (tags := "proved") (effort := "small")
*The Helmholtz and Gibbs energies are distinct kinds — by defining construction, not by
fiat.* They share dimension `M·L²·T⁻²` and are both "free energies", yet are different
kinds _because they are defined by different natural variables_ (`A = U − TS`, natural in
T,V; `G = H − TS`, natural in T,p), proved through `distinct_of_examPrinciple` (§7.5). This
is the thermodynamic-potential analogue of width ≠ distance and static ≠ kinetic friction
force. Uses {uses "def_examination"}[the examination principle].
:::

:::proof "thm_part5_helmholtz_gibbs"
`helmholtzEnergy_ne_gibbsEnergy : helmholtzEnergy.kind ≠ gibbsEnergy.kind`, from
`KindOfProperty.distinct_of_examPrinciple` applied to the differing principles `natural-T-V`
and `natural-T-p` (a `decide` on the `Option String` links). The companions
`internalEnergy_ne_enthalpy` and `internalEnergy_ne_energy` separate the other species, and
`internalEnergy_examinedBy` checks the kind-to-principle link. Axiom-free.
:::

:::theorem "thm_part5_energy_comparable" (parent := "iso80000_part5_energy") (lean := "PropertyKindCalculus.Iso80000.Part5.helmholtzEnergy_gibbsEnergy_comparable") (tags := "proved") (effort := "small")
*Comparability is preserved.* The Helmholtz and Gibbs energies, though distinct kinds,
remain _mutually comparable_ — they share the super-kind energy, so combining them is
possible but only via an explicit up-cast, never silently. The companion
`internalEnergy_specializes_energy` records that internal energy specializes energy. Uses
{uses "def_specializes"}[specialization].
:::

:::proof "thm_part5_energy_comparable"
`helmholtzEnergy_gibbsEnergy_comparable : MutuallyComparable Edge helmholtzEnergy.kind
gibbsEnergy.kind`, with witness `energy.kind`, each species reaching it by one edge.
Axiom-free.
:::

# Dimension does not classify; the kind does — the entropy/heat-capacity case

Part 5 holds another textbook dimension collision. _Entropy_ (5-18) and _heat capacity_
(5-15) are _both_ `M·L²·T⁻²·Θ⁻¹` — the joule per kelvin — yet they are distinct kinds, and
the collision is unusually sharp: their units carry not only the same dimension but the
_same symbol_, "J/K", and are still not commensurable, because their kinds differ. The
Massieu (5-22) and Planck (5-23) functions join them at `J/K`; specific entropy (5-19),
specific heat capacity (5-16.1), and the specific gas constant (5-26) collide the same way
at `J/(kg·K)`; and the humidity ratios and fractions (5-29 … 5-35), with the ratio of
specific heats and the efficiencies, fill out the dimension-one family.

:::group "iso80000_part5_collision"
These are the dimension-disambiguation capstone, on _standard_ quantities: the
{uses "def_dim"}[dimension map] identifies the members of each pair, while the kind layer
keeps them apart, both as kinds and as {uses "def_metrologicalUnit"}[units] — here even
when the units share a symbol.
:::

:::theorem "thm_part5_entropy_heatCapacity" (parent := "iso80000_part5_collision") (lean := "PropertyKindCalculus.Iso80000.Part5.iso80000_5_dim_collision") (tags := "proved") (effort := "small")
*Entropy is not heat capacity, though both are `M·L²·T⁻²·Θ⁻¹`.* There exist distinct
ISO 80000-5 kinds with the same dimension — entropy and heat capacity witness it. No
dimension-only type system can separate them; the kind layer does. This is the textbook
thermodynamic case that a dimension does not classify a quantity. Uses
{uses "def_dim"}[the dimension map].
:::

:::proof "thm_part5_entropy_heatCapacity"
`iso80000_5_dim_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim`,
witnessed by `⟨entropy, heatCapacity, …⟩` with `entropy_ne_heatCapacity` (a `decide`) and
reflexivity. The companion `specificEntropy_ne_specificHeatCapacity` is the `J/(kg·K)`
case. Axiom-free.
:::

:::theorem "thm_part5_jk_unit" (parent := "iso80000_part5_collision") (lean := "PropertyKindCalculus.Iso80000.Part5.entropy_heatCapacity_unit_not_commensurable") (tags := "proved") (effort := "small")
*The entropy "J/K" is not the heat-capacity "J/K".* The units of entropy and heat capacity
carry the same symbol and the same dimension `M·L²·T⁻²·Θ⁻¹`, yet are not commensurable —
the sharpest form of the rule that neither a dimension nor a unit string determines a kind.
Uses {uses "def_metrologicalUnit"}[metrological units].
:::

:::proof "thm_part5_jk_unit"
`entropy_heatCapacity_unit_not_commensurable : ¬ joulePerKelvinEntropy.Commensurable
joulePerKelvinHeatCapacity` by unfolding to the underlying kinds and `decide` (entropy's
kind differs from the heat-capacity kind, although both units are written "J/K").
:::

:::theorem "thm_part5_dim_one" (parent := "iso80000_part5_collision") (lean := "PropertyKindCalculus.Iso80000.Part5.iso80000_5_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard.* There exist distinct ISO 80000-5 kinds
with the same dimension one — the ratio of specific heat capacities and the efficiency
witness it, alongside the isentropic exponent and the humidity ratios and fractions.
Dimension cannot separate them; the kind layer does. Uses {uses "def_dim"}[the dimension
map].
:::

:::proof "thm_part5_dim_one"
`iso80000_5_dim_one_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim
∧ a.dim = 1`, witnessed by `⟨ratioOfSpecificHeatCapacities, efficiency, …⟩` with
`ratioOfSpecificHeatCapacities_ne_efficiency` (a `decide`) and reflexivity. Axiom-free.
:::

# The algebraic Remarks as kind-laws: thermodynamics built from the earlier parts

Many Part-5 remarks state a quantity's defining relation _algebraically_ — and, in
thermodynamics, the other quantities are often from _earlier parts_ (mass from
ISO 80000-4, area from ISO 80000-3) or from temperature, the base quantity this part
introduces. Heat capacity is added heat per temperature (5-15); specific heat capacity is
heat capacity / mass (5-16.1); specific entropy is entropy / mass (5-19); the density of
heat flow rate is heat flow rate / area (5-8); thermal conductance is `1/R` (5-13); the
ratio of specific heats is `cp/cV` (5-17.1). Each is formalized as an R12 kind-law over
the catalogued kinds, several composing a Part-5 kind out of an earlier part's kinds.

:::group "iso80000_part5_relations"
The {uses "def_quotient_kind"}[quotient] and {uses "def_reciprocal_kind"}[reciprocal]
families carry the kind-laws. Three payoffs on the standard's own remarks: the cross-part
dependency structure of the ISQ is made explicit; the _dimension follows from the
relation_ as a checked computation; and a verified-by-construction quantity carries its
classification certificate.
:::

:::theorem "thm_part5_specific_heat" (parent := "iso80000_part5_relations") (lean := "PropertyKindCalculus.Iso80000.Part5.DefiningRelations.specificHeatCapacityOf_isQuotient") (tags := "proved") (effort := "small")
*Specific heat capacity is heat capacity / mass — a verified, cross-part construction.* A
specific heat capacity built as the quotient of a heat capacity (Part 5) by a mass (Part 4)
carries its quotient certificate by construction, over the `ℝ` carrier, and canonicity makes
the certificate determine the quantity. Uses {uses "def_quotient_kind"}[the quotient kind-law].
:::

:::proof "thm_part5_specific_heat"
`specificHeatCapacityOf c m := Quantity.div specificHeatCapacity_quot_heatCapacity_mass c m`,
and `specificHeatCapacityOf_isQuotient` is `rfl`; `specificHeatCapacity_certificate_canonical`
is `eq_div_of_isQuotient`. The kind-law `specificHeatCapacity_quot_heatCapacity_mass :
QuotientKind heatCapacity.kind Part4.mass.kind specificHeatCapacity.kind` is `⟨rfl, rfl, rfl⟩`,
and `specificHeatCapacity_dim_from_heatCapacity_mass` checks `L²·T⁻²·Θ⁻¹` follows from the
relation. The same families give `densityOfHeatFlowRateOf` (= heat flow rate / area) and
`thermalConductanceOf` (= the reciprocal of thermal resistance).
:::

:::theorem "thm_part5_ratio" (parent := "iso80000_part5_relations") (lean := "PropertyKindCalculus.Iso80000.Part5.DefiningRelations.ratio_dim_from_specific_heats") (tags := "proved") (effort := "small")
*The ratio of specific heats is dimension one because it is a ratio of two specific heat
capacities.* From the remark `γ = cp/cV`, the specific heat capacities cancel and the
dimension is _computed_ to be one — not stipulated, the thermodynamic analogue of the
plane angle being a ratio of two lengths and the efficiency a ratio of two powers. Yet the
ratio remains a distinct kind from every other dimension-one quantity (the collision
capstone above). Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part5_ratio"
`ratio_dim_from_specific_heats : ratioOfSpecificHeatCapacities.dim =
specificHeatCapacityConstantPressure.dim / specificHeatCapacityConstantVolume.dim`, by
reducing both sides via `div_self'` (`a / a = 1`). The kind-law
`ratioOfSpecificHeatCapacities_quot_cp_cV` is `⟨rfl, rfl, rfl⟩`.
:::

# Item index — ISO 80000-5

Every catalogued item of ISO 80000-5, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it. Each item number links to the formalized result it participates in — the
scale-type distinction, the energy-family lattice, the entropy/heat-capacity collision, a
cross-part defining relation, or the catalogue itself. Symbols and unit strings are
*citation locators*; nothing normative is reproduced.

:::table +header (align := left)
*
  * Item
  * Quantity
  * Symbol
  * Unit
  * Dimension
*
  * {bpref "thm_part5_scale_collision"}[5-1]
  * thermodynamic temperature
  * `T`
  * `K`
  * `Θ`
*
  * {bpref "thm_part5_scale_collision"}[5-2]
  * Celsius temperature
  * `t`
  * `°C`
  * `Θ`
*
  * {bpref "thm_part5_entropy_dim"}[5-3.1]
  * linear expansion coefficient
  * `α_l`
  * `K⁻¹`
  * `Θ⁻¹`
*
  * {bpref "thm_part5_entropy_dim"}[5-3.2]
  * cubic expansion coefficient
  * `α_V`
  * `K⁻¹`
  * `Θ⁻¹`
*
  * {bpref "thm_part5_entropy_dim"}[5-3.3]
  * relative pressure coefficient
  * `α_p`
  * `K⁻¹`
  * `Θ⁻¹`
*
  * {bpref "def_part5_catalogued_kind"}[5-4]
  * pressure coefficient
  * `β`
  * `Pa/K`
  * `M·L⁻¹·T⁻²·Θ⁻¹`
*
  * {bpref "def_part5_catalogued_kind"}[5-5.1]
  * isothermal compressibility
  * `ϰ_T`
  * `Pa⁻¹`
  * `M⁻¹·L·T²`
*
  * {bpref "def_part5_catalogued_kind"}[5-5.2]
  * isentropic compressibility
  * `ϰ_S`
  * `Pa⁻¹`
  * `M⁻¹·L·T²`
*
  * {bpref "thm_part5_entropy_heatCapacity"}[5-6.1]
  * heat
  * `Q`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "def_part5_catalogued_kind"}[5-6.2]
  * latent heat
  * `Q`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part5_specific_heat"}[5-7]
  * heat flow rate
  * `Φ`
  * `W`
  * `M·L²·T⁻³`
*
  * {bpref "thm_part5_specific_heat"}[5-8]
  * density of heat flow rate
  * `q`
  * `W/m²`
  * `M·T⁻³`
*
  * {bpref "def_part5_catalogued_kind"}[5-9]
  * thermal conductivity
  * `λ`
  * `W/(m·K)`
  * `M·L·T⁻³·Θ⁻¹`
*
  * {bpref "thm_part5_specific_heat"}[5-10.1]
  * coefficient of heat transfer
  * `K`
  * `W/(m²·K)`
  * `M·T⁻³·Θ⁻¹`
*
  * {bpref "def_part5_catalogued_kind"}[5-10.2]
  * surface coefficient of heat transfer
  * `h`
  * `W/(m²·K)`
  * `M·T⁻³·Θ⁻¹`
*
  * {bpref "thm_part5_specific_heat"}[5-11]
  * thermal insulance
  * `M`
  * `m²·K/W`
  * `M⁻¹·T³·Θ`
*
  * {bpref "def_part5_catalogued_kind"}[5-12]
  * thermal resistance
  * `R`
  * `K/W`
  * `M⁻¹·L⁻²·T³·Θ`
*
  * {bpref "thm_part5_specific_heat"}[5-13]
  * thermal conductance
  * `G`
  * `W/K`
  * `M·L²·T⁻³·Θ⁻¹`
*
  * {bpref "def_part5_catalogued_kind"}[5-14]
  * thermal diffusivity
  * `a`
  * `m²/s`
  * `L²·T⁻¹`
*
  * {bpref "thm_part5_entropy_heatCapacity"}[5-15]
  * heat capacity
  * `C`
  * `J/K`
  * `M·L²·T⁻²·Θ⁻¹`
*
  * {bpref "thm_part5_specific_heat"}[5-16.1]
  * specific heat capacity
  * `c`
  * `J/(kg·K)`
  * `L²·T⁻²·Θ⁻¹`
*
  * {bpref "thm_part5_specific_heat"}[5-16.2]
  * specific heat capacity at constant pressure
  * `c_p`
  * `J/(kg·K)`
  * `L²·T⁻²·Θ⁻¹`
*
  * {bpref "thm_part5_ratio"}[5-16.3]
  * specific heat capacity at constant volume
  * `c_V`
  * `J/(kg·K)`
  * `L²·T⁻²·Θ⁻¹`
*
  * {bpref "def_part5_catalogued_kind"}[5-16.4]
  * specific heat capacity at saturated vapour pressure
  * `c_sat`
  * `J/(kg·K)`
  * `L²·T⁻²·Θ⁻¹`
*
  * {bpref "thm_part5_ratio"}[5-17.1]
  * ratio of specific heat capacities
  * `γ`
  * `1`
  * `1`
*
  * {bpref "thm_part5_dim_one"}[5-17.2]
  * isentropic exponent
  * `ϰ`
  * `1`
  * `1`
*
  * {bpref "thm_part5_entropy_heatCapacity"}[5-18]
  * entropy
  * `S`
  * `J/K`
  * `M·L²·T⁻²·Θ⁻¹`
*
  * {bpref "thm_part5_specific_heat"}[5-19]
  * specific entropy
  * `s`
  * `J/(kg·K)`
  * `L²·T⁻²·Θ⁻¹`
*
  * {bpref "def_part5_energy_species"}[5-20.1]
  * energy
  * `E`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part5_helmholtz_gibbs"}[5-20.2]
  * internal energy
  * `U`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part5_helmholtz_gibbs"}[5-20.3]
  * enthalpy
  * `H`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part5_helmholtz_gibbs"}[5-20.4]
  * Helmholtz energy
  * `A`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part5_helmholtz_gibbs"}[5-20.5]
  * Gibbs energy
  * `G`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "def_part5_catalogued_kind"}[5-21.1]
  * specific energy
  * `e`
  * `J/kg`
  * `L²·T⁻²`
*
  * {bpref "def_part5_catalogued_kind"}[5-21.2]
  * specific internal energy
  * `u`
  * `J/kg`
  * `L²·T⁻²`
*
  * {bpref "def_part5_catalogued_kind"}[5-21.3]
  * specific enthalpy
  * `h`
  * `J/kg`
  * `L²·T⁻²`
*
  * {bpref "def_part5_catalogued_kind"}[5-21.4]
  * specific Helmholtz energy
  * `a`
  * `J/kg`
  * `L²·T⁻²`
*
  * {bpref "def_part5_catalogued_kind"}[5-21.5]
  * specific Gibbs energy
  * `g`
  * `J/kg`
  * `L²·T⁻²`
*
  * {bpref "thm_part5_entropy_heatCapacity"}[5-22]
  * Massieu function
  * `J`
  * `J/K`
  * `M·L²·T⁻²·Θ⁻¹`
*
  * {bpref "thm_part5_entropy_heatCapacity"}[5-23]
  * Planck function
  * `Y`
  * `J/K`
  * `M·L²·T⁻²·Θ⁻¹`
*
  * {bpref "def_part5_catalogued_kind"}[5-24]
  * Joule-Thomson coefficient
  * `μ_JT`
  * `K/Pa`
  * `M⁻¹·L·T²·Θ`
*
  * {bpref "thm_part5_dim_one"}[5-25.1]
  * efficiency
  * `η`
  * `1`
  * `1`
*
  * {bpref "thm_part5_dim_one"}[5-25.2]
  * maximum efficiency
  * `η_max`
  * `1`
  * `1`
*
  * {bpref "thm_part5_specific_heat"}[5-26]
  * specific gas constant
  * `R_s`
  * `J/(kg·K)`
  * `L²·T⁻²·Θ⁻¹`
*
  * {bpref "def_part5_catalogued_kind"}[5-27]
  * mass concentration of water
  * `w`
  * `kg/m³`
  * `M·L⁻³`
*
  * {bpref "def_part5_catalogued_kind"}[5-28]
  * mass concentration of water vapour
  * `v`
  * `kg/m³`
  * `M·L⁻³`
*
  * {bpref "thm_part5_dim_one"}[5-29]
  * mass ratio of water to dry matter
  * `u`
  * `1`
  * `1`
*
  * {bpref "thm_part5_dim_one"}[5-30]
  * mass ratio of water vapour to dry gas
  * `r`
  * `1`
  * `1`
*
  * {bpref "thm_part5_dim_one"}[5-31]
  * mass fraction of water
  * `w_H2O`
  * `1`
  * `1`
*
  * {bpref "thm_part5_dim_one"}[5-32]
  * mass fraction of dry matter
  * `w_d`
  * `1`
  * `1`
*
  * {bpref "thm_part5_dim_one"}[5-33]
  * relative humidity
  * `φ`
  * `1`
  * `1`
*
  * {bpref "thm_part5_dim_one"}[5-34]
  * relative mass concentration of vapour
  * `φ`
  * `1`
  * `1`
*
  * {bpref "thm_part5_dim_one"}[5-35]
  * relative mass ratio of vapour
  * `ψ`
  * `1`
  * `1`
*
  * {bpref "thm_part5_scale_collision"}[5-36]
  * dew-point temperature
  * `T_d`
  * `K`
  * `Θ`
:::
