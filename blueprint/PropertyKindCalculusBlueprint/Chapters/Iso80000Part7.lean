import Verso
import VersoManual
import VersoBlueprint
-- The Part-7 nodes link real declarations (dimensioned kinds over the radiation
-- reductions, the radiant/luminous/photon trios, the scale-spanning candela collision,
-- the steradian collision, the dimension-one family, and the defining-relation
-- kind-laws), so this chapter imports the Part-7 modules of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part7
import PropertyKindCalculus.Iso80000.Part7.DefiningRelations
import PropertyKindCalculusBlueprint.ItemIndex

open Verso.Genre
open Verso.Genre.Manual
open Informal

open PropertyKindCalculusBlueprint.ItemIndex

/-- Default blueprint node for ISO/IEC 80000-7 item-index rows (editorial). -/
def part7Default : String := "def_part7_catalogued_kind"

/-- Per-item blueprint cross-reference overrides for the ISO/IEC 80000-7 item
index (editorial; items not listed link to `part7Default`). Every other column
is generated from `PropertyKindCalculus.Iso80000.Part7.catalogue`. -/
def part7Refs : List (String × String) := [
  ("7-1.2", "thm_part7_dim_one"),
  ("7-2.1", "thm_part7_candela_power"),
  ("7-4.1", "thm_part7_collision"),
  ("7-5.1", "thm_part7_collision"),
  ("7-6.1", "thm_part7_collision"),
  ("7-7.1", "thm_part7_irradiance"),
  ("7-10.1", "thm_part7_dim_one"),
  ("7-10.2", "thm_part7_dim_one"),
  ("7-11.1", "thm_part7_efficacy"),
  ("7-11.2", "thm_part7_efficacy"),
  ("7-11.3", "thm_part7_efficacy"),
  ("7-11.4", "thm_part7_efficacy"),
  ("7-12", "thm_part7_candela_power"),
  ("7-13", "thm_part7_collision"),
  ("7-14", "thm_part7_candela_power"),
  ("7-15", "thm_part7_collision"),
  ("7-16", "thm_part7_collision"),
  ("7-19.1", "thm_part7_dim_one"),
  ("7-19.2", "thm_part7_candela_power"),
  ("7-20", "thm_part7_trio"),
  ("7-27.1", "thm_part7_dim_one"),
  ("7-27.2", "thm_part7_dim_one"),
  ("7-28.1", "thm_part7_dim_one"),
  ("7-28.2", "thm_part7_dim_one"),
  ("7-30.1", "thm_part7_dim_one"),
  ("7-30.2", "thm_part7_dim_one"),
  ("7-31.1", "thm_part7_dim_one"),
  ("7-31.2", "thm_part7_dim_one"),
  ("7-31.3", "thm_part7_dim_one"),
  ("7-31.4", "thm_part7_dim_one"),
  ("7-31.5", "thm_part7_dim_one"),
  ("7-31.6", "thm_part7_dim_one"),
  ("7-32.1", "thm_part7_dim_one"),
  ("7-32.2", "thm_part7_dim_one"),
  ("7-33.1", "thm_part7_dim_one"),
  ("7-33.2", "thm_part7_dim_one"),
  ("7-34", "thm_part7_dim_one"),
  ("7-37", "thm_part7_candela_power")
]

/-- The ISO/IEC 80000-7 item index, generated live from the catalogue. -/
def part7IndexTable : DocTable :=
  standardIndex PropertyKindCalculus.Iso80000.Part7.catalogue part7Default part7Refs

#doc (Manual) "ISO 80000-7 — Light and radiation" =>

The fifth part specified in full is ISO 80000-7, _Light and radiation_. Every item — all
of 7-1.1 … 7-37, including every sub-suffixed item — is catalogued: the speed of light
and refractive index, radiant energy and its densities, radiant flux, intensity, and
radiance, irradiance, exitance, and exposure, the luminous efficiency and efficacy, the
luminous quantities, the photon quantities, colorimetry, colour temperature, the optical
material properties, and the attenuation coefficients — each carrying its exact source as
data: the part, the printed item designation, the principal quantity symbol, and the
coherent SI unit symbol. Only _citation locators_ are recorded; no normative content from
the licensed standard is reproduced. The defining _mathematics_ of selected remarks is
specified in the sibling module `Part7.DefiningRelations`.

Light and radiation is where _dimension does not classify the kind_ reaches its widest
form, and where the catalogue meets two SI base quantities PhysLib's five-generator
`Dimension` does not carry — luminous intensity and amount of substance. Both are handled
by the Finkelstein–Whitehead _scale-spanning_ reduction (the _Scale-spanning units_
chapter, requirement _R13_), not by a new generator: the candela is the dimension of
_power_, the steradian and the mole are dimension one. So the luminous quantities share
the dimensions of their radiant partners — luminous flux ≡ radiant flux, luminance ≡
radiance, illuminance ≡ irradiance — while staying distinct kinds, and a molar quantity
drops the mole.

# Quantity-kinds and units of ISO 80000-7

:::group "iso80000_part7"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, here over mass, length, and time only: the radiation reductions make the
candela the dimension of power and the steradian and mole dimension one. The standard's
dimensional facts — a radiant flux is `M·L²·T⁻³`, an irradiance `M·T⁻³`, a molar
absorption coefficient an area `L²` — are _checked computations_. Each unit is a
{uses "def_metrologicalUnit"}[metrological unit] of its kind; commensurability is a
type-level fact, so the watt of radiant flux and the lumen of luminous flux are not
interchangeable though they share one dimension.
:::

:::definition "def_part7_catalogued_kind" (parent := "iso80000_part7") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "7-6.1"), the
principal quantity symbol, and the coherent SI unit symbol. The citation travels with the
kind as data, so the source of each definition can be rendered or audited downstream.
:::

:::proof "def_part7_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `ISO 80000-7, Second edition, 2019-08 item 7-6.1`. The `catalogue` lists all 66
items in item order — the speed of light (7-1.1), radiant flux (7-4.1), luminous
intensity (7-14), the photon quantities (7-19.1 … 7-25), the molar absorption coefficient
(7-37), … — each paired with its coherent SI unit symbol.
:::

:::theorem "thm_part7_candela_power" (parent := "iso80000_part7") (lean := "PropertyKindCalculus.Iso80000.Part7.luminousIntensity_dim_eq_power") (tags := "proved") (effort := "small")
*The candela reduces to power (item 7-14).* Luminous intensity carries the dimension of
power, `M·L²·T⁻³` — the scale-spanning reduction (R13) made a checked computation: PhysLib
has no luminous-intensity generator, and none is needed, the spectral luminous efficiency
`V(λ)` that relates the candela to the watt being dimensionless. Uses
{uses "def_dim"}[the dimension map] and {uses "def_scale_spanning_unit"}[the scale-spanning
units].
:::

:::proof "thm_part7_candela_power"
`luminousIntensity_dim_eq_power : luminousIntensity.dim = Dim.power`, by reflexivity over
`Dim.luminousIntensity := Dim.power`. The companions `radiantFlux_dim_{mass,length,time}`
record `M·L²·T⁻³` for radiant flux, `radiantEnergy_dim_time = -2` the joule,
`photonFlux_dim_time = -1` the photon count rate, and
`molarAbsorptionCoefficient_dim_length = 2` the molar coefficient as an area (the mole
reduced).
:::

# The radiant / luminous / photon trios

ISO 80000-7 lists most measurands three times — a _radiant_ (energetic, subscript e)
version, a _luminous_ (photopic, subscript v) version, and a _photon_ (count, subscript p)
version — and pairs them explicitly ("the corresponding photometric quantity is …"). They
are not the same kind of quantity: radiant flux is the total radiant power, luminous flux
its `V(λ)`-weighted response in the human eye, photon flux a count rate. A dimension-only
model sees one type, "a real number of watts", for radiant and luminous flux, and cannot
say why a count rate is a different thing again.

This is requirement _R2_ once more — the pattern Part 3 set on the length family, Part 4
on the force family, Part 5 on the thermodynamic potentials, Part 6 on the AC power
quantities — now on the radiation trios. Each member is a distinct _kind_ individuated
_not by fiat_ but by a _radiation mode_ (Dybkær's examination principle, §7.5). And the
trios split two ways: the luminous mode is a _dimensionless reweighting_ (luminous flux ≡
radiant flux in dimension), while the photon mode is a genuine _re-dimensioning_ (photon
flux is `T⁻¹`, not `M·L²·T⁻³`).

:::group "iso80000_part7_trios"
The trio members are individuated by an {uses "def_examination"}[examination principle] —
the radiation mode — and (the luminous and radiant members) collide in dimension. The
sharpest case is radiant versus luminous flux: both `M·L²·T⁻³`, they are nonetheless
different kinds, and the calculus proves it from their differing radiation modes, not from
a naming convention.
:::

:::definition "def_part7_radiation_mode" (parent := "iso80000_part7_trios") (lean := "PropertyKindCalculus.Iso80000.Part7.modeKind")
A _radiation-mode kind_ is a ratio-scale {uses "def_quantity"}[quantity]-kind carrying an
{uses "def_examination"}[examination principle] — this work's terse descriptor of which
aspect of the radiation it isolates: the total energetics (subscript e), the
`V(λ)`-weighted photopic response (subscript v), or a photon count (subscript p). The
radiant, luminous, and photon members of each measurand's trio differ in this principle.
:::

:::proof "def_part7_radiation_mode"
`modeKind id m dim := { kind := { id, scale := .ratio, examPrinciple := some m.id }, dim }`,
with the three modes `RadiationMode.energetic`, `.photopic`, `.photonic`. The flux trio is
`radiantFlux` / `luminousFlux` / `photonFlux`, and likewise for energy, intensity,
radiance, irradiance, exitance, and exposure.
:::

:::theorem "thm_part7_trio" (parent := "iso80000_part7_trios") (lean := "PropertyKindCalculus.Iso80000.Part7.radiantFlux_ne_luminousFlux") (tags := "proved") (effort := "small")
*Radiant and luminous flux are distinct kinds — by radiation mode, not by fiat.* They
share dimension `M·L²·T⁻³` and are both "flux", yet are different kinds _because one is the
total radiant power and the other its `V(λ)`-weighted photopic response_ — proved through
`distinct_of_examPrinciple` (§7.5). The photon member is distinct again, and even
re-dimensions (`T⁻¹`). This is the AC-power-family pattern of Part 6 on the radiation
trios. Uses {uses "def_examination"}[the examination principle].
:::

:::proof "thm_part7_trio"
`radiantFlux_ne_luminousFlux : radiantFlux.kind ≠ luminousFlux.kind`, from
`KindOfProperty.distinct_of_examPrinciple` on the differing modes `radiant-energetic` and
`luminous-photopic-Vlambda`. The companions `radiantFlux_ne_photonFlux` (the photon mode)
and `radiance_ne_luminance` cover further trios; `radiantFlux_examinedBy` and
`luminousFlux_examinedBy` check the kind-to-mode links. Axiom-free.
:::

:::theorem "thm_part7_efficacy" (parent := "iso80000_part7_trios") (lean := "PropertyKindCalculus.Iso80000.Part7.DefiningRelations.luminousEfficacy_dim_from_fluxes") (tags := "proved") (effort := "small")
*The luminous efficacy is dimension one because it is a ratio of two fluxes (item 7-11.1).*
From `K = Φ_v/Φ_e`, with luminous and radiant flux of equal dimension (the candela
reducing to power), the dimension cancels and the efficacy is _computed_ to be one — the
photometric analogue of the power factor (Part 6) and the plane angle (Part 3). The scale
coefficient `K_cd = 683 lm/W` is the candela's scale-spanning constant (R13). Uses
{uses "def_dim"}[the dimension map] and {uses "def_quotient_kind"}[the quotient kind-law].
:::

:::proof "thm_part7_efficacy"
`luminousEfficacy_dim_from_fluxes : luminousEfficacy.dim = luminousFlux.dim /
radiantFlux.dim`, by reducing the right side via `div_self` (`a / a = 1`). The kind-law
`luminousEfficacy_quot_fluxes` is `⟨rfl, rfl, rfl⟩`; the efficacy nonetheless remains a
distinct kind from every other dimension-one quantity (the collision capstone below).
:::

# Dimension does not classify; the kind does — the widest collisions in the series

ISO 80000-7 holds the widest dimension collisions of the catalogue. The candela reducing
to power and the steradian to one, _radiant flux, luminous flux, radiant intensity, and
luminous intensity all share_ `M·L²·T⁻³`; radiance, luminance, irradiance, illuminance,
and the exitances all share `M·T⁻³`; and over two dozen kinds — refractive index, the
efficiencies and efficacies, emissivity, the absorptances, reflectances, and
transmittances, the optical densities, the radiance and luminance factors, the
chromaticity coordinates, the colour-matching functions, the photon number — share
dimension one.

:::group "iso80000_part7_collision"
These are the dimension-disambiguation capstones, on _standard_ quantities: the
{uses "def_dim"}[dimension map] identifies the members of each set, while the kind layer
keeps them apart, both as kinds and as {uses "def_metrologicalUnit"}[units]. The sharpest
is the scale-spanning collision — a base-quantity unit (the candela) sharing a dimension
with a derived one (the watt), separated only by kind.
:::

:::theorem "thm_part7_collision" (parent := "iso80000_part7_collision") (lean := "PropertyKindCalculus.Iso80000.Part7.iso80000_7_dim_collision") (tags := "proved") (effort := "small")
*Radiant flux is not luminous flux, though both are `M·L²·T⁻³`.* There exist distinct
ISO 80000-7 kinds with the same dimension — radiant and luminous flux witness it, alongside
radiant and luminous intensity. The candela reduces to power, so no dimension-only type
system can separate them; the kind layer — and the unit, `W` versus `lm` — does. This is a
collision _between a base-quantity unit and a derived one_, the scale-spanning case (R13)
on the standard. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part7_collision"
`iso80000_7_dim_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim`,
witnessed by `⟨radiantFlux, luminousFlux, …⟩`. The companion
`radiantFlux_dim_eq_radiantIntensity_dim` is the _steradian_ collision (flux versus
intensity, the steradian being dimension one), and
`wattRadiant_lumen_not_commensurable` / `wattRadiant_wattPerSteradian_not_commensurable`
record the unit-level facts. Axiom-free.
:::

:::theorem "thm_part7_dim_one" (parent := "iso80000_part7_collision") (lean := "PropertyKindCalculus.Iso80000.Part7.iso80000_7_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 disambiguation, on the standard — the widest in the series.* There exist
distinct ISO 80000-7 kinds with the same dimension one — refractive index and emissivity
witness it, alongside the efficiencies, efficacies, absorptances, reflectances,
transmittances, optical densities, the radiance and luminance factors, the reflectance
factor, the chromaticity coordinates, the colour-matching functions, and the photon number.
Dimension cannot separate them; the kind layer does. Uses {uses "def_dim"}[the dimension
map].
:::

:::proof "thm_part7_dim_one"
`iso80000_7_dim_one_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
a.dim = 1`, witnessed by `⟨refractiveIndex, emissivity, …⟩` with `refractiveIndex_ne_emissivity`
(a `decide`) and reflexivity. Axiom-free.
:::

# The algebraic Remarks as kind-laws: radiometry and photometry built by the kind algebra

Many Part-7 definitions state a quantity's defining relation _algebraically_ — the
constitutive laws of radiometry and photometry. Radiant flux is the time-derivative of
radiant energy (7-4.1); photon flux of photon number (7-20); irradiance is the
area-density of radiant flux (7-7.1); radiant intensity its solid-angle-density (7-5.1);
the luminous efficacy is luminous flux over radiant flux (7-11.1). Each is specified as an
R12 kind-law, several crossing to ISO 80000-3 for time, area, and solid angle.

:::group "iso80000_part7_relations"
The {uses "def_quotient_kind"}[quotient] family carries the kind-laws. Three payoffs on the
standard's own definitions: radiometry and photometry are built from one another; the
_dimension follows from the relation_ as a checked computation (the luminous efficacy
dimensionless, radiant intensity keeping flux's dimension because the solid angle is
dimension one); and a verified-by-construction quantity carries its classification
certificate.
:::

:::theorem "thm_part7_irradiance" (parent := "iso80000_part7_relations") (lean := "PropertyKindCalculus.Iso80000.Part7.DefiningRelations.irradianceOf_isQuotient") (tags := "proved") (effort := "small")
*Irradiance is radiant flux / area — a verified construction (item 7-7.1).* An irradiance
built as the quotient of a radiant flux by an area carries its quotient certificate by
construction, over the `ℝ` carrier, and canonicity makes the certificate determine the
quantity. The companion `radiantIntensity_dim_from_flux_solidAngle` shows radiant intensity
_keeps_ the dimension of flux because the solid angle it divides by is dimension one — the
steradian dropping, as a checked computation. Uses {uses "def_quotient_kind"}[the quotient
kind-law].
:::

:::proof "thm_part7_irradiance"
`irradianceOf φ a := Quantity.div irradiance_quot_flux_area φ a`, and `irradianceOf_isQuotient`
is `rfl`; `irradiance_certificate_canonical` is `eq_div_of_isQuotient`. The same family gives
`luminousEfficacyOf` (= `Φ_v/Φ_e`), and the cross-part `radiantFlux_quot_energy_duration`
(= radiant energy / time) and `photonFlux_quot_number_duration` (= photon number / time),
the time crossing to ISO 80000-3.
:::

# Item index — ISO 80000-7

Every catalogued item of ISO 80000-7, indexed by its printed item number, with the
principal quantity symbol, the coherent SI unit, and the PhysLib dimension this work
assigns it (over the radiation reductions). Each item number links to the formalized
result it participates in — a trio distinction, a dimension collision, a defining
relation, or the catalogue itself. Symbols and unit strings are _citation locators_;
nothing normative is reproduced.

:::iso_doc_table part7IndexTable
:::
