/-
# Worked examples — ISO 80000-7 (Light and radiation)

Part-7 examples, mirroring the `Iso80000` library's own `Iso80000/Part7` layout:

1. the dimensional algebra over the radiation reductions (radiant flux is `M·L²·T⁻³`,
   luminous intensity reduces to power, the molar absorption coefficient is an area,
   photon flux is `T⁻¹`);
2. **the radiant / luminous / photon trios (requirement R2)** — radiant flux, luminous
   flux, and photon flux as distinct kinds individuated **by radiation mode**; radiant
   and luminous flux comparable in dimension, distinct in kind;
3. **the scale-spanning candela collision (R13)** — luminous flux ≡ radiant flux in
   dimension yet not in kind (the candela reducing to power), and the watt of radiant
   flux not commensurable with the lumen of luminous flux *though both are* `M·L²·T⁻³`;
4. **the steradian reduction** — radiant intensity ≡ radiant flux in dimension (the
   steradian being dimension one);
5. **the dimension-one mega-family** — refractive index, emissivity, and two dozen more
   distinct kinds at dimension one;
6. **defining relations** — radiant flux = radiant energy / time, irradiance = flux /
   area, radiant intensity = flux / solid angle (the steradian dropping), and the
   luminous efficacy dimensionless because it is a ratio of two fluxes; several cross to
   ISO 80000-3;
7. **catalogue coverage** — all 66 items carry their source as data.

Series-wide catalogue examples are in the sibling
`PropertyKindCalculus.DimensionExamples.Iso80000.References`; the scale-spanning unit
classification (R13) is exercised in `PropertyKindCalculus.DimensionExamples.ScaleSpanning`.
-/

module

public import PropertyKindCalculus.Iso80000
meta import PropertyKindCalculus.Iso80000
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Iso80000.Part7

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part7
open PropertyKindCalculus.Iso80000.Part7.DefiningRelations

/-! ## (1) ISO 80000-7 — the dimensional algebra over the radiation reductions

PhysLib carries no luminous-intensity, solid-angle, or amount-of-substance generator;
following the scale-spanning reduction (R13), the candela is the dimension of power, the
steradian and the mole are dimension one. The dimensional algebra is a checked
computation. -/

-- radiant flux is `M·L²·T⁻³` (the watt)
example : radiantFlux.dim.mass = 1 := radiantFlux_dim_mass
example : radiantFlux.dim.length = 2 := radiantFlux_dim_length
example : radiantFlux.dim.time = -3 := radiantFlux_dim_time
-- the candela reduces to power; radiant energy is `M·L²·T⁻²`; photon flux is `T⁻¹`
example : luminousIntensity.dim = Dim.power := luminousIntensity_dim_eq_power
example : radiantEnergy.dim.time = -2 := radiantEnergy_dim_time
example : photonFlux.dim.time = -1 := photonFlux_dim_time
-- the molar absorption coefficient is an area `L²` — the mole reduced (item 7-37)
example : molarAbsorptionCoefficient.dim.length = 2 :=
  molarAbsorptionCoefficient_dim_length

-- each kind carries its exact item citation as data
#guard radiantFluxCK.item == "7-4.1"
#guard luminousIntensityCK.item == "7-14"
#guard luminousIntensityCK.cite == "ISO 80000-7, Second edition, 2019-08 item 7-14"
#guard photonExposureCK.item == "7-25"

-- the watt and the candela are well-formed units
example : wattRadiant.WellFormed := wattRadiant_wellFormed
example : candela.WellFormed := candela_wellFormed

/-! ## (2) The radiant / luminous / photon trios (requirement R2, on the real standard)

ISO 80000-7 lists most measurands as a trio — radiant (energetic), luminous (photopic),
photon — individuated by which aspect of the radiation each isolates. Each is a distinct
kind carrying a *radiation mode* examination principle. -/

-- (a) DISTINCTION NOT BY FIAT: radiant flux and luminous flux are distinct kinds
--     *because they isolate different aspects* (total radiant power vs the V(λ)-weighted
--     photopic response) — proved via `distinct_of_examPrinciple`, not by `id` strings.
example : radiantFlux.kind ≠ luminousFlux.kind := radiantFlux_ne_luminousFlux
example : radiantFlux.kind.examinedBy RadiationMode.energetic := radiantFlux_examinedBy
example : luminousFlux.kind.examinedBy RadiationMode.photopic := luminousFlux_examinedBy

-- (b) the photon mode even RE-DIMENSIONS: radiant flux (`M·L²·T⁻³`) ≠ photon flux
--     (`T⁻¹`), distinct in both kind and dimension.
example : radiantFlux.kind ≠ photonFlux.kind := radiantFlux_ne_photonFlux

-- (c) the radiance trio likewise: radiance ≠ luminance, distinct by radiation mode.
example : radiance.kind ≠ luminance.kind := radiance_ne_luminance

/-! ## (3) The scale-spanning candela collision (requirement R13, on the real standard)

The luminous quantities differ from their radiant partners only by the *dimensionless*
spectral luminous efficiency `V(λ)`, scaled by the human-selected efficacy `K_cd`
(683 lm/W). So luminous flux carries the *same* dimension as radiant flux — the candela
reducing to power — yet is a different kind. -/

-- (a) SAME DIMENSION: luminous flux ≡ radiant flux in dimension (`M·L²·T⁻³`).
example : radiantFlux.dim = luminousFlux.dim := radiantFlux_dim_eq_luminousFlux_dim
-- (b) DISTINCT KIND: yet they are not the same kind (radiation mode).
example : radiantFlux.kind ≠ luminousFlux.kind := radiantFlux_ne_luminousFlux
-- (c) and the units are not commensurable, *though the dimension is one and the same* —
--     the watt of radiant flux and the lumen of luminous flux, `W` vs `lm`.
example : ¬ wattRadiant.Commensurable lumen := wattRadiant_lumen_not_commensurable

/-! ## (4) The steradian reduction

PhysLib carries no solid-angle generator (the steradian is dimension one), so radiant
flux `W` and radiant intensity `W/sr` share `M·L²·T⁻³` — distinct kinds the dimension
cannot separate. -/

example : radiantFlux.dim = radiantIntensity.dim :=
  radiantFlux_dim_eq_radiantIntensity_dim
example : ¬ wattRadiant.Commensurable wattPerSteradian :=
  wattRadiant_wattPerSteradian_not_commensurable

/-! ## (5) The dimension-one mega-family — the widest in the series

Refractive index, emissivity, the efficiencies and efficacies, absorptances,
reflectances, transmittances, optical densities, the radiance and luminance factors, the
chromaticity coordinates, the colour-matching functions, and the photon number are *all*
dimension one. -/

example : refractiveIndex.dim = emissivity.dim := refractiveIndex_dim_eq_emissivity_dim
example : refractiveIndex.kind ≠ emissivity.kind := refractiveIndex_ne_emissivity
-- the dimension-1 capstone, on standard quantities (the widest collision in the series).
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_7_dim_one_collision
-- and the scale-spanning collision capstone, `M·L²·T⁻³`.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  iso80000_7_dim_collision

/-! ## (6) Defining relations: radiometry and photometry built by the kind algebra

Radiant flux is the time-derivative of radiant energy, irradiance the area-density of
flux, radiant intensity the solid-angle-density of flux (the steradian dropping), and the
luminous efficacy a ratio of two fluxes; several cross to ISO 80000-3. -/

-- DIM FROM RELATION: radiant flux's `M·L²·T⁻³` follows from radiant energy / time
-- (cross-part, the time from ISO 80000-3).
example : radiantFlux.dim = radiantEnergy.dim / Part3.duration.dim :=
  radiantFlux_dim_from_energy_duration
-- irradiance's `M·T⁻³` follows from radiant flux / area (cross-part).
example : irradiance.dim = radiantFlux.dim / Part3.area.dim :=
  irradiance_dim_from_flux_area
-- THE STERADIAN DROPS: radiant intensity keeps radiant flux's dimension because the
-- solid angle it divides by is dimension one.
example : radiantIntensity.dim = radiantFlux.dim / Part3.solidAngle.dim :=
  radiantIntensity_dim_from_flux_solidAngle
-- ALGEBRAIC REMARK (item 7-11.1): the luminous efficacy is dimension one *because* it is
-- a ratio of two fluxes of equal dimension (`K = Φ_v/Φ_e`), the candela reducing to power.
example : luminousEfficacy.dim = luminousFlux.dim / radiantFlux.dim :=
  luminousEfficacy_dim_from_fluxes

-- VERIFIED CONSTRUCTION (item 7-7.1): an irradiance built as radiant flux / area carries
-- its classification certificate by construction, over `ℝ`.
example (φ : Quantity radiantFlux.kind ℝ) (a : Quantity Part3.area.kind ℝ) :
    (irradianceOf φ a).IsQuotient irradiance_quot_flux_area φ a :=
  irradianceOf_isQuotient φ a

-- the irradiance quotient instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `12 W / 3 m² = 4 W/m²` (at `Int`).
def irradianceInt : Quantity irradiance.kind Int :=
  Quantity.div irradiance_quot_flux_area
    (⟨12⟩ : Quantity radiantFlux.kind Int) (⟨3⟩ : Quantity Part3.area.kind Int)
#guard irradianceInt.magnitude == 4

/-! ## (7) Catalogue coverage — all 66 items carry their source as data -/

-- every ISO 80000-7 item is catalogued, in item order …
#guard PropertyKindCalculus.Iso80000.Part7.catalogue.length == 66
-- … with the item designations (including every sub-suffixed item) …
#guard radiantEnergyCK.item == "7-2.1"
#guard spectralRadiantEnergyDensityWavenumberCK.item == "7-3.3"
#guard maximumLuminousEfficacyCK.item == "7-11.3"
#guard luminousExposureCK.item == "7-18"
#guard molarAbsorptionCoefficientCK.item == "7-37"
-- … each citing its full source …
#guard luminousFluxCK.cite == "ISO 80000-7, Second edition, 2019-08 item 7-13"
-- … and recording its coherent SI unit symbol as a locator (one dimension, two units).
#guard radiantFluxCK.coherentUnit == "W"
#guard luminousFluxCK.coherentUnit == "lm"
#guard luminousIntensityCK.coherentUnit == "cd"
#guard photonFluxCK.coherentUnit == "s⁻¹"

end PropertyKindCalculus.Examples.Iso80000.Part7

end Blanket
