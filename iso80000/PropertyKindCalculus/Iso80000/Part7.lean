/-
# ISO 80000-7 — Light and radiation (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
ISO 80000-7 *Light and radiation* — all of items 7-1.1 … 7-37, including every
sub-suffixed item — each carrying its exact source as data: the part (`iso80000_7`),
the printed item designation, the principal quantity symbol, and the coherent SI unit
symbol. Only **citation locators** are recorded (item number, symbol, coherent SI
unit); no normative content (definitions, remarks) from the licensed standard is
reproduced. The defining *mathematics* of selected remarks is formalized in the sibling
module `Part7.DefiningRelations`.

Light and radiation is where the *dimension does not classify the kind* thesis reaches
its widest form, and where the calculus meets two SI base quantities that PhysLib's
five-generator `Dimension` does not carry — luminous intensity and amount of substance.
Following the Finkelstein–Whitehead *scale-spanning* analysis (Eur. J. Phys. 46 (2025)
035701; see `ScaleSpanning`, requirement **R13**), both are handled by **reduction**,
not by a new generator:

* **The radiant / luminous / photon trios.** ISO 80000-7 lists most measurands three
  times — a *radiant* (energetic, subscript e) version, a *luminous* (photopic,
  subscript v) version, and a *photon* (count, subscript p) version: radiant flux,
  luminous flux, photon flux; radiance, luminance, photon radiance; and so on. The
  standard pairs them explicitly ("the corresponding photometric quantity is …"). Here
  each trio is three distinct {kinds} individuated by an {examination principle} — the
  *radiation mode*: total radiant power, the `V(λ)`-weighted human eye, or a photon
  count.

* **The candela reduces to power — the scale-spanning collision (R13).** The luminous
  quantities differ from their radiant partners only by the *dimensionless* spectral
  luminous efficiency `V(λ)`, scaled by the human-selected efficacy `K_cd` (683 lm/W).
  So **luminous flux and radiant flux carry the *same* dimension `M·L²·T⁻³`, yet are
  different kinds** — and likewise luminance ≡ radiance, illuminance ≡ irradiance, …
  This is the sharpest *dimension does not classify* case in the series: the collision
  is built into the standard's own structure of corresponding quantities.

* **The photon mode re-dimensions where the luminous mode does not.** Counting quanta
  rather than weighting power changes the dimension: photon flux is `T⁻¹`, photon
  radiance `L⁻²·T⁻¹`. So a flux trio splits as *radiant ≡ luminous* (one dimension,
  two kinds) versus *photon* (a third dimension) — the luminous mode is a dimensionless
  reweighting, the photon mode a genuine re-dimensioning.

* **The steradian reduces too.** PhysLib carries no solid-angle generator (the
  steradian is dimensionless), so **radiant intensity `W/sr` and radiant flux `W` share
  `M·L²·T⁻³`**, and radiance shares with the per-area quantities. The plane/solid angle
  being dimension one is ISO 80000-3's convention, here made to bite.

* **The largest dimension-one family in the series.** Refractive index, luminous
  efficiency and efficacy, emissivity, absorptance, reflectance, transmittance (and
  their luminous variants), optical density, absorbance, the radiance and luminance
  factors, the reflectance factor, the chromaticity coordinates, the colour-matching
  functions, and the photon number are *all* dimension one — over two dozen distinct
  kinds the {dimension functor} collapses to one point and the kind layer keeps apart.

* **Amount of substance reduces to a count.** ISO 80000-7's one chemical quantity, the
  molar absorption coefficient (item 7-37, `m²/mol`), is an **area** `L²` once the mole
  is read as the dimensionless count `N_A` (R13).

* **The dimensional facts are checked computations**, discharged in PhysLib's dimension
  group over mass, length, and time.
-/

module

public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.ScaleSpanning
public import PropertyKindCalculus.Iso80000.References
public import PropertyKindCalculus.Iso80000.Catalogue

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Iso80000.Part7

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_7

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Radiation modes — the examination principles of the trios

Most ISO 80000-7 measurands come as a trio individuated by *which aspect of the
radiation each isolates* (Dybkær §7.5): the total energetics (subscript e), the
`V(λ)`-weighted response of the human photopic eye (subscript v), or a count of photons
(subscript p). Each `id` is this work's own terse descriptor of the defining
construction, not the standard's normative definition. -/

namespace RadiationMode
/-- Radiant (energetic) mode — the total radiant power, subscript e. -/
def energetic : ExaminationPrinciple := { id := "radiant-energetic" }
/-- Luminous (photopic) mode — radiant power weighted by the spectral luminous
efficiency `V(λ)` of the human eye, subscript v. -/
def photopic : ExaminationPrinciple := { id := "luminous-photopic-Vlambda" }
/-- Photon mode — a count of photons, subscript p. -/
def photonic : ExaminationPrinciple := { id := "photon-count" }
end RadiationMode

/-- A ratio-scale dimensioned kind individuated by its radiation mode (examination
principle). -/
def modeKind (id : String) (m : ExaminationPrinciple) (dim : Dimension LTMCTDimensionBase) :
    DimensionedKind :=
  { kind := { id := id, scale := .ratio, examPrinciple := some m.id }, dim := dim }

/-! ## Radiation dimensions

The dimensions of light and radiation, composed in PhysLib's `Dimension` group from
mass `M`, length `L`, and time `T`. Following the *scale-spanning* reduction (R13), the
candela is the dimension of *power* (`Dim.luminousIntensity = Dim.power`), the steradian
is dimension one, and the mole is dimension one — so the luminous quantities share the
dimensions of their radiant partners and a molar quantity drops the mole. -/

namespace RDim

/-- Volume, `L³`. -/
def volume : Dimension LTMCTDimensionBase := Dim.area * Dim.length
/-- Radiant/luminous/photon energy, `M·L²·T⁻²` (the joule, and `lm·s` reduced). -/
def energy : Dimension LTMCTDimensionBase := Dim.energy
/-- Spectral radiant energy (per wavelength), `M·L·T⁻²` (`J/nm` → `J/m`). -/
def energyPerLength : Dimension LTMCTDimensionBase := Dim.energy / Dim.length
/-- Radiant energy density, `M·L⁻¹·T⁻²` (energy per volume, `J/m³`). -/
def energyDensity : Dimension LTMCTDimensionBase := Dim.energy / volume
/-- Spectral radiant energy density per wavelength, `M·L⁻²·T⁻²` (`J/(m³·nm)`). -/
def spectralEnergyDensity : Dimension LTMCTDimensionBase := energyDensity / Dim.length
/-- Energy per area, `M·T⁻²` (radiant exposure `J/m²`; energy density per wavenumber). -/
def energyPerArea : Dimension LTMCTDimensionBase := Dim.energy / Dim.area
/-- Radiant/luminous flux and intensity, `M·L²·T⁻³` (the watt, and the candela
reduced). The steradian being dimension one, flux and intensity coincide here. -/
def power : Dimension LTMCTDimensionBase := Dim.power
/-- Spectral radiant flux/intensity (per wavelength), `M·L·T⁻³` (`W/nm`). -/
def powerPerLength : Dimension LTMCTDimensionBase := Dim.power / Dim.length
/-- Power per area, `M·T⁻³` (radiance, irradiance, exitance; luminance, illuminance). -/
def powerPerArea : Dimension LTMCTDimensionBase := Dim.power / Dim.area
/-- Spectral power per area per wavelength, `M·L⁻¹·T⁻³` (`W/(m²·nm)`; spectral
radiance/irradiance/exitance). -/
def powerPerVolume : Dimension LTMCTDimensionBase := Dim.power / volume
/-- Photon flux and intensity, `T⁻¹` (a count rate; the steradian being dimension one,
flux and intensity coincide). -/
def perTime : Dimension LTMCTDimensionBase := Dim.time⁻¹
/-- Photon radiance, irradiance, exitance, `L⁻²·T⁻¹` (`m⁻²·s⁻¹`). -/
def perAreaPerTime : Dimension LTMCTDimensionBase := (Dim.area * Dim.time)⁻¹
/-- Photon exposure, `L⁻²` (`m⁻²`). -/
def perArea : Dimension LTMCTDimensionBase := Dim.area⁻¹
/-- Linear attenuation/absorption coefficient, `L⁻¹` (`m⁻¹`). -/
def perLength : Dimension LTMCTDimensionBase := Dim.length⁻¹
/-- Mass attenuation/absorption coefficient, `M⁻¹·L²` (`kg⁻¹·m²`). -/
def massAttenuation : Dimension LTMCTDimensionBase := Dim.area / Dim.mass

end RDim

/-! ## (A) Propagation: speed of light and refractive index (items 7-1.1, 7-1.2) -/

/-- Speed of light in a medium — item 7-1.1, dimension `L·T⁻¹` (unit m/s). -/
def speedOfLight : DimensionedKind := dimKind "speed of light in a medium" Dim.speed
/-- Refractive index — item 7-1.2, dimension one (a ratio of speeds). -/
def refractiveIndex : DimensionedKind := dimKind "refractive index" Dim.one

/-! ## (B) Radiant energy and its densities (items 7-2.1 … 7-3.3)

Radiant energy (7-2.1) is the joule; its spectral density (7-2.2) is per wavelength.
The radiant energy density (7-3.1) is energy per volume, with spectral densities per
wavelength (7-3.2) and per wavenumber (7-3.3). -/

/-- Radiant energy `<electromagnetism>` — item 7-2.1, dimension `M·L²·T⁻²` (unit J). -/
def radiantEnergy : DimensionedKind :=
  modeKind "radiant energy" RadiationMode.energetic RDim.energy
/-- Spectral radiant energy — item 7-2.2, dimension `M·L·T⁻²` (unit J/nm). -/
def spectralRadiantEnergy : DimensionedKind :=
  modeKind "spectral radiant energy" RadiationMode.energetic RDim.energyPerLength
/-- Radiant energy density — item 7-3.1, dimension `M·L⁻¹·T⁻²` (unit J/m³). -/
def radiantEnergyDensity : DimensionedKind :=
  modeKind "radiant energy density" RadiationMode.energetic RDim.energyDensity
/-- Spectral radiant energy density in terms of wavelength — item 7-3.2, dimension
`M·L⁻²·T⁻²` (unit J/(m³·nm)). -/
def spectralRadiantEnergyDensityWavelength : DimensionedKind :=
  modeKind "spectral radiant energy density in terms of wavelength"
    RadiationMode.energetic RDim.spectralEnergyDensity
/-- Spectral radiant energy density in terms of wavenumber — item 7-3.3, dimension
`M·T⁻²` (unit J/m²). -/
def spectralRadiantEnergyDensityWavenumber : DimensionedKind :=
  modeKind "spectral radiant energy density in terms of wavenumber"
    RadiationMode.energetic RDim.energyPerArea

/-! ## (C) Radiant flux, intensity, radiance (items 7-4.1 … 7-6.2)

Radiant flux/power (7-4.1) is the watt; radiant intensity (7-5.1) is W/sr — the *same*
dimension, the steradian being dimension one. Radiance (7-6.1) is W/(sr·m²). Each has a
spectral (per-wavelength) variant. -/

/-- Radiant flux, radiant power — item 7-4.1, dimension `M·L²·T⁻³` (unit W). -/
def radiantFlux : DimensionedKind :=
  modeKind "radiant flux" RadiationMode.energetic RDim.power
/-- Spectral radiant flux, spectral radiant power — item 7-4.2, dimension `M·L·T⁻³`
(unit W/nm). -/
def spectralRadiantFlux : DimensionedKind :=
  modeKind "spectral radiant flux" RadiationMode.energetic RDim.powerPerLength
/-- Radiant intensity — item 7-5.1, dimension `M·L²·T⁻³` (unit W/sr; the steradian is
dimension one, so this shares the dimension of radiant flux). -/
def radiantIntensity : DimensionedKind :=
  modeKind "radiant intensity" RadiationMode.energetic RDim.power
/-- Spectral radiant intensity — item 7-5.2, dimension `M·L·T⁻³` (unit W/(sr·nm)). -/
def spectralRadiantIntensity : DimensionedKind :=
  modeKind "spectral radiant intensity" RadiationMode.energetic RDim.powerPerLength
/-- Radiance — item 7-6.1, dimension `M·T⁻³` (unit W/(sr·m²)). -/
def radiance : DimensionedKind :=
  modeKind "radiance" RadiationMode.energetic RDim.powerPerArea
/-- Spectral radiance — item 7-6.2, dimension `M·L⁻¹·T⁻³` (unit W/(sr·m²·nm)). -/
def spectralRadiance : DimensionedKind :=
  modeKind "spectral radiance" RadiationMode.energetic RDim.powerPerVolume

/-! ## (D) Irradiance, exitance, exposure (items 7-7.1 … 7-9.2)

Irradiance (7-7.1, flux onto a surface) and radiant exitance (7-8.1, flux off a
surface) are both W/m² — the same dimension as radiance. Radiant exposure (7-9.1) is
J/m². Each has a spectral (per-wavelength) variant. -/

/-- Irradiance — item 7-7.1, dimension `M·T⁻³` (unit W/m²). -/
def irradiance : DimensionedKind :=
  modeKind "irradiance" RadiationMode.energetic RDim.powerPerArea
/-- Spectral irradiance — item 7-7.2, dimension `M·L⁻¹·T⁻³` (unit W/(m²·nm)). -/
def spectralIrradiance : DimensionedKind :=
  modeKind "spectral irradiance" RadiationMode.energetic RDim.powerPerVolume
/-- Radiant exitance (deprecated: radiant emittance) — item 7-8.1, dimension `M·T⁻³`
(unit W/m²). -/
def radiantExitance : DimensionedKind :=
  modeKind "radiant exitance" RadiationMode.energetic RDim.powerPerArea
/-- Spectral radiant exitance — item 7-8.2, dimension `M·L⁻¹·T⁻³` (unit W/(m²·nm)). -/
def spectralRadiantExitance : DimensionedKind :=
  modeKind "spectral radiant exitance" RadiationMode.energetic RDim.powerPerVolume
/-- Radiant exposure — item 7-9.1, dimension `M·T⁻²` (unit J/m²). -/
def radiantExposure : DimensionedKind :=
  modeKind "radiant exposure" RadiationMode.energetic RDim.energyPerArea
/-- Spectral radiant exposure — item 7-9.2, dimension `M·L⁻²·T⁻²` (unit J/(m²·nm)). -/
def spectralRadiantExposure : DimensionedKind :=
  modeKind "spectral radiant exposure" RadiationMode.energetic RDim.spectralEnergyDensity

/-! ## (E) Luminous efficiency and efficacy (items 7-10.1 … 7-11.4)

The luminous efficiency (7-10.1) and spectral luminous efficiency `V(λ)` (7-10.2) are
dimension one — the weighting that turns radiant into luminous quantities. The luminous
efficacy quantities (7-11.1 … 7-11.4) are lm/W, **dimension one** once the candela
reduces to power: a ratio of a luminous to a radiant flux. -/

/-- Luminous efficiency `<specified photometric condition>` — item 7-10.1, dimension
one. -/
def luminousEfficiency : DimensionedKind := dimKind "luminous efficiency" Dim.one
/-- Spectral luminous efficiency `<specified photometric condition>`, `V(λ)` — item
7-10.2, dimension one. -/
def spectralLuminousEfficiency : DimensionedKind :=
  dimKind "spectral luminous efficiency" Dim.one
/-- Luminous efficacy of radiation `<specified photometric condition>` — item 7-11.1,
dimension one (lm/W; luminous flux over radiant flux, the candela reducing to power). -/
def luminousEfficacy : DimensionedKind := dimKind "luminous efficacy of radiation" Dim.one
/-- Spectral luminous efficacy `<specified photometric condition>`, `K(λ)` — item
7-11.2, dimension one (lm/W). -/
def spectralLuminousEfficacy : DimensionedKind :=
  dimKind "spectral luminous efficacy" Dim.one
/-- Maximum luminous efficacy `<specified photometric condition>`, `K_m` — item 7-11.3,
dimension one (lm/W; `K_cd = 683 lm/W` is the scale-spanning coefficient of R13). -/
def maximumLuminousEfficacy : DimensionedKind :=
  dimKind "maximum luminous efficacy" Dim.one
/-- Luminous efficacy of a source — item 7-11.4, dimension one (lm/W). -/
def luminousEfficacyOfSource : DimensionedKind :=
  dimKind "luminous efficacy of a source" Dim.one

/-! ## (F) The luminous quantities — the candela reduced to power (items 7-12 … 7-18)

Each luminous quantity is the photopic (`V(λ)`-weighted) partner of a radiant quantity,
and — the candela reducing to power (R13) — carries the *same* dimension as that partner
while being a distinct kind: luminous energy ≡ radiant energy, luminous flux ≡ radiant
flux, luminous intensity ≡ radiant intensity, luminance ≡ radiance, illuminance ≡
irradiance, luminous exitance ≡ radiant exitance, luminous exposure ≡ radiant
exposure. -/

/-- Luminous energy (deprecated: quantity of light) — item 7-12, dimension `M·L²·T⁻²`
(unit lm·s; the photopic partner of radiant energy). -/
def luminousEnergy : DimensionedKind :=
  modeKind "luminous energy" RadiationMode.photopic RDim.energy
/-- Luminous flux — item 7-13, dimension `M·L²·T⁻³` (unit lm; the photopic partner of
radiant flux, the same dimension once the candela reduces to power). -/
def luminousFlux : DimensionedKind :=
  modeKind "luminous flux" RadiationMode.photopic RDim.power
/-- Luminous intensity — item 7-14, dimension `M·L²·T⁻³` (unit cd, the candela). The
SI base quantity PhysLib does not carry, here the dimension of *power*
(`Dim.luminousIntensity`), via the scale-spanning reduction (R13). -/
def luminousIntensity : DimensionedKind :=
  modeKind "luminous intensity" RadiationMode.photopic Dim.luminousIntensity
/-- Luminance — item 7-15, dimension `M·T⁻³` (unit cd/m²; the photopic partner of
radiance). -/
def luminance : DimensionedKind :=
  modeKind "luminance" RadiationMode.photopic RDim.powerPerArea
/-- Illuminance — item 7-16, dimension `M·T⁻³` (unit lx; the photopic partner of
irradiance). -/
def illuminance : DimensionedKind :=
  modeKind "illuminance" RadiationMode.photopic RDim.powerPerArea
/-- Luminous exitance — item 7-17, dimension `M·T⁻³` (unit lm/m²; the photopic partner
of radiant exitance). -/
def luminousExitance : DimensionedKind :=
  modeKind "luminous exitance" RadiationMode.photopic RDim.powerPerArea
/-- Luminous exposure (deprecated: quantity of illumination, light exposure) — item
7-18, dimension `M·T⁻²` (unit lx·s; the photopic partner of radiant exposure). -/
def luminousExposure : DimensionedKind :=
  modeKind "luminous exposure" RadiationMode.photopic RDim.energyPerArea

/-! ## (G) The photon quantities — counting quanta re-dimensions (items 7-19.1 … 7-25)

The photon quantities count quanta rather than weighting power, so — except photon
energy (the joule) — they carry *different* dimensions from their radiant/luminous
partners: photon flux is `T⁻¹`, photon radiance `L⁻²·T⁻¹`. The photon number (7-19.1)
is dimension one. -/

/-- Photon number, number of photons — item 7-19.1, dimension one. -/
def photonNumber : DimensionedKind := dimKind "photon number" Dim.one
/-- Photon energy — item 7-19.2, dimension `M·L²·T⁻²` (unit J; `Q_p = hν`, the photon
partner of radiant energy, same dimension). -/
def photonEnergy : DimensionedKind :=
  modeKind "photon energy" RadiationMode.photonic RDim.energy
/-- Photon flux — item 7-20, dimension `T⁻¹` (unit s⁻¹; a count rate, the photon partner
of radiant flux at a *different* dimension). -/
def photonFlux : DimensionedKind :=
  modeKind "photon flux" RadiationMode.photonic RDim.perTime
/-- Photon intensity — item 7-21, dimension `T⁻¹` (unit s⁻¹·sr⁻¹; the steradian being
dimension one, this shares the dimension of photon flux). -/
def photonIntensity : DimensionedKind :=
  modeKind "photon intensity" RadiationMode.photonic RDim.perTime
/-- Photon radiance — item 7-22, dimension `L⁻²·T⁻¹` (unit m⁻²·s⁻¹·sr⁻¹). -/
def photonRadiance : DimensionedKind :=
  modeKind "photon radiance" RadiationMode.photonic RDim.perAreaPerTime
/-- Photon irradiance — item 7-23, dimension `L⁻²·T⁻¹` (unit m⁻²·s⁻¹). -/
def photonIrradiance : DimensionedKind :=
  modeKind "photon irradiance" RadiationMode.photonic RDim.perAreaPerTime
/-- Photon exitance — item 7-24, dimension `L⁻²·T⁻¹` (unit m⁻²·s⁻¹). -/
def photonExitance : DimensionedKind :=
  modeKind "photon exitance" RadiationMode.photonic RDim.perAreaPerTime
/-- Photon exposure — item 7-25, dimension `L⁻²` (unit m⁻²). -/
def photonExposure : DimensionedKind :=
  modeKind "photon exposure" RadiationMode.photonic RDim.perArea

/-! ## (H) Colorimetry — tristimulus, colour-matching, chromaticity (items 7-26.1 … 7-28.2)

The CIE tristimulus values (7-26.1, 7-26.2) are dimension one for object colours (for
source colours they carry luminance, `cd/m²`); the colour-matching functions (7-27.1,
7-27.2) and chromaticity coordinates (7-28.1, 7-28.2) are dimension one. -/

/-- Tristimulus values for the CIE 1931 standard colorimetric observer — item 7-26.1,
dimension one (object colours; for source colours, `cd/m²`). -/
def tristimulus1931 : DimensionedKind :=
  dimKind "tristimulus values for the CIE 1931 standard observer" Dim.one
/-- Tristimulus values for the CIE 1964 standard colorimetric observer — item 7-26.2,
dimension one. -/
def tristimulus1964 : DimensionedKind :=
  dimKind "tristimulus values for the CIE 1964 standard observer" Dim.one
/-- CIE colour-matching functions for the CIE 1931 standard colorimetric observer —
item 7-27.1, dimension one. -/
def colourMatching1931 : DimensionedKind :=
  dimKind "CIE colour-matching functions for the CIE 1931 standard observer" Dim.one
/-- CIE colour-matching functions for the CIE 1964 standard colorimetric observer —
item 7-27.2, dimension one. -/
def colourMatching1964 : DimensionedKind :=
  dimKind "CIE colour-matching functions for the CIE 1964 standard observer" Dim.one
/-- Chromaticity coordinates in the CIE 1931 standard colorimetric system — item
7-28.1, dimension one. -/
def chromaticity1931 : DimensionedKind :=
  dimKind "chromaticity coordinates in the CIE 1931 standard system" Dim.one
/-- Chromaticity coordinates in the CIE 1964 standard colorimetric system — item
7-28.2, dimension one. -/
def chromaticity1964 : DimensionedKind :=
  dimKind "chromaticity coordinates in the CIE 1964 standard system" Dim.one

/-! ## (I) Colour temperature (items 7-29.1, 7-29.2)

The colour temperature (7-29.1) and correlated colour temperature (7-29.2) are
thermodynamic temperatures, `Θ` (unit K) — the one place ISO 80000-7 reaches the
kelvin, the scale-spanning unit PhysLib keeps as an independent generator (R13). -/

/-- Colour temperature — item 7-29.1, dimension `Θ` (unit K). -/
def colourTemperature : DimensionedKind := dimKind "colour temperature" Dim.temperature
/-- Correlated colour temperature — item 7-29.2, dimension `Θ` (unit K). -/
def correlatedColourTemperature : DimensionedKind :=
  dimKind "correlated colour temperature" Dim.temperature

/-! ## (J) Emissivity and the optical material properties (items 7-30.1 … 7-34)

Emissivity (7-30.*), absorptance/reflectance/transmittance and their luminous variants
(7-31.*), the optical densities and absorbance (7-32.*), the radiance/luminance factors
(7-33.*), and the reflectance factor (7-34) are all dimension one — the optical
material-property family, every member a ratio of two like quantities. -/

/-- Emissivity — item 7-30.1, dimension one. -/
def emissivity : DimensionedKind := dimKind "emissivity" Dim.one
/-- Emissivity at a specified wavelength — item 7-30.2, dimension one. -/
def spectralEmissivity : DimensionedKind :=
  dimKind "emissivity at a specified wavelength" Dim.one
/-- Absorptance — item 7-31.1, dimension one. -/
def absorptance : DimensionedKind := dimKind "absorptance" Dim.one
/-- Luminous absorptance — item 7-31.2, dimension one (the photopic-weighted ratio). -/
def luminousAbsorptance : DimensionedKind := dimKind "luminous absorptance" Dim.one
/-- Reflectance — item 7-31.3, dimension one. -/
def reflectance : DimensionedKind := dimKind "reflectance" Dim.one
/-- Luminous reflectance — item 7-31.4, dimension one. -/
def luminousReflectance : DimensionedKind := dimKind "luminous reflectance" Dim.one
/-- Transmittance — item 7-31.5, dimension one. -/
def transmittance : DimensionedKind := dimKind "transmittance" Dim.one
/-- Luminous transmittance — item 7-31.6, dimension one. -/
def luminousTransmittance : DimensionedKind := dimKind "luminous transmittance" Dim.one
/-- Transmittance optical density (optical density, transmittance density, decadic
absorbance) — item 7-32.1, dimension one (`A₁₀ = -lg τ`). -/
def opticalDensity : DimensionedKind := dimKind "transmittance optical density" Dim.one
/-- Napierian absorbance — item 7-32.2, dimension one (`A_n = -ln τ`). -/
def napierianAbsorbance : DimensionedKind := dimKind "Napierian absorbance" Dim.one
/-- Radiance factor — item 7-33.1, dimension one. -/
def radianceFactor : DimensionedKind := dimKind "radiance factor" Dim.one
/-- Luminance factor — item 7-33.2, dimension one. -/
def luminanceFactor : DimensionedKind := dimKind "luminance factor" Dim.one
/-- Reflectance factor — item 7-34, dimension one. -/
def reflectanceFactor : DimensionedKind := dimKind "reflectance factor" Dim.one

/-! ## (K) Attenuation and absorption coefficients (items 7-35.1 … 7-37)

The linear attenuation and absorption coefficients (7-35.*) are `m⁻¹`; their mass
counterparts (7-36.*) are `kg⁻¹·m²`. The molar absorption coefficient (7-37, `m²/mol`)
is an **area** `L²` once the mole reduces to a dimensionless count (R13). -/

/-- Linear attenuation coefficient (linear extinction coefficient) `<radiometry>` —
item 7-35.1, dimension `L⁻¹` (unit m⁻¹). -/
def linearAttenuationCoefficient : DimensionedKind :=
  dimKind "linear attenuation coefficient" RDim.perLength
/-- Linear absorption coefficient `<radiometry>` — item 7-35.2, dimension `L⁻¹`
(unit m⁻¹). -/
def linearAbsorptionCoefficient : DimensionedKind :=
  dimKind "linear absorption coefficient" RDim.perLength
/-- Mass attenuation coefficient `<radiometry>` — item 7-36.1, dimension `M⁻¹·L²`
(unit kg⁻¹·m²). -/
def massAttenuationCoefficient : DimensionedKind :=
  dimKind "mass attenuation coefficient" RDim.massAttenuation
/-- Mass absorption coefficient `<radiometry>` — item 7-36.2, dimension `M⁻¹·L²`
(unit kg⁻¹·m²). -/
def massAbsorptionCoefficient : DimensionedKind :=
  dimKind "mass absorption coefficient" RDim.massAttenuation
/-- Molar absorption coefficient `<radiometry>` — item 7-37, dimension `L²` (unit
m²/mol), the mole reduced to a dimensionless count (R13). -/
def molarAbsorptionCoefficient : DimensionedKind :=
  dimKind "molar absorption coefficient" Dim.area

/-! ## The catalogue (every kind, with its source as data) -/

/-- Propagation. -/
def speedOfLightCK : CataloguedKind := cat "7-1.1" "c" "m/s" speedOfLight
def refractiveIndexCK : CataloguedKind := cat "7-1.2" "n" "1" refractiveIndex

/-- Radiant energy and its densities. -/
def radiantEnergyCK : CataloguedKind := cat "7-2.1" "Q_e" "J" radiantEnergy
def spectralRadiantEnergyCK : CataloguedKind :=
  cat "7-2.2" "Q_eλ" "J/nm" spectralRadiantEnergy
def radiantEnergyDensityCK : CataloguedKind := cat "7-3.1" "w" "J/m³" radiantEnergyDensity
def spectralRadiantEnergyDensityWavelengthCK : CataloguedKind :=
  cat "7-3.2" "w_λ" "J/(m³·nm)" spectralRadiantEnergyDensityWavelength
def spectralRadiantEnergyDensityWavenumberCK : CataloguedKind :=
  cat "7-3.3" "w_ṽ" "J/m²" spectralRadiantEnergyDensityWavenumber

/-- Radiant flux, intensity, radiance. -/
def radiantFluxCK : CataloguedKind := cat "7-4.1" "Φ_e" "W" radiantFlux
def spectralRadiantFluxCK : CataloguedKind :=
  cat "7-4.2" "Φ_eλ" "W/nm" spectralRadiantFlux
def radiantIntensityCK : CataloguedKind := cat "7-5.1" "I_e" "W/sr" radiantIntensity
def spectralRadiantIntensityCK : CataloguedKind :=
  cat "7-5.2" "I_eλ" "W/(sr·nm)" spectralRadiantIntensity
def radianceCK : CataloguedKind := cat "7-6.1" "L_e" "W/(sr·m²)" radiance
def spectralRadianceCK : CataloguedKind :=
  cat "7-6.2" "L_eλ" "W/(sr·m²·nm)" spectralRadiance

/-- Irradiance, exitance, exposure. -/
def irradianceCK : CataloguedKind := cat "7-7.1" "E_e" "W/m²" irradiance
def spectralIrradianceCK : CataloguedKind :=
  cat "7-7.2" "E_eλ" "W/(m²·nm)" spectralIrradiance
def radiantExitanceCK : CataloguedKind := cat "7-8.1" "M_e" "W/m²" radiantExitance
def spectralRadiantExitanceCK : CataloguedKind :=
  cat "7-8.2" "M_eλ" "W/(m²·nm)" spectralRadiantExitance
def radiantExposureCK : CataloguedKind := cat "7-9.1" "H_e" "J/m²" radiantExposure
def spectralRadiantExposureCK : CataloguedKind :=
  cat "7-9.2" "H_eλ" "J/(m²·nm)" spectralRadiantExposure

/-- Luminous efficiency and efficacy. -/
def luminousEfficiencyCK : CataloguedKind := cat "7-10.1" "V" "1" luminousEfficiency
def spectralLuminousEfficiencyCK : CataloguedKind :=
  cat "7-10.2" "V(λ)" "1" spectralLuminousEfficiency
def luminousEfficacyCK : CataloguedKind := cat "7-11.1" "K" "lm/W" luminousEfficacy
def spectralLuminousEfficacyCK : CataloguedKind :=
  cat "7-11.2" "K(λ)" "lm/W" spectralLuminousEfficacy
def maximumLuminousEfficacyCK : CataloguedKind :=
  cat "7-11.3" "K_m" "lm/W" maximumLuminousEfficacy
def luminousEfficacyOfSourceCK : CataloguedKind :=
  cat "7-11.4" "η_v" "lm/W" luminousEfficacyOfSource

/-- The luminous quantities. -/
def luminousEnergyCK : CataloguedKind := cat "7-12" "Q_v" "lm·s" luminousEnergy
def luminousFluxCK : CataloguedKind := cat "7-13" "Φ_v" "lm" luminousFlux
def luminousIntensityCK : CataloguedKind := cat "7-14" "I_v" "cd" luminousIntensity
def luminanceCK : CataloguedKind := cat "7-15" "L_v" "cd/m²" luminance
def illuminanceCK : CataloguedKind := cat "7-16" "E_v" "lx" illuminance
def luminousExitanceCK : CataloguedKind := cat "7-17" "M_v" "lm/m²" luminousExitance
def luminousExposureCK : CataloguedKind := cat "7-18" "H_v" "lx·s" luminousExposure

/-- The photon quantities. -/
def photonNumberCK : CataloguedKind := cat "7-19.1" "N_p" "1" photonNumber
def photonEnergyCK : CataloguedKind := cat "7-19.2" "Q_p" "J" photonEnergy
def photonFluxCK : CataloguedKind := cat "7-20" "Φ_p" "s⁻¹" photonFlux
def photonIntensityCK : CataloguedKind := cat "7-21" "I_p" "s⁻¹·sr⁻¹" photonIntensity
def photonRadianceCK : CataloguedKind :=
  cat "7-22" "L_p" "m⁻²·s⁻¹·sr⁻¹" photonRadiance
def photonIrradianceCK : CataloguedKind := cat "7-23" "E_p" "m⁻²·s⁻¹" photonIrradiance
def photonExitanceCK : CataloguedKind := cat "7-24" "M_p" "m⁻²·s⁻¹" photonExitance
def photonExposureCK : CataloguedKind := cat "7-25" "H_p" "m⁻²" photonExposure

/-- Colorimetry. -/
def tristimulus1931CK : CataloguedKind := cat "7-26.1" "X, Y, Z" "1" tristimulus1931
def tristimulus1964CK : CataloguedKind :=
  cat "7-26.2" "X₁₀, Y₁₀, Z₁₀" "1" tristimulus1964
def colourMatching1931CK : CataloguedKind :=
  cat "7-27.1" "x̄, ȳ, z̄" "1" colourMatching1931
def colourMatching1964CK : CataloguedKind :=
  cat "7-27.2" "x̄₁₀, ȳ₁₀, z̄₁₀" "1" colourMatching1964
def chromaticity1931CK : CataloguedKind := cat "7-28.1" "x, y, z" "1" chromaticity1931
def chromaticity1964CK : CataloguedKind :=
  cat "7-28.2" "x₁₀, y₁₀, z₁₀" "1" chromaticity1964

/-- Colour temperature. -/
def colourTemperatureCK : CataloguedKind := cat "7-29.1" "T_c" "K" colourTemperature
def correlatedColourTemperatureCK : CataloguedKind :=
  cat "7-29.2" "T_cp" "K" correlatedColourTemperature

/-- Emissivity and the optical material properties. -/
def emissivityCK : CataloguedKind := cat "7-30.1" "ε" "1" emissivity
def spectralEmissivityCK : CataloguedKind := cat "7-30.2" "ε(λ)" "1" spectralEmissivity
def absorptanceCK : CataloguedKind := cat "7-31.1" "α" "1" absorptance
def luminousAbsorptanceCK : CataloguedKind := cat "7-31.2" "α_v" "1" luminousAbsorptance
def reflectanceCK : CataloguedKind := cat "7-31.3" "ρ" "1" reflectance
def luminousReflectanceCK : CataloguedKind := cat "7-31.4" "ρ_v" "1" luminousReflectance
def transmittanceCK : CataloguedKind := cat "7-31.5" "τ" "1" transmittance
def luminousTransmittanceCK : CataloguedKind :=
  cat "7-31.6" "τ_v" "1" luminousTransmittance
def opticalDensityCK : CataloguedKind := cat "7-32.1" "D" "1" opticalDensity
def napierianAbsorbanceCK : CataloguedKind := cat "7-32.2" "A_n" "1" napierianAbsorbance
def radianceFactorCK : CataloguedKind := cat "7-33.1" "β_e" "1" radianceFactor
def luminanceFactorCK : CataloguedKind := cat "7-33.2" "β_v" "1" luminanceFactor
def reflectanceFactorCK : CataloguedKind := cat "7-34" "R" "1" reflectanceFactor

/-- Attenuation and absorption coefficients. -/
def linearAttenuationCoefficientCK : CataloguedKind :=
  cat "7-35.1" "μ" "m⁻¹" linearAttenuationCoefficient
def linearAbsorptionCoefficientCK : CataloguedKind :=
  cat "7-35.2" "a_l" "m⁻¹" linearAbsorptionCoefficient
def massAttenuationCoefficientCK : CataloguedKind :=
  cat "7-36.1" "μ_m" "kg⁻¹·m²" massAttenuationCoefficient
def massAbsorptionCoefficientCK : CataloguedKind :=
  cat "7-36.2" "α_m" "kg⁻¹·m²" massAbsorptionCoefficient
def molarAbsorptionCoefficientCK : CataloguedKind :=
  cat "7-37" "χ" "m²/mol" molarAbsorptionCoefficient

/-- The full ISO 80000-7 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [speedOfLightCK, refractiveIndexCK,
   radiantEnergyCK, spectralRadiantEnergyCK, radiantEnergyDensityCK,
   spectralRadiantEnergyDensityWavelengthCK, spectralRadiantEnergyDensityWavenumberCK,
   radiantFluxCK, spectralRadiantFluxCK, radiantIntensityCK, spectralRadiantIntensityCK,
   radianceCK, spectralRadianceCK,
   irradianceCK, spectralIrradianceCK, radiantExitanceCK, spectralRadiantExitanceCK,
   radiantExposureCK, spectralRadiantExposureCK,
   luminousEfficiencyCK, spectralLuminousEfficiencyCK, luminousEfficacyCK,
   spectralLuminousEfficacyCK, maximumLuminousEfficacyCK, luminousEfficacyOfSourceCK,
   luminousEnergyCK, luminousFluxCK, luminousIntensityCK, luminanceCK, illuminanceCK,
   luminousExitanceCK, luminousExposureCK,
   photonNumberCK, photonEnergyCK, photonFluxCK, photonIntensityCK, photonRadianceCK,
   photonIrradianceCK, photonExitanceCK, photonExposureCK,
   tristimulus1931CK, tristimulus1964CK, colourMatching1931CK, colourMatching1964CK,
   chromaticity1931CK, chromaticity1964CK,
   colourTemperatureCK, correlatedColourTemperatureCK,
   emissivityCK, spectralEmissivityCK, absorptanceCK, luminousAbsorptanceCK,
   reflectanceCK, luminousReflectanceCK, transmittanceCK, luminousTransmittanceCK,
   opticalDensityCK, napierianAbsorbanceCK, radianceFactorCK, luminanceFactorCK,
   reflectanceFactorCK,
   linearAttenuationCoefficientCK, linearAbsorptionCoefficientCK,
   massAttenuationCoefficientCK, massAbsorptionCoefficientCK, molarAbsorptionCoefficientCK]

/-! ## (L) Units — a few coherent SI units of these kinds

The watt of radiant flux and the lumen of luminous flux are not commensurable, *though
both carry the dimension `M·L²·T⁻³`* — the scale-spanning candela reduces to power, yet
the kind keeps the radiant and luminous flux apart. The candela is the SI unit of
luminous intensity; the steradian being dimension one, the watt of radiant flux and the
watt-per-steradian of radiant intensity are not commensurable either. -/

/-- The watt of radiant flux (item 7-4.1). -/
def wattRadiant : MetrologicalUnit := radiantFlux.kind.unit "W"
/-- The lumen of luminous flux (item 7-13) — *also* `M·L²·T⁻³`, but a unit of luminous,
not radiant, flux. -/
def lumen : MetrologicalUnit := luminousFlux.kind.unit "lm"
/-- The candela, the SI unit of luminous intensity (item 7-14). -/
def candela : MetrologicalUnit := luminousIntensity.kind.unit "cd"
/-- The lux of illuminance (item 7-16). -/
def lux : MetrologicalUnit := illuminance.kind.unit "lx"
/-- The watt-per-steradian of radiant intensity (item 7-5.1) — *also* `M·L²·T⁻³`, the
steradian being dimension one. -/
def wattPerSteradian : MetrologicalUnit := radiantIntensity.kind.unit "W/sr"

/-! ## (M) Checked dimensional facts (the dimensional algebra) -/

/-- Radiant flux is `M·L²·T⁻³`: its mass-exponent is `1` (item 7-4.1). -/
theorem radiantFlux_dim_mass : radiantFlux.dim.mass = 1 := Dim.power_mass
/-- Radiant flux is `M·L²·T⁻³`: its length-exponent is `2` (item 7-4.1). -/
theorem radiantFlux_dim_length : radiantFlux.dim.length = 2 := Dim.power_length
/-- Radiant flux is `M·L²·T⁻³`: its time-exponent is `-3` (item 7-4.1). -/
theorem radiantFlux_dim_time : radiantFlux.dim.time = -3 := Dim.power_time

/-- **Luminous intensity reduces to power.** The candela carries the dimension of
power, `M·L²·T⁻³` — the scale-spanning reduction (R13). -/
theorem luminousIntensity_dim_eq_power : luminousIntensity.dim = Dim.power := rfl

/-- Radiant energy is `M·L²·T⁻²`: its time-exponent is `-2` (item 7-2.1). -/
theorem radiantEnergy_dim_time : radiantEnergy.dim.time = -2 := Dim.energy_time

/-- The molar absorption coefficient is an **area** `L²` — the mole reduced (item
7-37). -/
theorem molarAbsorptionCoefficient_dim_length :
    molarAbsorptionCoefficient.dim.length = 2 := Dim.area_length

/-- Photon flux is `T⁻¹` — a count rate (item 7-20). -/
theorem photonFlux_dim_time : photonFlux.dim.time = -1 := by
  norm_num [photonFlux, modeKind, RDim.perTime, Dim.time, Dimension.inv_time,
    Dimension.T𝓭_time]

/-! ## (N) Unit well-formedness and (in)commensurability -/

/-- The watt of radiant flux is a well-formed unit. -/
theorem wattRadiant_wellFormed : wattRadiant.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- The candela is a well-formed unit of luminous intensity. -/
theorem candela_wellFormed : candela.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- **The watt of radiant flux and the lumen of luminous flux are not commensurable,
though both are `M·L²·T⁻³`.** The candela reduces to power, so the two fluxes share a
dimension — yet they are different kinds (radiant vs photopic), and the unit layer keeps
them apart. This is the scale-spanning collision of R13 on the standard. -/
theorem wattRadiant_lumen_not_commensurable :
    ¬ wattRadiant.Commensurable lumen := by
  unfold MetrologicalUnit.Commensurable wattRadiant lumen radiantFlux luminousFlux
    modeKind KindOfProperty.unit
  decide

/-- **The watt of radiant flux and the watt-per-steradian of radiant intensity are not
commensurable, though both are `M·L²·T⁻³`.** The steradian being dimension one, flux and
intensity share a dimension — yet they are different kinds. -/
theorem wattRadiant_wattPerSteradian_not_commensurable :
    ¬ wattRadiant.Commensurable wattPerSteradian := by
  unfold MetrologicalUnit.Commensurable wattRadiant wattPerSteradian radiantFlux
    radiantIntensity modeKind KindOfProperty.unit
  decide

/-! ## (O) The radiant / luminous / photon trios (requirement R2, on the standard)

Each measurand is listed by ISO 80000-7 as a trio — radiant (energetic), luminous
(photopic), photon — individuated by which aspect of the radiation it isolates. Each is
a distinct {kind} carrying a *radiation mode* examination principle; the luminous and
radiant members share a dimension (the candela reducing to power), the photon member
generally does not. -/

/-- **Radiant flux and luminous flux are distinct kinds — by radiation mode, not by
fiat.** They share dimension `M·L²·T⁻³` and are both "flux", yet differ because one is
the total radiant power and the other its `V(λ)`-weighted photopic response — proved
through `distinct_of_examPrinciple`. This is the candela's scale-spanning collision (R13)
realized as a kind distinction. -/
theorem radiantFlux_ne_luminousFlux : radiantFlux.kind ≠ luminousFlux.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- Radiant flux is examined by the energetic radiation mode. -/
theorem radiantFlux_examinedBy :
    radiantFlux.kind.examinedBy RadiationMode.energetic := rfl

/-- Luminous flux is examined by the photopic radiation mode. -/
theorem luminousFlux_examinedBy :
    luminousFlux.kind.examinedBy RadiationMode.photopic := rfl

/-- Radiant flux and photon flux are distinct kinds — and here the photon mode even
*re-dimensions*: photon flux is `T⁻¹`, not `M·L²·T⁻³`. -/
theorem radiantFlux_ne_photonFlux : radiantFlux.kind ≠ photonFlux.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- Radiance and luminance are distinct kinds, again by radiation mode (both `M·T⁻³`). -/
theorem radiance_ne_luminance : radiance.kind ≠ luminance.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-! ## (P) Dimension collisions — the kind classifies where the dimension cannot

ISO 80000-7 holds the widest dimension collisions in the series. The candela reducing
to power and the steradian to one, *radiant flux, luminous flux, radiant intensity, and
luminous intensity all share `M·L²·T⁻³`*; radiance, luminance, irradiance, illuminance,
and the exitances all share `M·T⁻³`; and over two dozen kinds share dimension one. -/

/-- Radiant flux and luminous flux share dimension `M·L²·T⁻³` (the candela reduced). -/
theorem radiantFlux_dim_eq_luminousFlux_dim :
    radiantFlux.dim = luminousFlux.dim := rfl

/-- Radiant flux and radiant intensity share dimension `M·L²·T⁻³` (the steradian
reduced). -/
theorem radiantFlux_dim_eq_radiantIntensity_dim :
    radiantFlux.dim = radiantIntensity.dim := rfl

/-- Irradiance and illuminance share dimension `M·T⁻³` (the candela reduced). -/
theorem irradiance_dim_eq_illuminance_dim :
    irradiance.dim = illuminance.dim := rfl

/-- Refractive index and emissivity share dimension one. -/
theorem refractiveIndex_dim_eq_emissivity_dim :
    refractiveIndex.dim = emissivity.dim := rfl

/-- Refractive index is not emissivity, though both are dimension one. -/
theorem refractiveIndex_ne_emissivity : refractiveIndex.kind ≠ emissivity.kind := by
  unfold refractiveIndex emissivity dimKind; decide

/-- **The scale-spanning collision capstone, on the standard.** There exist distinct
ISO 80000-7 kinds with the same dimension `M·L²·T⁻³` — radiant flux and luminous flux
witness it (alongside radiant and luminous intensity). The candela reduces to power, so
the {dimension functor} cannot separate them; the kind layer — and the unit, `W` versus
`lm` — does. This is the dimension-does-not-classify case at its sharpest: the collision
is between a base-quantity unit (the candela) and a derived one. -/
theorem iso80000_7_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨radiantFlux, luminousFlux, radiantFlux_ne_luminousFlux,
    radiantFlux_dim_eq_luminousFlux_dim⟩

/-- **The dimension-one disambiguation, on the standard — the widest in the series.**
There exist distinct ISO 80000-7 kinds with the same dimension one — refractive index
and emissivity witness it, alongside the efficiencies, efficacies, absorptances,
reflectances, transmittances, optical densities, the radiance and luminance factors, the
reflectance factor, the chromaticity coordinates, the colour-matching functions, and the
photon number. Dimension cannot separate them; the kind layer does. -/
theorem iso80000_7_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨refractiveIndex, emissivity, refractiveIndex_ne_emissivity, rfl, rfl⟩

end PropertyKindCalculus.Iso80000.Part7

end -- pkc-blanket-expose
end -- pkc-blanket
