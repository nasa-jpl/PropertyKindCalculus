/-
# ISO 80000-12 — Condensed matter physics (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
ISO 80000-12 *Condensed matter physics* — all of items 12-1.1 … 12-38.2, every
sub-suffixed item included, sixty in all — each carrying its exact source as data: the
part (`iso80000_12`), the printed item designation, the principal quantity symbol, and the
coherent SI unit symbol. Only **citation locators** are recorded; no normative content from
the licensed standard is reproduced. The defining *mathematics* of selected remarks is
formalized in the sibling module `Part12.DefiningRelations`.

Condensed matter physics is where the *dimension does not classify the kind* thesis becomes
the rule rather than the exception: nearly every quantity collides in dimension with
several others. Five families dominate the catalogue, and each is one big collision:

* **Thirteen lengths.** The lattice vector, fundamental lattice vectors, lattice plane
  spacing, Burgers vector, particle/equilibrium/displacement position vectors, the phonon
  and electron mean free paths, the diffusion length, the London penetration depth, and the
  coherence length all carry dimension `L`. Thirteen distinct kinds, one dimension.

* **Seven energies.** The work function, ionization energy, electron affinity, Fermi
  energy, gap energy, exchange integral, and superconductor energy gap all carry
  `M·L²·T⁻²`. The Fermi energy is not the gap energy though both are joules.

* **Five temperatures.** The Debye, Fermi, Curie, Néel, and superconduction-transition
  temperatures all carry `Θ` — five *named* temperatures, distinct kinds, one dimension and
  one unit (the kelvin).

* **Five carrier densities.** The electron, hole, intrinsic-carrier, donor, and acceptor
  densities all carry `L⁻³`.

* **Five reciprocal lengths.** The angular and fundamental reciprocal lattice vectors and
  the angular, Fermi, and Debye wavenumbers all carry `L⁻¹`.

* **The dimensional facts are checked computations**, discharged in PhysLib's dimension
  group over mass, length, time, temperature, and charge.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.Iso80000.Catalogue

namespace PropertyKindCalculus.Iso80000.Part12

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_12

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Condensed-matter dimensions

The dimensions of condensed matter physics, composed in PhysLib's `Dimension` group from
mass `M`, length `L`, time `T`, temperature `Θ`, and charge `C`. -/

namespace CDim

/-- Volume, `L³`. -/
def volume : Dimension PhyslibBase := Dim.area * Dim.length
/-- Reciprocal length, `L⁻¹` (`m⁻¹`) — reciprocal lattice vectors and wavenumbers. -/
def perLength : Dimension PhyslibBase := Dim.length⁻¹
/-- Number density, `L⁻³` (`m⁻³`) — the carrier densities. -/
def numberDensity : Dimension PhyslibBase := volume⁻¹
/-- Per time, `T⁻¹` (`s⁻¹`) — the Debye angular frequency. -/
def perTime : Dimension PhyslibBase := Dim.time⁻¹
/-- Density of vibrational states, `L⁻³·T` (`m⁻³·s`). -/
def vibrationalDOS : Dimension PhyslibBase := numberDensity * Dim.time
/-- Voltage, `M·L²·T⁻²·C⁻¹` (`V`) — thermoelectric voltage and Peltier coefficient. -/
def voltage : Dimension PhyslibBase := Dim.energy / Dim.charge
/-- Resistivity, `M·L³·T⁻¹·C⁻²` (`Ω·m`) — the residual resistivity. -/
def resistivity : Dimension PhyslibBase := voltage / Dim.current * Dim.length
/-- Energy density of states, `M⁻¹·L⁻⁵·T²` (`J⁻¹·m⁻³`). -/
def energyDOS : Dimension PhyslibBase := (Dim.energy * volume)⁻¹
/-- Lorenz coefficient, `M²·L⁴·T⁻⁴·C⁻²·Θ⁻²` (`V²/K²`). -/
def lorenz : Dimension PhyslibBase := (voltage * voltage) / (Dim.temperature * Dim.temperature)
/-- Hall coefficient, `L³·C⁻¹` (`m³/C`). -/
def hallCoeff : Dimension PhyslibBase := volume / Dim.charge
/-- Seebeck and Thomson coefficient, `M·L²·T⁻²·C⁻¹·Θ⁻¹` (`V/K`). -/
def seebeck : Dimension PhyslibBase := voltage / Dim.temperature
/-- Richardson constant, `C·T⁻¹·L⁻²·Θ⁻²` (`A·m⁻²·K⁻²`). -/
def richardson : Dimension PhyslibBase := Dim.current / (Dim.area * Dim.temperature * Dim.temperature)
/-- Magnetic flux density, `M·T⁻¹·C⁻¹` (`T`, the tesla) — the critical flux densities. -/
def magFluxDensity : Dimension PhyslibBase := (Dim.energy * Dim.time) / (Dim.charge * Dim.area)

end CDim

/-! ## (A) Lattice geometry (items 12-1.1 … 12-8) -/

def latticeVector : DimensionedKind := dimKind "lattice vector" Dim.length
def fundamentalLatticeVectors : DimensionedKind :=
  dimKind "fundamental lattice vectors" Dim.length
def angularReciprocalLatticeVector : DimensionedKind :=
  dimKind "angular reciprocal lattice vector" CDim.perLength
def fundamentalReciprocalLatticeVectors : DimensionedKind :=
  dimKind "fundamental reciprocal lattice vectors" CDim.perLength
def latticePlaneSpacing : DimensionedKind := dimKind "lattice plane spacing" Dim.length
def braggAngle : DimensionedKind := dimKind "Bragg angle" Dim.one
def shortRangeOrderParameter : DimensionedKind :=
  dimKind "short-range order parameter" Dim.one
def longRangeOrderParameter : DimensionedKind :=
  dimKind "long-range order parameter" Dim.one
def atomicScatteringFactor : DimensionedKind := dimKind "atomic scattering factor" Dim.one
def structureFactor : DimensionedKind := dimKind "structure factor" Dim.one
def burgersVector : DimensionedKind := dimKind "Burgers vector" Dim.length
def particlePositionVector : DimensionedKind :=
  dimKind "particle position vector" Dim.length
def equilibriumPositionVector : DimensionedKind :=
  dimKind "equilibrium position vector" Dim.length
def displacementVector : DimensionedKind := dimKind "displacement vector" Dim.length
def debyeWallerFactor : DimensionedKind := dimKind "Debye-Waller factor" Dim.one

/-! ## (B) Wavenumbers, Debye, Grüneisen, mean free paths (items 12-9.1 … 12-16) -/

def angularWavenumber : DimensionedKind := dimKind "angular wavenumber" CDim.perLength
def fermiAngularWavenumber : DimensionedKind :=
  dimKind "Fermi angular wavenumber" CDim.perLength
def debyeAngularWavenumber : DimensionedKind :=
  dimKind "Debye angular wavenumber" CDim.perLength
def debyeAngularFrequency : DimensionedKind :=
  dimKind "Debye angular frequency" CDim.perTime
def debyeTemperature : DimensionedKind := dimKind "Debye temperature" Dim.temperature
def densityOfVibrationalStates : DimensionedKind :=
  dimKind "density of vibrational states" CDim.vibrationalDOS
def thermodynamicGrueneisenParameter : DimensionedKind :=
  dimKind "thermodynamic Grüneisen parameter" Dim.one
def grueneisenParameter : DimensionedKind := dimKind "Grüneisen parameter" Dim.one
def meanFreePathPhonons : DimensionedKind := dimKind "mean free path of phonons" Dim.length
def meanFreePathElectrons : DimensionedKind :=
  dimKind "mean free path of electrons" Dim.length
def energyDensityOfStates : DimensionedKind :=
  dimKind "energy density of states" CDim.energyDOS

/-! ## (C) Transport and thermoelectric (items 12-17 … 12-23) -/

def residualResistivity : DimensionedKind := dimKind "residual resistivity" CDim.resistivity
def lorenzCoefficient : DimensionedKind := dimKind "Lorenz coefficient" CDim.lorenz
def hallCoefficient : DimensionedKind := dimKind "Hall coefficient" CDim.hallCoeff
def thermoelectricVoltage : DimensionedKind :=
  dimKind "thermoelectric voltage" CDim.voltage
def seebeckCoefficient : DimensionedKind := dimKind "Seebeck coefficient" CDim.seebeck
def peltierCoefficient : DimensionedKind := dimKind "Peltier coefficient" CDim.voltage
def thomsonCoefficient : DimensionedKind := dimKind "Thomson coefficient" CDim.seebeck

/-! ## (D) Work functions and band energies (items 12-24.1 … 12-28) -/

def workFunction : DimensionedKind := dimKind "work function" Dim.energy
def ionizationEnergy : DimensionedKind := dimKind "ionization energy" Dim.energy
def electronAffinity : DimensionedKind := dimKind "electron affinity" Dim.energy
def richardsonConstant : DimensionedKind := dimKind "Richardson constant" CDim.richardson
def fermiEnergy : DimensionedKind := dimKind "Fermi energy" Dim.energy
def gapEnergy : DimensionedKind := dimKind "gap energy" Dim.energy
def fermiTemperature : DimensionedKind := dimKind "Fermi temperature" Dim.temperature

/-! ## (E) Carrier densities and effective mass (items 12-29.1 … 12-33) -/

def electronDensity : DimensionedKind := dimKind "electron density" CDim.numberDensity
def holeDensity : DimensionedKind := dimKind "hole density" CDim.numberDensity
def intrinsicCarrierDensity : DimensionedKind :=
  dimKind "intrinsic carrier density" CDim.numberDensity
def donorDensity : DimensionedKind := dimKind "donor density" CDim.numberDensity
def acceptorDensity : DimensionedKind := dimKind "acceptor density" CDim.numberDensity
def effectiveMass : DimensionedKind := dimKind "effective mass" Dim.mass
def mobilityRatio : DimensionedKind := dimKind "mobility ratio" Dim.one
def relaxationTime : DimensionedKind := dimKind "relaxation time" Dim.time
def carrierLifetime : DimensionedKind := dimKind "carrier lifetime" Dim.time
def diffusionLength : DimensionedKind := dimKind "diffusion length" Dim.length

/-! ## (F) Magnetism and superconductivity (items 12-34 … 12-38.2) -/

def exchangeIntegral : DimensionedKind := dimKind "exchange integral" Dim.energy
def curieTemperature : DimensionedKind := dimKind "Curie temperature" Dim.temperature
def neelTemperature : DimensionedKind := dimKind "Néel temperature" Dim.temperature
def superconductionTransitionTemperature : DimensionedKind :=
  dimKind "superconduction transition temperature" Dim.temperature
def thermodynamicCriticalFluxDensity : DimensionedKind :=
  dimKind "thermodynamic critical magnetic flux density" CDim.magFluxDensity
def lowerCriticalFluxDensity : DimensionedKind :=
  dimKind "lower critical magnetic flux density" CDim.magFluxDensity
def upperCriticalFluxDensity : DimensionedKind :=
  dimKind "upper critical magnetic flux density" CDim.magFluxDensity
def superconductorEnergyGap : DimensionedKind :=
  dimKind "superconductor energy gap" Dim.energy
def londonPenetrationDepth : DimensionedKind :=
  dimKind "London penetration depth" Dim.length
def coherenceLength : DimensionedKind := dimKind "coherence length" Dim.length

/-! ## The catalogue (every kind, with its source as data) -/

def latticeVectorCK : CataloguedKind := cat "12-1.1" "R" "m" latticeVector
def fundamentalLatticeVectorsCK : CataloguedKind :=
  cat "12-1.2" "a₁" "m" fundamentalLatticeVectors
def angularReciprocalLatticeVectorCK : CataloguedKind :=
  cat "12-2.1" "G" "m⁻¹" angularReciprocalLatticeVector
def fundamentalReciprocalLatticeVectorsCK : CataloguedKind :=
  cat "12-2.2" "b₁" "m⁻¹" fundamentalReciprocalLatticeVectors
def latticePlaneSpacingCK : CataloguedKind := cat "12-3" "d" "m" latticePlaneSpacing
def braggAngleCK : CataloguedKind := cat "12-4" "ϑ" "1" braggAngle
def shortRangeOrderParameterCK : CataloguedKind :=
  cat "12-5.1" "r" "1" shortRangeOrderParameter
def longRangeOrderParameterCK : CataloguedKind :=
  cat "12-5.2" "R" "1" longRangeOrderParameter
def atomicScatteringFactorCK : CataloguedKind :=
  cat "12-5.3" "f" "1" atomicScatteringFactor
def structureFactorCK : CataloguedKind := cat "12-5.4" "F" "1" structureFactor
def burgersVectorCK : CataloguedKind := cat "12-6" "b" "m" burgersVector
def particlePositionVectorCK : CataloguedKind :=
  cat "12-7.1" "r" "m" particlePositionVector
def equilibriumPositionVectorCK : CataloguedKind :=
  cat "12-7.2" "R₀" "m" equilibriumPositionVector
def displacementVectorCK : CataloguedKind := cat "12-7.3" "u" "m" displacementVector
def debyeWallerFactorCK : CataloguedKind := cat "12-8" "D" "1" debyeWallerFactor
def angularWavenumberCK : CataloguedKind := cat "12-9.1" "k" "m⁻¹" angularWavenumber
def fermiAngularWavenumberCK : CataloguedKind :=
  cat "12-9.2" "k_F" "m⁻¹" fermiAngularWavenumber
def debyeAngularWavenumberCK : CataloguedKind :=
  cat "12-9.3" "q_D" "m⁻¹" debyeAngularWavenumber
def debyeAngularFrequencyCK : CataloguedKind := cat "12-10" "ω_D" "s⁻¹" debyeAngularFrequency
def debyeTemperatureCK : CataloguedKind := cat "12-11" "Θ_D" "K" debyeTemperature
def densityOfVibrationalStatesCK : CataloguedKind :=
  cat "12-12" "g" "m⁻³·s" densityOfVibrationalStates
def thermodynamicGrueneisenParameterCK : CataloguedKind :=
  cat "12-13" "γ_G" "1" thermodynamicGrueneisenParameter
def grueneisenParameterCK : CataloguedKind := cat "12-14" "γ" "1" grueneisenParameter
def meanFreePathPhononsCK : CataloguedKind := cat "12-15.1" "l_p" "m" meanFreePathPhonons
def meanFreePathElectronsCK : CataloguedKind :=
  cat "12-15.2" "l_e" "m" meanFreePathElectrons
def energyDensityOfStatesCK : CataloguedKind :=
  cat "12-16" "n_E" "J⁻¹·m⁻³" energyDensityOfStates
def residualResistivityCK : CataloguedKind := cat "12-17" "ρ₀" "Ω·m" residualResistivity
def lorenzCoefficientCK : CataloguedKind := cat "12-18" "L" "V²/K²" lorenzCoefficient
def hallCoefficientCK : CataloguedKind := cat "12-19" "R_H" "m³/C" hallCoefficient
def thermoelectricVoltageCK : CataloguedKind :=
  cat "12-20" "E_ab" "V" thermoelectricVoltage
def seebeckCoefficientCK : CataloguedKind := cat "12-21" "S_ab" "V/K" seebeckCoefficient
def peltierCoefficientCK : CataloguedKind := cat "12-22" "Π_ab" "V" peltierCoefficient
def thomsonCoefficientCK : CataloguedKind := cat "12-23" "μ" "V/K" thomsonCoefficient
def workFunctionCK : CataloguedKind := cat "12-24.1" "φ" "J" workFunction
def ionizationEnergyCK : CataloguedKind := cat "12-24.2" "E_i" "J" ionizationEnergy
def electronAffinityCK : CataloguedKind := cat "12-25" "χ" "J" electronAffinity
def richardsonConstantCK : CataloguedKind :=
  cat "12-26" "A" "A·m⁻²·K⁻²" richardsonConstant
def fermiEnergyCK : CataloguedKind := cat "12-27.1" "E_F" "J" fermiEnergy
def gapEnergyCK : CataloguedKind := cat "12-27.2" "E_g" "J" gapEnergy
def fermiTemperatureCK : CataloguedKind := cat "12-28" "T_F" "K" fermiTemperature
def electronDensityCK : CataloguedKind := cat "12-29.1" "n" "m⁻³" electronDensity
def holeDensityCK : CataloguedKind := cat "12-29.2" "p" "m⁻³" holeDensity
def intrinsicCarrierDensityCK : CataloguedKind :=
  cat "12-29.3" "n_i" "m⁻³" intrinsicCarrierDensity
def donorDensityCK : CataloguedKind := cat "12-29.4" "n_d" "m⁻³" donorDensity
def acceptorDensityCK : CataloguedKind := cat "12-29.5" "n_a" "m⁻³" acceptorDensity
def effectiveMassCK : CataloguedKind := cat "12-30" "m*" "kg" effectiveMass
def mobilityRatioCK : CataloguedKind := cat "12-31" "b" "1" mobilityRatio
def relaxationTimeCK : CataloguedKind := cat "12-32.1" "τ" "s" relaxationTime
def carrierLifetimeCK : CataloguedKind := cat "12-32.2" "τ" "s" carrierLifetime
def diffusionLengthCK : CataloguedKind := cat "12-33" "L" "m" diffusionLength
def exchangeIntegralCK : CataloguedKind := cat "12-34" "J" "J" exchangeIntegral
def curieTemperatureCK : CataloguedKind := cat "12-35.1" "T_C" "K" curieTemperature
def neelTemperatureCK : CataloguedKind := cat "12-35.2" "T_N" "K" neelTemperature
def superconductionTransitionTemperatureCK : CataloguedKind :=
  cat "12-35.3" "T_c" "K" superconductionTransitionTemperature
def thermodynamicCriticalFluxDensityCK : CataloguedKind :=
  cat "12-36.1" "B_c" "T" thermodynamicCriticalFluxDensity
def lowerCriticalFluxDensityCK : CataloguedKind :=
  cat "12-36.2" "B_c1" "T" lowerCriticalFluxDensity
def upperCriticalFluxDensityCK : CataloguedKind :=
  cat "12-36.3" "B_c2" "T" upperCriticalFluxDensity
def superconductorEnergyGapCK : CataloguedKind :=
  cat "12-37" "Δ" "J" superconductorEnergyGap
def londonPenetrationDepthCK : CataloguedKind :=
  cat "12-38.1" "λ_L" "m" londonPenetrationDepth
def coherenceLengthCK : CataloguedKind := cat "12-38.2" "ξ" "m" coherenceLength

/-- The full ISO 80000-12 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [latticeVectorCK, fundamentalLatticeVectorsCK, angularReciprocalLatticeVectorCK,
   fundamentalReciprocalLatticeVectorsCK, latticePlaneSpacingCK, braggAngleCK,
   shortRangeOrderParameterCK, longRangeOrderParameterCK, atomicScatteringFactorCK,
   structureFactorCK, burgersVectorCK, particlePositionVectorCK, equilibriumPositionVectorCK,
   displacementVectorCK, debyeWallerFactorCK, angularWavenumberCK, fermiAngularWavenumberCK,
   debyeAngularWavenumberCK, debyeAngularFrequencyCK, debyeTemperatureCK,
   densityOfVibrationalStatesCK, thermodynamicGrueneisenParameterCK, grueneisenParameterCK,
   meanFreePathPhononsCK, meanFreePathElectronsCK, energyDensityOfStatesCK,
   residualResistivityCK, lorenzCoefficientCK, hallCoefficientCK, thermoelectricVoltageCK,
   seebeckCoefficientCK, peltierCoefficientCK, thomsonCoefficientCK, workFunctionCK,
   ionizationEnergyCK, electronAffinityCK, richardsonConstantCK, fermiEnergyCK, gapEnergyCK,
   fermiTemperatureCK, electronDensityCK, holeDensityCK, intrinsicCarrierDensityCK,
   donorDensityCK, acceptorDensityCK, effectiveMassCK, mobilityRatioCK, relaxationTimeCK,
   carrierLifetimeCK, diffusionLengthCK, exchangeIntegralCK, curieTemperatureCK,
   neelTemperatureCK, superconductionTransitionTemperatureCK,
   thermodynamicCriticalFluxDensityCK, lowerCriticalFluxDensityCK, upperCriticalFluxDensityCK,
   superconductorEnergyGapCK, londonPenetrationDepthCK, coherenceLengthCK]

/-! ## (G) Units — the energy and temperature collisions

The joule of Fermi energy and the joule of gap energy carry the same dimension `M·L²·T⁻²`,
yet are not commensurable; and the kelvin of Curie temperature and the kelvin of Néel
temperature carry the same dimension `Θ`, yet are not commensurable either. -/

/-- The joule of Fermi energy (item 12-27.1). -/
def jouleFermi : MetrologicalUnit := fermiEnergy.kind.unit "J"
/-- The joule of gap energy (item 12-27.2) — *also* `M·L²·T⁻²`. -/
def jouleGap : MetrologicalUnit := gapEnergy.kind.unit "J"
/-- The kelvin of Curie temperature (item 12-35.1). -/
def kelvinCurie : MetrologicalUnit := curieTemperature.kind.unit "K"
/-- The kelvin of Néel temperature (item 12-35.2) — *also* `Θ`. -/
def kelvinNeel : MetrologicalUnit := neelTemperature.kind.unit "K"

/-! ## (H) Checked dimensional facts (the dimensional algebra) -/

/-- The Fermi energy is `M·L²·T⁻²` — its time-exponent is `-2` (item 12-27.1). -/
theorem fermiEnergy_dim_time : fermiEnergy.dim.time = -2 := Dim.energy_time

/-- The lattice plane spacing is a length `L` (item 12-3). -/
theorem latticePlaneSpacing_dim_eq_length : latticePlaneSpacing.dim = Dim.length := rfl

/-- The Debye temperature carries temperature-exponent `1` — the generator `Θ` (item
12-11). -/
theorem debyeTemperature_dim_temperature : debyeTemperature.dim.temperature = 1 :=
  Dim.temperature_temperature

/-- The angular wavenumber is a reciprocal length `L⁻¹` — its length-exponent is `-1`
(item 12-9.1). -/
theorem angularWavenumber_dim_length : angularWavenumber.dim.length = -1 := by
  norm_num [angularWavenumber, dimKind, CDim.perLength, Dim.length, Dimension.inv_length,
    Dimension.L𝓭_length]

/-! ## (I) Unit well-formedness and (in)commensurability -/

/-- The joule of Fermi energy is a well-formed unit. -/
theorem jouleFermi_wellFormed : jouleFermi.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- **The joule of Fermi energy and the joule of gap energy are not commensurable, though
both are `M·L²·T⁻²`.** Same unit, same dimension, different kind. -/
theorem jouleFermi_jouleGap_not_commensurable :
    ¬ jouleFermi.Commensurable jouleGap := by
  unfold MetrologicalUnit.Commensurable jouleFermi jouleGap fermiEnergy gapEnergy dimKind
    KindOfProperty.unit
  decide

/-- **The kelvin of Curie temperature and the kelvin of Néel temperature are not
commensurable, though both are `Θ`.** Five named temperatures, one dimension, one unit
symbol — the kind layer keeps them apart. -/
theorem kelvinCurie_kelvinNeel_not_commensurable :
    ¬ kelvinCurie.Commensurable kelvinNeel := by
  unfold MetrologicalUnit.Commensurable kelvinCurie kelvinNeel curieTemperature
    neelTemperature dimKind KindOfProperty.unit
  decide

/-! ## (J) Dimension collisions — the kind classifies where the dimension cannot -/

/-- Fermi energy and gap energy share dimension `M·L²·T⁻²`. -/
theorem fermiEnergy_dim_eq_gapEnergy_dim : fermiEnergy.dim = gapEnergy.dim := rfl

/-- The lattice plane spacing and the Burgers vector share dimension `L`. -/
theorem latticePlaneSpacing_dim_eq_burgersVector_dim :
    latticePlaneSpacing.dim = burgersVector.dim := rfl

/-- The Curie and Néel temperatures share dimension `Θ`. -/
theorem curieTemperature_dim_eq_neelTemperature_dim :
    curieTemperature.dim = neelTemperature.dim := rfl

/-- Fermi energy is not gap energy, though both are `M·L²·T⁻²`. -/
theorem fermiEnergy_ne_gapEnergy : fermiEnergy.kind ≠ gapEnergy.kind := by
  unfold fermiEnergy gapEnergy dimKind; decide

/-- The Bragg angle is not the structure factor, though both are dimension one. -/
theorem braggAngle_ne_structureFactor : braggAngle.kind ≠ structureFactor.kind := by
  unfold braggAngle structureFactor dimKind; decide

/-- **The dimension-collision capstone, on the standard — collisions everywhere.** There
exist distinct ISO 80000-12 kinds with the same dimension `M·L²·T⁻²` — the Fermi energy and
the gap energy witness it, alongside the work function, ionization energy, electron
affinity, exchange integral, and superconductor energy gap (seven energies). The
{dimension functor} cannot separate them; the kind layer does. -/
theorem iso80000_12_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨fermiEnergy, gapEnergy, fermiEnergy_ne_gapEnergy, fermiEnergy_dim_eq_gapEnergy_dim⟩

/-- **The dimension-one disambiguation, on the standard.** There exist distinct
ISO 80000-12 kinds with the same dimension one — the Bragg angle and the structure factor
witness it, alongside the order parameters, the scattering factor, the Debye-Waller factor,
the Grüneisen parameters, and the mobility ratio. Dimension cannot separate them; the kind
layer does. -/
theorem iso80000_12_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨braggAngle, structureFactor, braggAngle_ne_structureFactor, rfl, rfl⟩

end PropertyKindCalculus.Iso80000.Part12
