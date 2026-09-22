/-
# ISO 80000-10 — Atomic and nuclear physics (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
ISO 80000-10 *Atomic and nuclear physics* — all of items 10-1.1 … 10-89, every
sub-suffixed item included, one hundred and twenty-five in all — each carrying its exact
source as data: the part (`iso80000_10`), the printed item designation, the principal
quantity symbol, and the coherent SI unit symbol. Only **citation locators** are recorded;
no normative content from the licensed standard is reproduced. The defining *mathematics*
of selected remarks is formalized in the sibling module `Part10.DefiningRelations`.

Atomic and nuclear physics holds the series' clearest case of *one unit, two kinds the
unit must keep apart by name* — the gray and the sievert — and a second, the becquerel:

* **The gray/sievert collision — the standard's own `J/kg` disambiguation.** The absorbed
  dose (10-81.1, `Gy`), the specific energy imparted (10-81.2, `Gy`), the kerma (10-86.1,
  `Gy`), and the dose equivalent (10-83.1, `Sv`) all carry the *same* dimension `L²·T⁻²`
  (energy per mass), and the standard assigns them *two different special unit names* —
  gray for the physical doses, sievert for the biologically-weighted one — precisely
  *because the kinds differ*. This is the entropy-vs-heat-capacity `J/K` collision of
  ISO 80000-5 made even sharper: here the standard itself coins distinct unit names for one
  dimension, the strongest external confirmation of the *dimension does not classify the
  kind* thesis.

* **The becquerel collision.** The activity (10-27, `Bq`) carries dimension `T⁻¹`, shared
  with the decay constant (10-24, `s⁻¹`), the particle emission rate (10-36), and the
  Larmor and cyclotron angular frequencies (10-15.*, 10-16). The becquerel is the special
  name SI reserves for `s⁻¹` *as the unit of activity* — a kind distinction the dimension
  cannot see.

* **The widest dimension-one family in the physical parts.** The atomic, neutron, and
  nucleon numbers, the eight quantum numbers, the two g-factors, the relative mass excess
  and defect, the packing and binding fractions, the internal conversion and quality
  factors, the total ionization, and the reactor factors (resonance escape, fast fission,
  thermal utilization, non-leakage, multiplication) — dozens of distinct kinds the
  {dimension functor} sends to the single point one.

* **The mole reduces here too.** The molar attenuation coefficient (10-51, `m²/mol`) is an
  **area** once the mole reads as the dimensionless count `N_A` (R13).

* **The dimensional facts are checked computations**, discharged in PhysLib's dimension
  group over mass, length, time, and charge.
-/

module

public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.ScaleSpanning
public import PropertyKindCalculus.Iso80000.References
public import PropertyKindCalculus.Iso80000.Catalogue

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Iso80000.Part10

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_10

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Atomic and nuclear dimensions

The dimensions of atomic and nuclear physics, composed in PhysLib's `Dimension` group from
mass `M`, length `L`, time `T`, and charge `C`. The steradian and the mole are dimension
one (the scale-spanning reduction, R13), so a cross section per solid angle is still an
area and a molar attenuation coefficient an area. -/

namespace NDim

/-- Volume, `L³`. -/
def volume : Dimension LTMCTDimensionBase := Dim.area * Dim.length
/-- Per time, `T⁻¹` — activity (the becquerel), decay constant, emission rate, the Larmor
and cyclotron angular frequencies. -/
def perTime : Dimension LTMCTDimensionBase := Dim.time⁻¹
/-- **Specific energy (dose), `L²·T⁻²`** — energy per mass (`J/kg`): the absorbed dose, the
specific energy imparted, the kerma (all `Gy`), and the dose equivalent (`Sv`) all share
it. -/
def specificEnergy : Dimension LTMCTDimensionBase := Dim.energy / Dim.mass
/-- Specific energy rate, `L²·T⁻³` — power per mass (`W/kg`): the dose-equivalent, absorbed-
dose, and kerma rates. -/
def specificEnergyRate : Dimension LTMCTDimensionBase := Dim.power / Dim.mass
/-- Magnetic dipole moment, `L²·C·T⁻¹` (`m²·A`) — the magnetic moment and the Bohr and
nuclear magnetons. -/
def magneticMoment : Dimension LTMCTDimensionBase := Dim.area * Dim.current
/-- Angular momentum, `M·L²·T⁻¹` (`J·s`) — spin and total angular momentum. -/
def angularMomentum : Dimension LTMCTDimensionBase := Dim.energy * Dim.time
/-- Gyromagnetic ratio, `M⁻¹·C` (`A·m²·J⁻¹·s⁻¹`) — magnetic moment per angular momentum. -/
def gyromagneticRatio : Dimension LTMCTDimensionBase := magneticMoment / angularMomentum
/-- Per length, `L⁻¹` (`m⁻¹`) — the Rydberg constant, the macroscopic cross section, the
linear attenuation coefficient, the linear ionization. -/
def perLength : Dimension LTMCTDimensionBase := Dim.length⁻¹
/-- Mass attenuation coefficient, `M⁻¹·L²` (`kg⁻¹·m²`) — also the mass energy-transfer
coefficient. -/
def massAttenuation : Dimension LTMCTDimensionBase := Dim.area / Dim.mass
/-- Number density, `L⁻³` (`m⁻³`) — particle and ion number densities. -/
def numberDensity : Dimension LTMCTDimensionBase := volume⁻¹
/-- Particle fluence, `L⁻²` (`m⁻²`). -/
def particleFluence : Dimension LTMCTDimensionBase := Dim.area⁻¹
/-- Fluence rate, `L⁻²·T⁻¹` (`m⁻²·s⁻¹`) — particle fluence rate, particle current density,
and the surface-activity density (`Bq/m²`). -/
def fluenceRate : Dimension LTMCTDimensionBase := (Dim.area * Dim.time)⁻¹
/-- Activity per mass, `M⁻¹·T⁻¹` (`Bq/kg`) — the specific (massic) activity. -/
def activityPerMass : Dimension LTMCTDimensionBase := perTime / Dim.mass
/-- Activity density, `L⁻³·T⁻¹` (`Bq/m³`) — also the particle source density and slowing-
down density (`m⁻³·s⁻¹`). -/
def activityDensity : Dimension LTMCTDimensionBase := (volume * Dim.time)⁻¹
/-- Cross section per energy, `M⁻¹·T²` (`m²/J`) — the energy-distributed cross sections. -/
def crossSectionPerEnergy : Dimension LTMCTDimensionBase := Dim.area / Dim.energy
/-- Energy fluence, `M·T⁻²` (`J/m²`). -/
def energyFluence : Dimension LTMCTDimensionBase := Dim.energy / Dim.area
/-- Energy fluence rate, `M·T⁻³` (`W/m²`). -/
def energyFluenceRate : Dimension LTMCTDimensionBase := Dim.power / Dim.area
/-- Linear stopping power, `M·L·T⁻²` (`J/m`) — also the linear energy transfer (LET). -/
def linearStoppingPower : Dimension LTMCTDimensionBase := Dim.energy / Dim.length
/-- Mass stopping power, `L⁴·T⁻²` (`J·m²/kg`). -/
def massStoppingPower : Dimension LTMCTDimensionBase := Dim.energy * Dim.area / Dim.mass
/-- Mean mass range, `M·L⁻²` (`kg·m⁻²`). -/
def massRange : Dimension LTMCTDimensionBase := Dim.mass / Dim.area
/-- Voltage, `M·L²·T⁻²·C⁻¹` — used to compose mobility. -/
def voltage : Dimension LTMCTDimensionBase := Dim.energy / Dim.charge
/-- Mobility, `M⁻¹·T·C` (`m²/(V·s)`). -/
def mobility : Dimension LTMCTDimensionBase := Dim.area / (voltage * Dim.time)
/-- Recombination coefficient, `L³·T⁻¹` (`m³·s⁻¹`). -/
def recombination : Dimension LTMCTDimensionBase := volume / Dim.time
/-- Diffusion coefficient, `L²·T⁻¹` (`m²/s`). -/
def diffusionCoefficient : Dimension LTMCTDimensionBase := Dim.area / Dim.time
/-- Exposure, `M⁻¹·C` (`C/kg`). -/
def exposure : Dimension LTMCTDimensionBase := Dim.charge / Dim.mass
/-- Exposure rate, `M⁻¹·T⁻¹·C` (`C/(kg·s)`). -/
def exposureRate : Dimension LTMCTDimensionBase := exposure / Dim.time

end NDim

/-! ## (A) Nucleon numbers, masses, charge (items 10-1.1 … 10-5.2) -/

def atomicNumber : DimensionedKind := dimKind "atomic number" Dim.one
def neutronNumber : DimensionedKind := dimKind "neutron number" Dim.one
def nucleonNumber : DimensionedKind := dimKind "nucleon number" Dim.one
def restMass : DimensionedKind := dimKind "rest mass" Dim.mass
def restEnergy : DimensionedKind := dimKind "rest energy" Dim.energy
def atomicMass : DimensionedKind := dimKind "atomic mass" Dim.mass
def nuclidicMass : DimensionedKind := dimKind "nuclidic mass" Dim.mass
def unifiedAtomicMassConstant : DimensionedKind :=
  dimKind "unified atomic mass constant" Dim.mass
def elementaryCharge : DimensionedKind := dimKind "elementary charge" Dim.charge
def chargeNumber : DimensionedKind := dimKind "charge number" Dim.one

/-! ## (B) Atomic constants and magnetic moments (items 10-6 … 10-12.2) -/

def bohrRadius : DimensionedKind := dimKind "Bohr radius" Dim.length
def rydbergConstant : DimensionedKind := dimKind "Rydberg constant" NDim.perLength
def hartreeEnergy : DimensionedKind := dimKind "Hartree energy" Dim.energy
def magneticDipoleMoment : DimensionedKind :=
  dimKind "magnetic dipole moment" NDim.magneticMoment
def bohrMagneton : DimensionedKind := dimKind "Bohr magneton" NDim.magneticMoment
def nuclearMagneton : DimensionedKind := dimKind "nuclear magneton" NDim.magneticMoment
def spin : DimensionedKind := dimKind "spin" NDim.angularMomentum
def totalAngularMomentum : DimensionedKind :=
  dimKind "total angular momentum" NDim.angularMomentum
def gyromagneticRatio : DimensionedKind :=
  dimKind "gyromagnetic ratio" NDim.gyromagneticRatio
def gyromagneticRatioElectron : DimensionedKind :=
  dimKind "gyromagnetic ratio of the electron" NDim.gyromagneticRatio

/-! ## (C) The quantum numbers and g-factors (items 10-13.1 … 10-14.2) — all dimension one -/

def quantumNumber : DimensionedKind := dimKind "quantum number" Dim.one
def principalQuantumNumber : DimensionedKind := dimKind "principal quantum number" Dim.one
def orbitalQuantumNumber : DimensionedKind :=
  dimKind "orbital angular momentum quantum number" Dim.one
def magneticQuantumNumber : DimensionedKind := dimKind "magnetic quantum number" Dim.one
def spinQuantumNumber : DimensionedKind := dimKind "spin quantum number" Dim.one
def totalAngularMomentumQuantumNumber : DimensionedKind :=
  dimKind "total angular momentum quantum number" Dim.one
def nuclearSpinQuantumNumber : DimensionedKind :=
  dimKind "nuclear spin quantum number" Dim.one
def hyperfineQuantumNumber : DimensionedKind :=
  dimKind "hyperfine structure quantum number" Dim.one
def landeFactor : DimensionedKind := dimKind "Landé factor" Dim.one
def gFactorNucleus : DimensionedKind := dimKind "g factor of nucleus" Dim.one

/-! ## (D) Precession frequencies and orbit radii (items 10-15.1 … 10-20) -/

def larmorAngularFrequency : DimensionedKind :=
  dimKind "Larmor angular frequency" NDim.perTime
def larmorFrequency : DimensionedKind := dimKind "Larmor frequency" NDim.perTime
def nuclearPrecessionAngularFrequency : DimensionedKind :=
  dimKind "nuclear precession angular frequency" NDim.perTime
def cyclotronAngularFrequency : DimensionedKind :=
  dimKind "cyclotron angular frequency" NDim.perTime
def gyroradius : DimensionedKind := dimKind "gyroradius" Dim.length
def nuclearQuadrupoleMoment : DimensionedKind :=
  dimKind "nuclear quadrupole moment" Dim.area
def nuclearRadius : DimensionedKind := dimKind "nuclear radius" Dim.length
def electronRadius : DimensionedKind := dimKind "electron radius" Dim.length
def comptonWavelength : DimensionedKind := dimKind "Compton wavelength" Dim.length

/-! ## (E) Mass excess and defect, fractions (items 10-21.1 … 10-23.2) -/

def massExcess : DimensionedKind := dimKind "mass excess" Dim.mass
def massDefect : DimensionedKind := dimKind "mass defect" Dim.mass
def relativeMassExcess : DimensionedKind := dimKind "relative mass excess" Dim.one
def relativeMassDefect : DimensionedKind := dimKind "relative mass defect" Dim.one
def packingFraction : DimensionedKind := dimKind "packing fraction" Dim.one
def bindingFraction : DimensionedKind := dimKind "binding fraction" Dim.one

/-! ## (F) Decay, activity, and its densities (items 10-24 … 10-31)

The decay constant (10-24) and activity (10-27) are both `T⁻¹` — the becquerel collision;
the mean life (10-25), half life (10-31) are times; the level width (10-26) an energy. -/

def decayConstant : DimensionedKind := dimKind "decay constant" NDim.perTime
def meanLife : DimensionedKind := dimKind "mean duration of life" Dim.time
def levelWidth : DimensionedKind := dimKind "level width" Dim.energy
def activity : DimensionedKind := dimKind "activity" NDim.perTime
def specificActivity : DimensionedKind := dimKind "specific activity" NDim.activityPerMass
def activityDensity : DimensionedKind := dimKind "activity density" NDim.activityDensity
def surfaceActivityDensity : DimensionedKind :=
  dimKind "surface-activity density" NDim.fluenceRate
def halfLife : DimensionedKind := dimKind "half life" Dim.time

/-! ## (G) Disintegration energies, conversion, emission (items 10-32 … 10-37.2) -/

def alphaDisintegrationEnergy : DimensionedKind :=
  dimKind "alpha disintegration energy" Dim.energy
def maximumBetaParticleEnergy : DimensionedKind :=
  dimKind "maximum beta-particle energy" Dim.energy
def betaDisintegrationEnergy : DimensionedKind :=
  dimKind "beta disintegration energy" Dim.energy
def internalConversionFactor : DimensionedKind :=
  dimKind "internal conversion factor" Dim.one
def particleEmissionRate : DimensionedKind :=
  dimKind "particle emission rate" NDim.perTime
def reactionEnergy : DimensionedKind := dimKind "reaction energy" Dim.energy
def resonanceEnergy : DimensionedKind := dimKind "resonance energy" Dim.energy

/-! ## (H) Cross sections and their distributions (items 10-38.1 … 10-42.2) -/

def crossSection : DimensionedKind := dimKind "cross section" Dim.area
def totalCrossSection : DimensionedKind := dimKind "total cross section" Dim.area
def directionCrossSection : DimensionedKind :=
  dimKind "direction distribution of cross section" Dim.area
def energyCrossSection : DimensionedKind :=
  dimKind "energy distribution of cross section" NDim.crossSectionPerEnergy
def directionEnergyCrossSection : DimensionedKind :=
  dimKind "direction and energy distribution of cross section" NDim.crossSectionPerEnergy
def macroscopicCrossSection : DimensionedKind :=
  dimKind "macroscopic cross section" NDim.perLength
def macroscopicTotalCrossSection : DimensionedKind :=
  dimKind "macroscopic total cross section" NDim.perLength

/-! ## (I) Fluence, energy fluence, current (items 10-43 … 10-48) -/

def particleFluence : DimensionedKind := dimKind "particle fluence" NDim.particleFluence
def particleFluenceRate : DimensionedKind :=
  dimKind "particle fluence rate" NDim.fluenceRate
def radiantEnergy : DimensionedKind := dimKind "radiant energy" Dim.energy
def energyFluence : DimensionedKind := dimKind "energy fluence" NDim.energyFluence
def energyFluenceRate : DimensionedKind :=
  dimKind "energy fluence rate" NDim.energyFluenceRate
def particleCurrentDensity : DimensionedKind :=
  dimKind "particle current density" NDim.fluenceRate

/-! ## (J) Attenuation and stopping (items 10-49 … 10-60) -/

def linearAttenuationCoefficient : DimensionedKind :=
  dimKind "linear attenuation coefficient" NDim.perLength
def massAttenuationCoefficient : DimensionedKind :=
  dimKind "mass attenuation coefficient" NDim.massAttenuation
def molarAttenuationCoefficient : DimensionedKind :=
  dimKind "molar attenuation coefficient" Dim.area
def atomicAttenuationCoefficient : DimensionedKind :=
  dimKind "atomic attenuation coefficient" Dim.area
def halfValueThickness : DimensionedKind := dimKind "half-value thickness" Dim.length
def totalLinearStoppingPower : DimensionedKind :=
  dimKind "total linear stopping power" NDim.linearStoppingPower
def totalMassStoppingPower : DimensionedKind :=
  dimKind "total mass stopping power" NDim.massStoppingPower
def meanLinearRange : DimensionedKind := dimKind "mean linear range" Dim.length
def meanMassRange : DimensionedKind := dimKind "mean mass range" NDim.massRange
def linearIonization : DimensionedKind := dimKind "linear ionization" NDim.perLength
def totalIonization : DimensionedKind := dimKind "total ionization" Dim.one
def averageEnergyPerCharge : DimensionedKind :=
  dimKind "average energy loss per elementary charge produced" Dim.energy

/-! ## (K) Transport in matter (items 10-61 … 10-73.3) -/

def mobility : DimensionedKind := dimKind "mobility" NDim.mobility
def particleNumberDensity : DimensionedKind :=
  dimKind "particle number density" NDim.numberDensity
def ionNumberDensity : DimensionedKind := dimKind "ion number density" NDim.numberDensity
def recombinationCoefficient : DimensionedKind :=
  dimKind "recombination coefficient" NDim.recombination
def diffusionCoefficient : DimensionedKind :=
  dimKind "diffusion coefficient" NDim.diffusionCoefficient
def diffusionCoefficientFluence : DimensionedKind :=
  dimKind "diffusion coefficient for fluence rate" Dim.length
def particleSourceDensity : DimensionedKind :=
  dimKind "particle source density" NDim.activityDensity
def slowingDownDensity : DimensionedKind :=
  dimKind "slowing-down density" NDim.activityDensity
def resonanceEscapeProbability : DimensionedKind :=
  dimKind "resonance escape probability" Dim.one
def lethargy : DimensionedKind := dimKind "lethargy" Dim.one
def averageLogarithmicEnergyDecrement : DimensionedKind :=
  dimKind "average logarithmic energy decrement" Dim.one
def meanFreePath : DimensionedKind := dimKind "mean free path" Dim.length
def slowingDownArea : DimensionedKind := dimKind "slowing-down area" Dim.area
def diffusionArea : DimensionedKind := dimKind "diffusion area" Dim.area
def migrationArea : DimensionedKind := dimKind "migration area" Dim.area
def slowingDownLength : DimensionedKind := dimKind "slowing-down length" Dim.length
def diffusionLength : DimensionedKind := dimKind "diffusion length" Dim.length
def migrationLength : DimensionedKind := dimKind "migration length" Dim.length

/-! ## (L) Reactor factors (items 10-74.1 … 10-79) — all dimension one but the time -/

def neutronYieldPerFission : DimensionedKind :=
  dimKind "neutron yield per fission" Dim.one
def neutronYieldPerAbsorption : DimensionedKind :=
  dimKind "neutron yield per absorption" Dim.one
def fastFissionFactor : DimensionedKind := dimKind "fast fission factor" Dim.one
def thermalUtilizationFactor : DimensionedKind :=
  dimKind "thermal utilization factor" Dim.one
def nonLeakageProbability : DimensionedKind := dimKind "non-leakage probability" Dim.one
def multiplicationFactor : DimensionedKind := dimKind "multiplication factor" Dim.one
def infiniteMultiplicationFactor : DimensionedKind :=
  dimKind "infinite multiplication factor" Dim.one
def reactorTimeConstant : DimensionedKind := dimKind "reactor time constant" Dim.time

/-! ## (M) Dosimetry — the gray/sievert family (items 10-80.1 … 10-89)

The energy imparted (10-80.*) is an energy; the absorbed dose, specific energy imparted,
and kerma (10-81.*, 10-86.1) are `Gy`; the dose equivalent (10-83.1) is `Sv` — the *same*
dimension `L²·T⁻²`, a distinct kind, a distinct special unit. The dose rates (10-83.2,
10-84, 10-86.2) are `W/kg`; exposure (10-88) and its rate (10-89) are `C/kg`. -/

def energyImparted : DimensionedKind := dimKind "energy imparted" Dim.energy
def meanEnergyImparted : DimensionedKind := dimKind "mean energy imparted" Dim.energy
def absorbedDose : DimensionedKind := dimKind "absorbed dose" NDim.specificEnergy
def specificEnergyImparted : DimensionedKind :=
  dimKind "specific energy imparted" NDim.specificEnergy
def qualityFactor : DimensionedKind := dimKind "quality factor" Dim.one
def doseEquivalent : DimensionedKind := dimKind "dose equivalent" NDim.specificEnergy
def doseEquivalentRate : DimensionedKind :=
  dimKind "dose equivalent rate" NDim.specificEnergyRate
def absorbedDoseRate : DimensionedKind :=
  dimKind "absorbed-dose rate" NDim.specificEnergyRate
def linearEnergyTransfer : DimensionedKind :=
  dimKind "linear energy transfer" NDim.linearStoppingPower
def kerma : DimensionedKind := dimKind "kerma" NDim.specificEnergy
def kermaRate : DimensionedKind := dimKind "kerma rate" NDim.specificEnergyRate
def massEnergyTransferCoefficient : DimensionedKind :=
  dimKind "mass energy-transfer coefficient" NDim.massAttenuation
def exposure : DimensionedKind := dimKind "exposure" NDim.exposure
def exposureRate : DimensionedKind := dimKind "exposure rate" NDim.exposureRate

/-! ## The catalogue (every kind, with its source as data) -/

def atomicNumberCK : CataloguedKind := cat "10-1.1" "Z" "1" atomicNumber
def neutronNumberCK : CataloguedKind := cat "10-1.2" "N" "1" neutronNumber
def nucleonNumberCK : CataloguedKind := cat "10-1.3" "A" "1" nucleonNumber
def restMassCK : CataloguedKind := cat "10-2" "m" "kg" restMass
def restEnergyCK : CataloguedKind := cat "10-3" "E₀" "J" restEnergy
def atomicMassCK : CataloguedKind := cat "10-4.1" "m_a" "kg" atomicMass
def nuclidicMassCK : CataloguedKind := cat "10-4.2" "m" "kg" nuclidicMass
def unifiedAtomicMassConstantCK : CataloguedKind :=
  cat "10-4.3" "m_u" "kg" unifiedAtomicMassConstant
def elementaryChargeCK : CataloguedKind := cat "10-5.1" "e" "C" elementaryCharge
def chargeNumberCK : CataloguedKind := cat "10-5.2" "c" "1" chargeNumber
def bohrRadiusCK : CataloguedKind := cat "10-6" "a₀" "m" bohrRadius
def rydbergConstantCK : CataloguedKind := cat "10-7" "R∞" "m⁻¹" rydbergConstant
def hartreeEnergyCK : CataloguedKind := cat "10-8" "E_H" "eV" hartreeEnergy
def magneticDipoleMomentCK : CataloguedKind :=
  cat "10-9.1" "μ" "m²·A" magneticDipoleMoment
def bohrMagnetonCK : CataloguedKind := cat "10-9.2" "μ_B" "m²·A" bohrMagneton
def nuclearMagnetonCK : CataloguedKind := cat "10-9.3" "μ_N" "m²·A" nuclearMagneton
def spinCK : CataloguedKind := cat "10-10" "s" "J·s" spin
def totalAngularMomentumCK : CataloguedKind := cat "10-11" "J" "J·s" totalAngularMomentum
def gyromagneticRatioCK : CataloguedKind :=
  cat "10-12.1" "γ" "A·m²·J⁻¹·s⁻¹" gyromagneticRatio
def gyromagneticRatioElectronCK : CataloguedKind :=
  cat "10-12.2" "γ_e" "A·m²·J⁻¹·s⁻¹" gyromagneticRatioElectron
def quantumNumberCK : CataloguedKind := cat "10-13.1" "N" "1" quantumNumber
def principalQuantumNumberCK : CataloguedKind := cat "10-13.2" "n" "1" principalQuantumNumber
def orbitalQuantumNumberCK : CataloguedKind := cat "10-13.3" "l" "1" orbitalQuantumNumber
def magneticQuantumNumberCK : CataloguedKind := cat "10-13.4" "m" "1" magneticQuantumNumber
def spinQuantumNumberCK : CataloguedKind := cat "10-13.5" "s" "1" spinQuantumNumber
def totalAngularMomentumQuantumNumberCK : CataloguedKind :=
  cat "10-13.6" "j" "1" totalAngularMomentumQuantumNumber
def nuclearSpinQuantumNumberCK : CataloguedKind :=
  cat "10-13.7" "I" "1" nuclearSpinQuantumNumber
def hyperfineQuantumNumberCK : CataloguedKind := cat "10-13.8" "F" "1" hyperfineQuantumNumber
def landeFactorCK : CataloguedKind := cat "10-14.1" "g" "1" landeFactor
def gFactorNucleusCK : CataloguedKind := cat "10-14.2" "g" "1" gFactorNucleus
def larmorAngularFrequencyCK : CataloguedKind :=
  cat "10-15.1" "ω_L" "s⁻¹" larmorAngularFrequency
def larmorFrequencyCK : CataloguedKind := cat "10-15.2" "ν_L" "s⁻¹" larmorFrequency
def nuclearPrecessionAngularFrequencyCK : CataloguedKind :=
  cat "10-15.3" "ω_N" "s⁻¹" nuclearPrecessionAngularFrequency
def cyclotronAngularFrequencyCK : CataloguedKind :=
  cat "10-16" "ω_c" "s⁻¹" cyclotronAngularFrequency
def gyroradiusCK : CataloguedKind := cat "10-17" "r_g" "m" gyroradius
def nuclearQuadrupoleMomentCK : CataloguedKind :=
  cat "10-18" "Q" "m²" nuclearQuadrupoleMoment
def nuclearRadiusCK : CataloguedKind := cat "10-19.1" "R" "m" nuclearRadius
def electronRadiusCK : CataloguedKind := cat "10-19.2" "r_e" "m" electronRadius
def comptonWavelengthCK : CataloguedKind := cat "10-20" "λ_C" "m" comptonWavelength
def massExcessCK : CataloguedKind := cat "10-21.1" "Δ" "kg" massExcess
def massDefectCK : CataloguedKind := cat "10-21.2" "B" "kg" massDefect
def relativeMassExcessCK : CataloguedKind := cat "10-22.1" "Δ_r" "1" relativeMassExcess
def relativeMassDefectCK : CataloguedKind := cat "10-22.2" "B_r" "1" relativeMassDefect
def packingFractionCK : CataloguedKind := cat "10-23.1" "f" "1" packingFraction
def bindingFractionCK : CataloguedKind := cat "10-23.2" "b" "1" bindingFraction
def decayConstantCK : CataloguedKind := cat "10-24" "λ" "s⁻¹" decayConstant
def meanLifeCK : CataloguedKind := cat "10-25" "τ" "s" meanLife
def levelWidthCK : CataloguedKind := cat "10-26" "Γ" "eV" levelWidth
def activityCK : CataloguedKind := cat "10-27" "A" "Bq" activity
def specificActivityCK : CataloguedKind := cat "10-28" "a" "Bq/kg" specificActivity
def activityDensityCK : CataloguedKind := cat "10-29" "c_A" "Bq/m³" activityDensity
def surfaceActivityDensityCK : CataloguedKind :=
  cat "10-30" "a_S" "Bq/m²" surfaceActivityDensity
def halfLifeCK : CataloguedKind := cat "10-31" "T_½" "s" halfLife
def alphaDisintegrationEnergyCK : CataloguedKind :=
  cat "10-32" "Q_α" "eV" alphaDisintegrationEnergy
def maximumBetaParticleEnergyCK : CataloguedKind :=
  cat "10-33" "E_β" "eV" maximumBetaParticleEnergy
def betaDisintegrationEnergyCK : CataloguedKind :=
  cat "10-34" "Q_β" "eV" betaDisintegrationEnergy
def internalConversionFactorCK : CataloguedKind :=
  cat "10-35" "α" "1" internalConversionFactor
def particleEmissionRateCK : CataloguedKind := cat "10-36" "Ṅ" "s⁻¹" particleEmissionRate
def reactionEnergyCK : CataloguedKind := cat "10-37.1" "Q" "eV" reactionEnergy
def resonanceEnergyCK : CataloguedKind := cat "10-37.2" "E_r" "eV" resonanceEnergy
def crossSectionCK : CataloguedKind := cat "10-38.1" "σ" "m²" crossSection
def totalCrossSectionCK : CataloguedKind := cat "10-38.2" "σ_tot" "m²" totalCrossSection
def directionCrossSectionCK : CataloguedKind :=
  cat "10-39" "σ_Ω" "m²·sr⁻¹" directionCrossSection
def energyCrossSectionCK : CataloguedKind := cat "10-40" "σ_E" "m²/J" energyCrossSection
def directionEnergyCrossSectionCK : CataloguedKind :=
  cat "10-41" "σ_ΩE" "m²/(J·sr)" directionEnergyCrossSection
def macroscopicCrossSectionCK : CataloguedKind :=
  cat "10-42.1" "Σ" "m⁻¹" macroscopicCrossSection
def macroscopicTotalCrossSectionCK : CataloguedKind :=
  cat "10-42.2" "Σ_tot" "m⁻¹" macroscopicTotalCrossSection
def particleFluenceCK : CataloguedKind := cat "10-43" "Φ" "m⁻²" particleFluence
def particleFluenceRateCK : CataloguedKind :=
  cat "10-44" "Φ̇" "m⁻²·s⁻¹" particleFluenceRate
def radiantEnergyCK : CataloguedKind := cat "10-45" "R" "eV" radiantEnergy
def energyFluenceCK : CataloguedKind := cat "10-46" "Ψ" "eV/m²" energyFluence
def energyFluenceRateCK : CataloguedKind := cat "10-47" "Ψ̇" "W/m²" energyFluenceRate
def particleCurrentDensityCK : CataloguedKind :=
  cat "10-48" "J" "m⁻²·s⁻¹" particleCurrentDensity
def linearAttenuationCoefficientCK : CataloguedKind :=
  cat "10-49" "μ" "m⁻¹" linearAttenuationCoefficient
def massAttenuationCoefficientCK : CataloguedKind :=
  cat "10-50" "μ_m" "kg⁻¹·m²" massAttenuationCoefficient
def molarAttenuationCoefficientCK : CataloguedKind :=
  cat "10-51" "μ_c" "m²·mol⁻¹" molarAttenuationCoefficient
def atomicAttenuationCoefficientCK : CataloguedKind :=
  cat "10-52" "μ_a" "m²" atomicAttenuationCoefficient
def halfValueThicknessCK : CataloguedKind := cat "10-53" "d_½" "m" halfValueThickness
def totalLinearStoppingPowerCK : CataloguedKind :=
  cat "10-54" "S" "eV/m" totalLinearStoppingPower
def totalMassStoppingPowerCK : CataloguedKind :=
  cat "10-55" "S_m" "eV·m²/kg" totalMassStoppingPower
def meanLinearRangeCK : CataloguedKind := cat "10-56" "R" "m" meanLinearRange
def meanMassRangeCK : CataloguedKind := cat "10-57" "R_ρ" "kg·m⁻²" meanMassRange
def linearIonizationCK : CataloguedKind := cat "10-58" "N_il" "m⁻¹" linearIonization
def totalIonizationCK : CataloguedKind := cat "10-59" "N_i" "1" totalIonization
def averageEnergyPerChargeCK : CataloguedKind :=
  cat "10-60" "W_i" "eV" averageEnergyPerCharge
def mobilityCK : CataloguedKind := cat "10-61" "μ" "m²/(V·s)" mobility
def particleNumberDensityCK : CataloguedKind :=
  cat "10-62.1" "n" "m⁻³" particleNumberDensity
def ionNumberDensityCK : CataloguedKind := cat "10-62.2" "n⁺" "m⁻³" ionNumberDensity
def recombinationCoefficientCK : CataloguedKind :=
  cat "10-63" "α" "m³·s⁻¹" recombinationCoefficient
def diffusionCoefficientCK : CataloguedKind := cat "10-64" "D" "m²·s⁻¹" diffusionCoefficient
def diffusionCoefficientFluenceCK : CataloguedKind :=
  cat "10-65" "D_φ" "m" diffusionCoefficientFluence
def particleSourceDensityCK : CataloguedKind :=
  cat "10-66" "S" "m⁻³·s⁻¹" particleSourceDensity
def slowingDownDensityCK : CataloguedKind := cat "10-67" "q" "m⁻³·s⁻¹" slowingDownDensity
def resonanceEscapeProbabilityCK : CataloguedKind :=
  cat "10-68" "p" "1" resonanceEscapeProbability
def lethargyCK : CataloguedKind := cat "10-69" "u" "1" lethargy
def averageLogarithmicEnergyDecrementCK : CataloguedKind :=
  cat "10-70" "ζ" "1" averageLogarithmicEnergyDecrement
def meanFreePathCK : CataloguedKind := cat "10-71" "l" "m" meanFreePath
def slowingDownAreaCK : CataloguedKind := cat "10-72.1" "L²_s" "m²" slowingDownArea
def diffusionAreaCK : CataloguedKind := cat "10-72.2" "L²" "m²" diffusionArea
def migrationAreaCK : CataloguedKind := cat "10-72.3" "M²" "m²" migrationArea
def slowingDownLengthCK : CataloguedKind := cat "10-73.1" "L_s" "m" slowingDownLength
def diffusionLengthCK : CataloguedKind := cat "10-73.2" "L" "m" diffusionLength
def migrationLengthCK : CataloguedKind := cat "10-73.3" "M" "m" migrationLength
def neutronYieldPerFissionCK : CataloguedKind :=
  cat "10-74.1" "ν" "1" neutronYieldPerFission
def neutronYieldPerAbsorptionCK : CataloguedKind :=
  cat "10-74.2" "η" "1" neutronYieldPerAbsorption
def fastFissionFactorCK : CataloguedKind := cat "10-75" "ε" "1" fastFissionFactor
def thermalUtilizationFactorCK : CataloguedKind :=
  cat "10-76" "f" "1" thermalUtilizationFactor
def nonLeakageProbabilityCK : CataloguedKind := cat "10-77" "Λ" "1" nonLeakageProbability
def multiplicationFactorCK : CataloguedKind := cat "10-78.1" "k" "1" multiplicationFactor
def infiniteMultiplicationFactorCK : CataloguedKind :=
  cat "10-78.2" "k∞" "1" infiniteMultiplicationFactor
def reactorTimeConstantCK : CataloguedKind := cat "10-79" "T" "s" reactorTimeConstant
def energyImpartedCK : CataloguedKind := cat "10-80.1" "ε" "eV" energyImparted
def meanEnergyImpartedCK : CataloguedKind := cat "10-80.2" "ε̄" "eV" meanEnergyImparted
def absorbedDoseCK : CataloguedKind := cat "10-81.1" "D" "Gy" absorbedDose
def specificEnergyImpartedCK : CataloguedKind :=
  cat "10-81.2" "z" "Gy" specificEnergyImparted
def qualityFactorCK : CataloguedKind := cat "10-82" "Q" "1" qualityFactor
def doseEquivalentCK : CataloguedKind := cat "10-83.1" "H" "Sv" doseEquivalent
def doseEquivalentRateCK : CataloguedKind := cat "10-83.2" "Ḣ" "Sv/s" doseEquivalentRate
def absorbedDoseRateCK : CataloguedKind := cat "10-84" "Ḋ" "Gy/s" absorbedDoseRate
def linearEnergyTransferCK : CataloguedKind :=
  cat "10-85" "L_Δ" "eV/m" linearEnergyTransfer
def kermaCK : CataloguedKind := cat "10-86.1" "K" "Gy" kerma
def kermaRateCK : CataloguedKind := cat "10-86.2" "K̇" "Gy/s" kermaRate
def massEnergyTransferCoefficientCK : CataloguedKind :=
  cat "10-87" "μ_tr/ρ" "kg⁻¹·m²" massEnergyTransferCoefficient
def exposureCK : CataloguedKind := cat "10-88" "X" "C/kg" exposure
def exposureRateCK : CataloguedKind := cat "10-89" "Ẋ" "C/(kg·s)" exposureRate

/-- The full ISO 80000-10 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [atomicNumberCK, neutronNumberCK, nucleonNumberCK, restMassCK, restEnergyCK,
   atomicMassCK, nuclidicMassCK, unifiedAtomicMassConstantCK, elementaryChargeCK,
   chargeNumberCK, bohrRadiusCK, rydbergConstantCK, hartreeEnergyCK,
   magneticDipoleMomentCK, bohrMagnetonCK, nuclearMagnetonCK, spinCK,
   totalAngularMomentumCK, gyromagneticRatioCK, gyromagneticRatioElectronCK,
   quantumNumberCK, principalQuantumNumberCK, orbitalQuantumNumberCK,
   magneticQuantumNumberCK, spinQuantumNumberCK, totalAngularMomentumQuantumNumberCK,
   nuclearSpinQuantumNumberCK, hyperfineQuantumNumberCK, landeFactorCK, gFactorNucleusCK,
   larmorAngularFrequencyCK, larmorFrequencyCK, nuclearPrecessionAngularFrequencyCK,
   cyclotronAngularFrequencyCK, gyroradiusCK, nuclearQuadrupoleMomentCK, nuclearRadiusCK,
   electronRadiusCK, comptonWavelengthCK, massExcessCK, massDefectCK, relativeMassExcessCK,
   relativeMassDefectCK, packingFractionCK, bindingFractionCK, decayConstantCK, meanLifeCK,
   levelWidthCK, activityCK, specificActivityCK, activityDensityCK, surfaceActivityDensityCK,
   halfLifeCK, alphaDisintegrationEnergyCK, maximumBetaParticleEnergyCK,
   betaDisintegrationEnergyCK, internalConversionFactorCK, particleEmissionRateCK,
   reactionEnergyCK, resonanceEnergyCK, crossSectionCK, totalCrossSectionCK,
   directionCrossSectionCK, energyCrossSectionCK, directionEnergyCrossSectionCK,
   macroscopicCrossSectionCK, macroscopicTotalCrossSectionCK, particleFluenceCK,
   particleFluenceRateCK, radiantEnergyCK, energyFluenceCK, energyFluenceRateCK,
   particleCurrentDensityCK, linearAttenuationCoefficientCK, massAttenuationCoefficientCK,
   molarAttenuationCoefficientCK, atomicAttenuationCoefficientCK, halfValueThicknessCK,
   totalLinearStoppingPowerCK, totalMassStoppingPowerCK, meanLinearRangeCK, meanMassRangeCK,
   linearIonizationCK, totalIonizationCK, averageEnergyPerChargeCK, mobilityCK,
   particleNumberDensityCK, ionNumberDensityCK, recombinationCoefficientCK,
   diffusionCoefficientCK, diffusionCoefficientFluenceCK, particleSourceDensityCK,
   slowingDownDensityCK, resonanceEscapeProbabilityCK, lethargyCK,
   averageLogarithmicEnergyDecrementCK, meanFreePathCK, slowingDownAreaCK, diffusionAreaCK,
   migrationAreaCK, slowingDownLengthCK, diffusionLengthCK, migrationLengthCK,
   neutronYieldPerFissionCK, neutronYieldPerAbsorptionCK, fastFissionFactorCK,
   thermalUtilizationFactorCK, nonLeakageProbabilityCK, multiplicationFactorCK,
   infiniteMultiplicationFactorCK, reactorTimeConstantCK, energyImpartedCK,
   meanEnergyImpartedCK, absorbedDoseCK, specificEnergyImpartedCK, qualityFactorCK,
   doseEquivalentCK, doseEquivalentRateCK, absorbedDoseRateCK, linearEnergyTransferCK,
   kermaCK, kermaRateCK, massEnergyTransferCoefficientCK, exposureCK, exposureRateCK]

/-! ## (N) Units — the gray, the sievert, the becquerel

The gray of absorbed dose and the sievert of dose equivalent carry the *same* dimension
`L²·T⁻²` (energy per mass), yet are not commensurable — the standard's own two-name
disambiguation of one dimension. The becquerel of activity and the reciprocal second of
the decay constant likewise share `T⁻¹` and are not commensurable. -/

/-- The gray of absorbed dose (item 10-81.1). -/
def gray : MetrologicalUnit := absorbedDose.kind.unit "Gy"
/-- The sievert of dose equivalent (item 10-83.1) — *also* `J/kg`, dimension `L²·T⁻²`. -/
def sievert : MetrologicalUnit := doseEquivalent.kind.unit "Sv"
/-- The becquerel of activity (item 10-27). -/
def becquerel : MetrologicalUnit := activity.kind.unit "Bq"
/-- The reciprocal second of the decay constant (item 10-24) — *also* `s⁻¹`, dimension
`T⁻¹`. -/
def perSecondDecay : MetrologicalUnit := decayConstant.kind.unit "s⁻¹"

/-! ## (O) Checked dimensional facts (the dimensional algebra) -/

/-- **Absorbed dose is energy per mass, so its mass-exponent is zero** — `L²·T⁻²`, the mass
cancelling (item 10-81.1). -/
theorem absorbedDose_dim_mass : absorbedDose.dim.mass = 0 := by
  norm_num [absorbedDose, dimKind, NDim.specificEnergy, Dim.energy, Dim.force, Dim.length,
    Dim.mass, Dim.time, Dimension.div_mass, Dimension.mass_mul, Dimension.M𝓭,
    Dimension.L𝓭_mass, Dimension.T𝓭_mass]

/-- Absorbed dose carries length-exponent `2` — `L²·T⁻²` (item 10-81.1). -/
theorem absorbedDose_dim_length : absorbedDose.dim.length = 2 := by
  norm_num [absorbedDose, dimKind, NDim.specificEnergy, Dim.energy, Dim.force, Dim.length,
    Dim.mass, Dim.time, Dimension.div_length, Dimension.length_mul, Dimension.M𝓭,
    Dimension.L𝓭_length, Dimension.T𝓭_length]

/-- Activity is `T⁻¹` — a count rate, the becquerel (item 10-27). -/
theorem activity_dim_time : activity.dim.time = -1 := by
  norm_num [activity, dimKind, NDim.perTime, Dim.time, Dimension.inv_time,
    Dimension.T𝓭_time]

/-- The cross section is an area `L²` — its length-exponent is `2` (item 10-38.1). -/
theorem crossSection_dim_length : crossSection.dim.length = 2 := Dim.area_length

/-- **The molar attenuation coefficient is an area `L²` — the mole reduced** (item
10-51). -/
theorem molarAttenuationCoefficient_dim_length :
    molarAttenuationCoefficient.dim.length = 2 := Dim.area_length

/-! ## (P) Unit well-formedness and (in)commensurability -/

/-- The gray of absorbed dose is a well-formed unit. -/
theorem gray_wellFormed : gray.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- The sievert of dose equivalent is a well-formed unit. -/
theorem sievert_wellFormed : sievert.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- **The gray of absorbed dose and the sievert of dose equivalent are not commensurable,
though both are `J/kg` and `L²·T⁻²`.** The standard coins two special unit names for one
dimension *because the kinds differ* — the absorbed (physical) dose versus the
(biologically-weighted) dose equivalent. This is the dimension-does-not-classify thesis in
the standard's own hand: the entropy/heat-capacity `J/K` collision of ISO 80000-5, made
sharper by distinct unit names. -/
theorem gray_sievert_not_commensurable : ¬ gray.Commensurable sievert := by
  unfold MetrologicalUnit.Commensurable gray sievert absorbedDose doseEquivalent dimKind
    KindOfProperty.unit
  decide

/-- **The becquerel of activity and the reciprocal second of the decay constant are not
commensurable, though both are `T⁻¹`.** The becquerel is the special name SI reserves for
`s⁻¹` as the unit of activity — a kind distinction the dimension cannot see. -/
theorem becquerel_perSecond_not_commensurable :
    ¬ becquerel.Commensurable perSecondDecay := by
  unfold MetrologicalUnit.Commensurable becquerel perSecondDecay activity decayConstant
    dimKind KindOfProperty.unit
  decide

/-! ## (Q) Dimension collisions — the kind classifies where the dimension cannot

The gray/sievert collision (`L²·T⁻²`), the becquerel collision (`T⁻¹`), and the widest
dimension-one family in the physical parts. -/

/-- **Absorbed dose and dose equivalent share dimension `L²·T⁻²`** (both energy per
mass). -/
theorem absorbedDose_dim_eq_doseEquivalent_dim :
    absorbedDose.dim = doseEquivalent.dim := rfl

/-- Absorbed dose is not dose equivalent, though both are `L²·T⁻²` — the gray/sievert
distinction. -/
theorem absorbedDose_ne_doseEquivalent : absorbedDose.kind ≠ doseEquivalent.kind := by
  unfold absorbedDose doseEquivalent dimKind; decide

/-- **Activity and the decay constant share dimension `T⁻¹`** (the becquerel
collision). -/
theorem activity_dim_eq_decayConstant_dim : activity.dim = decayConstant.dim := rfl

/-- Activity is not the decay constant, though both are `T⁻¹`. -/
theorem activity_ne_decayConstant : activity.kind ≠ decayConstant.kind := by
  unfold activity decayConstant dimKind; decide

/-- Atomic number is not neutron number, though both are dimension one. -/
theorem atomicNumber_ne_neutronNumber : atomicNumber.kind ≠ neutronNumber.kind := by
  unfold atomicNumber neutronNumber dimKind; decide

/-- **The gray/sievert collision capstone, on the standard.** There exist distinct
ISO 80000-10 kinds with the same dimension `L²·T⁻²` — absorbed dose and dose equivalent
witness it, alongside the specific energy imparted and the kerma. The standard assigns two
unit names (gray, sievert) to one dimension; the {dimension functor} cannot separate them,
the kind layer — and the unit — does. -/
theorem iso80000_10_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨absorbedDose, doseEquivalent, absorbedDose_ne_doseEquivalent,
    absorbedDose_dim_eq_doseEquivalent_dim⟩

/-- **The dimension-one disambiguation, on the standard — the widest in the physical
parts.** There exist distinct ISO 80000-10 kinds with the same dimension one — the atomic
and neutron numbers witness it, alongside the eight quantum numbers, the g-factors, the
relative mass excess and defect, the packing and binding fractions, the conversion and
quality factors, and the reactor factors. Dimension cannot separate them; the kind layer
does. -/
theorem iso80000_10_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨atomicNumber, neutronNumber, atomicNumber_ne_neutronNumber, rfl, rfl⟩

end PropertyKindCalculus.Iso80000.Part10

end -- pkc-blanket-expose
end -- pkc-blanket
