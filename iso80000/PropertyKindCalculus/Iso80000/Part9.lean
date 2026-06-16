/-
# ISO 80000-9 — Physical chemistry and molecular physics (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
ISO 80000-9 *Physical chemistry and molecular physics* — all of items 9-1 … 9-49,
including every sub-suffixed item (9-6.1 … 9-6.4, 9-9.1/9-9.2, 9-12.1/9-12.2,
9-27.1 … 9-27.3, 9-35.1 … 9-35.4, 9-36.1/9-36.2, 9-37.1/9-37.2, 9-40.1/9-40.2),
sixty-two in all — each carrying its exact source as data: the part (`iso80000_9`),
the printed item designation, the principal quantity symbol, and the coherent SI unit
symbol. Only **citation locators** are recorded; no normative content from the licensed
standard is reproduced. The defining *mathematics* of selected remarks is formalized in
the sibling module `Part9.DefiningRelations`.

Physical chemistry is the home of the **mole**, and so the sharpest test in the series of
the Finkelstein–Whitehead *scale-spanning* reduction (Eur. J. Phys. 46 (2025) 035701; see
`ScaleSpanning`, requirement **R13**): the mole is a human-selected *dimensionless count*
of entities (`N_A` of them), so `Dim.amountOfSubstance = 1`, and every quantity *per mole*
drops the mole. This single reduction reorganizes the whole part:

* **The mole reduces to dimension one — amount of substance joins the dimensionless
  family.** Amount of substance (9-2, `mol`) and the number of entities (9-1) are *both*
  dimension one, yet are different kinds (`N = n·N_A`). The mole is the scale-spanning
  count `N_A`, not a base dimension.

* **Every molar quantity carries the dimension of its non-molar counterpart.** Molar mass
  (9-4, `kg/mol`) *is a mass*; molar volume (9-5, `m³/mol`) *is a volume*; the
  amount-of-substance concentration (9-12.1, `mol/m³`) *is a number density* `L⁻³`, equal
  to the particle concentration (9-9.1); molality (9-15, `mol/kg`) *is an inverse mass*
  `M⁻¹`. The `/mol` is invisible to the dimension functor.

* **The seven-fold `J/mol` collision.** Molar internal energy, molar enthalpy, molar
  Helmholtz energy, molar Gibbs energy (9-6.1 … 9-6.4), the chemical potential (9-17), the
  standard chemical potential (9-21), and the affinity of a reaction (9-30) all carry the
  *same* dimension — energy, `M·L²·T⁻²`, the mole reduced — and the *same* unit string
  `J/mol`, yet are seven different kinds. Likewise the molar heat capacity (9-7), molar
  entropy (9-8), and molar gas constant (9-37.1) all share `J/(mol·K)`.

* **A second large dimension-one family.** The fractions (mass, mole, volume), the
  activities and activity coefficients, the partition functions, the statistical weights,
  the equilibrium constant, the stoichiometric and transport numbers — over two dozen
  distinct kinds the {dimension functor} sends to the single point one.

* **The dimensional facts are checked computations**, discharged in PhysLib's dimension
  group over mass, length, time, temperature, and charge.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.ScaleSpanning
import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.Iso80000.Catalogue

namespace PropertyKindCalculus.Iso80000.Part9

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_9

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Physical-chemistry dimensions — the mole reduced (R13)

The dimensions of physical chemistry, composed in PhysLib's `Dimension` group. Following
the scale-spanning reduction, the mole is the dimensionless count `N_A`
(`Dim.amountOfSubstance = 1`), so every `/mol` factor disappears: a molar mass is a mass,
a molar energy an energy, an amount concentration a number density. -/

namespace PDim

/-- Amount of substance, the mole — reduced to dimension one (`N_A` particles). -/
def amount : Dimension := Dim.amountOfSubstance
/-- Volume, `L³` (`m³/mol` reduced to `m³`). -/
def volume : Dimension := Dim.area * Dim.length
/-- Number density, `L⁻³` — particle/molecular concentration, *and* the
amount-of-substance concentration `mol/m³` once the mole reduces. -/
def numberDensity : Dimension := volume⁻¹
/-- Mass concentration, `M·L⁻³` (mass per volume, `kg/m³`). -/
def massConcentration : Dimension := Dim.mass / volume
/-- Molar energy, `M·L²·T⁻²` — the energies *per mole* (`J/mol`) with the mole reduced:
the molar internal energy, enthalpy, Helmholtz and Gibbs energies, the chemical potential,
and the affinity all share it. -/
def molarEnergy : Dimension := Dim.energy
/-- Molar heat capacity, `M·L²·T⁻²·Θ⁻¹` — energy per temperature (`J/(mol·K)`), the mole
reduced: molar heat capacity, molar entropy, and the molar gas constant share it. -/
def molarHeatCapacity : Dimension := Dim.energy / Dim.temperature
/-- Specific gas constant, `L²·T⁻²·Θ⁻¹` — energy per mass per temperature
(`J/(kg·K)`). -/
def specificGasConstant : Dimension := Dim.energy / (Dim.mass * Dim.temperature)
/-- Pressure, `M·L⁻¹·T⁻²` (force per area; the pascal) — partial pressure, fugacity,
osmotic pressure. -/
def pressure : Dimension := Dim.force / Dim.area
/-- Inverse mass, `M⁻¹` — molality `mol/kg` and ionic strength, the mole reduced to a
count per mass. -/
def inverseMass : Dimension := Dim.mass⁻¹
/-- Diffusion coefficient, `L²·T⁻¹` (`m²/s`). -/
def diffusionCoefficient : Dimension := Dim.area / Dim.time
/-- Electrolytic conductivity, `M⁻¹·L⁻³·T·C²` (`S/m`) — the reciprocal of resistivity per
length, in the charge-based electromagnetic group. -/
def conductivity : Dimension := ((Dim.energy / Dim.charge / Dim.current) * Dim.length)⁻¹
/-- Molar conductivity, `M⁻¹·L⁻¹·T·C²` (`S·m²/mol`) — conductivity times area, the mole
reduced. -/
def molarConductivity : Dimension := conductivity * Dim.area
/-- Molar optical rotatory power, `L²` (`rad·m²/mol`) — an area, the radian dimension one
and the mole reduced. -/
def molarRotatoryPower : Dimension := Dim.area
/-- Specific optical rotatory power, `M⁻¹·L²` (`rad·m²/kg`). -/
def specificRotatoryPower : Dimension := Dim.area / Dim.mass

end PDim

/-! ## (A) Counting entities and the mole (items 9-1 … 9-3)

The number of entities (9-1) is a pure count; the amount of substance (9-2, the mole) is
that count divided by `N_A` — *also* dimension one (R13); the relative atomic mass (9-3) a
dimensionless ratio. -/

/-- Number of entities — item 9-1, dimension one. -/
def numberOfEntities : DimensionedKind := dimKind "number of entities" Dim.one
/-- Amount of substance — item 9-2, dimension one (the mole, the scale-spanning count
`N_A`; R13). -/
def amountOfSubstance : DimensionedKind := dimKind "amount of substance" PDim.amount
/-- Relative atomic mass — item 9-3, dimension one. -/
def relativeAtomicMass : DimensionedKind := dimKind "relative atomic mass" Dim.one

/-! ## (B) Molar quantities — the mole reduced (items 9-4 … 9-8)

Molar mass (9-4) *is a mass*; molar volume (9-5) *is a volume*; the molar energies
(9-6.1 … 9-6.4) *are energies*; molar heat capacity (9-7) and molar entropy (9-8) share
`J/(mol·K)`. -/

/-- Molar mass — item 9-4, dimension `M` (unit kg/mol) — *a mass*, the mole reduced. -/
def molarMass : DimensionedKind := dimKind "molar mass" Dim.mass
/-- Molar volume — item 9-5, dimension `L³` (unit m³/mol) — *a volume*. -/
def molarVolume : DimensionedKind := dimKind "molar volume" PDim.volume
/-- Molar internal energy — item 9-6.1, dimension `M·L²·T⁻²` (unit J/mol). -/
def molarInternalEnergy : DimensionedKind := dimKind "molar internal energy" PDim.molarEnergy
/-- Molar enthalpy — item 9-6.2, dimension `M·L²·T⁻²` (unit J/mol). -/
def molarEnthalpy : DimensionedKind := dimKind "molar enthalpy" PDim.molarEnergy
/-- Molar Helmholtz energy — item 9-6.3, dimension `M·L²·T⁻²` (unit J/mol). -/
def molarHelmholtzEnergy : DimensionedKind := dimKind "molar Helmholtz energy" PDim.molarEnergy
/-- Molar Gibbs energy — item 9-6.4, dimension `M·L²·T⁻²` (unit J/mol). -/
def molarGibbsEnergy : DimensionedKind := dimKind "molar Gibbs energy" PDim.molarEnergy
/-- Molar heat capacity — item 9-7, dimension `M·L²·T⁻²·Θ⁻¹` (unit J/(mol·K)). -/
def molarHeatCapacity : DimensionedKind :=
  dimKind "molar heat capacity" PDim.molarHeatCapacity
/-- Molar entropy — item 9-8, dimension `M·L²·T⁻²·Θ⁻¹` (unit J/(mol·K)). -/
def molarEntropy : DimensionedKind := dimKind "molar entropy" PDim.molarHeatCapacity

/-! ## (C) Concentrations and fractions (items 9-9.1 … 9-15)

Particle and molecular concentration (9-9.*) are number densities; mass concentration
(9-10) is `kg/m³`; the amount-of-substance concentration (9-12.*, `mol/m³`) *is also a
number density*, the mole reduced; molality (9-15, `mol/kg`) *is an inverse mass*. The
fractions (9-11, 9-13, 9-14) are dimension one. -/

/-- Particle concentration, number density — item 9-9.1, dimension `L⁻³` (unit m⁻³). -/
def particleConcentration : DimensionedKind :=
  dimKind "particle concentration" PDim.numberDensity
/-- Molecular concentration — item 9-9.2, dimension `L⁻³` (unit m⁻³). -/
def molecularConcentration : DimensionedKind :=
  dimKind "molecular concentration" PDim.numberDensity
/-- Mass concentration — item 9-10, dimension `M·L⁻³` (unit kg/m³). -/
def massConcentration : DimensionedKind := dimKind "mass concentration" PDim.massConcentration
/-- Mass fraction — item 9-11, dimension one. -/
def massFraction : DimensionedKind := dimKind "mass fraction" Dim.one
/-- Amount-of-substance concentration — item 9-12.1, dimension `L⁻³` (unit mol/m³) — *a
number density*, the mole reduced. -/
def amountConcentration : DimensionedKind :=
  dimKind "amount-of-substance concentration" PDim.numberDensity
/-- Standard amount-of-substance concentration — item 9-12.2, dimension `L⁻³`
(unit mol/m³). -/
def standardAmountConcentration : DimensionedKind :=
  dimKind "standard amount-of-substance concentration" PDim.numberDensity
/-- Amount-of-substance fraction, mole fraction — item 9-13, dimension one. -/
def moleFraction : DimensionedKind := dimKind "mole fraction" Dim.one
/-- Volume fraction — item 9-14, dimension one. -/
def volumeFraction : DimensionedKind := dimKind "volume fraction" Dim.one
/-- Molality — item 9-15, dimension `M⁻¹` (unit mol/kg) — *an inverse mass*, the mole
reduced. -/
def molality : DimensionedKind := dimKind "molality" PDim.inverseMass

/-! ## (D) Chemical potential and activities (items 9-16 … 9-27.3)

The latent heat (9-16, `J`); the chemical potential and its standard value (9-17, 9-21,
`J/mol`, energies); the partial pressure, fugacity, osmotic pressure (9-19, 9-20, 9-28,
`Pa`); and the long dimensionless ladder of activities (9-18, 9-22 … 9-27.3). -/

/-- Latent heat, enthalpy of phase transition — item 9-16, dimension `M·L²·T⁻²` (unit
J). -/
def latentHeat : DimensionedKind := dimKind "latent heat of phase transition" Dim.energy
/-- Chemical potential — item 9-17, dimension `M·L²·T⁻²` (unit J/mol) — an energy. -/
def chemicalPotential : DimensionedKind := dimKind "chemical potential" PDim.molarEnergy
/-- Absolute activity — item 9-18, dimension one. -/
def absoluteActivity : DimensionedKind := dimKind "absolute activity" Dim.one
/-- Partial pressure — item 9-19, dimension `M·L⁻¹·T⁻²` (unit Pa). -/
def partialPressure : DimensionedKind := dimKind "partial pressure" PDim.pressure
/-- Fugacity — item 9-20, dimension `M·L⁻¹·T⁻²` (unit Pa). -/
def fugacity : DimensionedKind := dimKind "fugacity" PDim.pressure
/-- Standard chemical potential — item 9-21, dimension `M·L²·T⁻²` (unit J/mol). -/
def standardChemicalPotential : DimensionedKind :=
  dimKind "standard chemical potential" PDim.molarEnergy
/-- Activity factor — item 9-22, dimension one. -/
def activityFactor : DimensionedKind := dimKind "activity factor" Dim.one
/-- Standard absolute activity in a mixture — item 9-23, dimension one. -/
def standardAbsoluteActivityMixture : DimensionedKind :=
  dimKind "standard absolute activity in a mixture" Dim.one
/-- Activity of solute, relative activity of solute — item 9-24, dimension one. -/
def activityOfSolute : DimensionedKind := dimKind "activity of solute" Dim.one
/-- Activity coefficient — item 9-25, dimension one. -/
def activityCoefficient : DimensionedKind := dimKind "activity coefficient" Dim.one
/-- Standard absolute activity in a solution — item 9-26, dimension one. -/
def standardAbsoluteActivitySolution : DimensionedKind :=
  dimKind "standard absolute activity in a solution" Dim.one
/-- Activity of solvent — item 9-27.1, dimension one. -/
def activityOfSolvent : DimensionedKind := dimKind "activity of solvent" Dim.one
/-- Osmotic coefficient of solvent — item 9-27.2, dimension one. -/
def osmoticCoefficient : DimensionedKind := dimKind "osmotic coefficient of solvent" Dim.one
/-- Standard absolute activity of solvent — item 9-27.3, dimension one. -/
def standardAbsoluteActivitySolvent : DimensionedKind :=
  dimKind "standard absolute activity of solvent" Dim.one

/-! ## (E) Reaction quantities and equilibrium (items 9-28 … 9-34)

The osmotic pressure (9-28); the stoichiometric number (9-29) and affinity (9-30); the
extent of reaction (9-31, `mol`, dimension one — the mole reduced); and the equilibrium
constants (9-32 … 9-34). The pressure- and concentration-basis constants (9-33, 9-34)
carry a *reaction-dependent* unit (`Pa^(Σν)`, `(mol/m³)^(Σν)`); they are recorded here at
the dimensionless representative `Σν = 0`. -/

/-- Osmotic pressure — item 9-28, dimension `M·L⁻¹·T⁻²` (unit Pa). -/
def osmoticPressure : DimensionedKind := dimKind "osmotic pressure" PDim.pressure
/-- Stoichiometric number of substance — item 9-29, dimension one. -/
def stoichiometricNumber : DimensionedKind := dimKind "stoichiometric number" Dim.one
/-- Affinity of a chemical reaction — item 9-30, dimension `M·L²·T⁻²` (unit J/mol). -/
def affinity : DimensionedKind := dimKind "affinity of a chemical reaction" PDim.molarEnergy
/-- Extent of reaction — item 9-31, dimension one (unit mol; the mole reduced). -/
def extentOfReaction : DimensionedKind := dimKind "extent of reaction" PDim.amount
/-- Standard equilibrium constant — item 9-32, dimension one. -/
def standardEquilibriumConstant : DimensionedKind :=
  dimKind "standard equilibrium constant" Dim.one
/-- Equilibrium constant on a pressure basis — item 9-33, dimension one at the
representative `Σν = 0` (the printed unit `Pa^(Σν)` is reaction-dependent). -/
def equilibriumConstantPressure : DimensionedKind :=
  dimKind "equilibrium constant (pressure basis)" Dim.one
/-- Equilibrium constant on a concentration basis — item 9-34, dimension one at the
representative `Σν = 0` (the printed unit `(mol/m³)^(Σν)` is reaction-dependent). -/
def equilibriumConstantConcentration : DimensionedKind :=
  dimKind "equilibrium constant (concentration basis)" Dim.one

/-! ## (F) Statistical mechanics (items 9-35.1 … 9-37.2)

The partition functions (9-35.*) and statistical weights (9-36.*) are dimension one; the
molar gas constant (9-37.1) shares `J/(mol·K)` with the molar heat capacity and entropy;
the specific gas constant (9-37.2) is `J/(kg·K)`. -/

/-- Microcanonical partition function — item 9-35.1, dimension one. -/
def microcanonicalPartition : DimensionedKind :=
  dimKind "microcanonical partition function" Dim.one
/-- Canonical partition function — item 9-35.2, dimension one. -/
def canonicalPartition : DimensionedKind := dimKind "canonical partition function" Dim.one
/-- Grand-canonical partition function — item 9-35.3, dimension one. -/
def grandCanonicalPartition : DimensionedKind :=
  dimKind "grand-canonical partition function" Dim.one
/-- Molecular partition function — item 9-35.4, dimension one. -/
def molecularPartition : DimensionedKind := dimKind "molecular partition function" Dim.one
/-- Statistical weight of a subsystem — item 9-36.1, dimension one. -/
def statisticalWeight : DimensionedKind := dimKind "statistical weight of subsystem" Dim.one
/-- Degeneracy, multiplicity — item 9-36.2, dimension one. -/
def degeneracy : DimensionedKind := dimKind "degeneracy" Dim.one
/-- Molar gas constant — item 9-37.1, dimension `M·L²·T⁻²·Θ⁻¹` (unit J/(mol·K)). -/
def molarGasConstant : DimensionedKind := dimKind "molar gas constant" PDim.molarHeatCapacity
/-- Specific gas constant — item 9-37.2, dimension `L²·T⁻²·Θ⁻¹` (unit J/(kg·K)). -/
def specificGasConstant : DimensionedKind :=
  dimKind "specific gas constant" PDim.specificGasConstant

/-! ## (G) Transport and electrochemistry (items 9-38 … 9-49)

The mean free path (9-38, `m`); diffusion and thermal-diffusion coefficients (9-39, 9-41,
`m²/s`); the dimensionless thermal-diffusion ratios (9-40.*) and degree of dissociation
(9-43); ionic strength (9-42, `mol/kg`, an inverse mass); the electrolytic and molar
conductivities (9-44, 9-45); the transport number (9-46); and optical rotation (9-47 …
9-49). -/

/-- Mean free path — item 9-38, dimension `L` (unit m). -/
def meanFreePath : DimensionedKind := dimKind "mean free path" Dim.length
/-- Diffusion coefficient — item 9-39, dimension `L²·T⁻¹` (unit m²/s). -/
def diffusionCoefficient : DimensionedKind :=
  dimKind "diffusion coefficient" PDim.diffusionCoefficient
/-- Thermal diffusion ratio — item 9-40.1, dimension one. -/
def thermalDiffusionRatio : DimensionedKind := dimKind "thermal diffusion ratio" Dim.one
/-- Thermal diffusion factor — item 9-40.2, dimension one. -/
def thermalDiffusionFactor : DimensionedKind := dimKind "thermal diffusion factor" Dim.one
/-- Thermal diffusion coefficient — item 9-41, dimension `L²·T⁻¹` (unit m²/s). -/
def thermalDiffusionCoefficient : DimensionedKind :=
  dimKind "thermal diffusion coefficient" PDim.diffusionCoefficient
/-- Ionic strength — item 9-42, dimension `M⁻¹` (unit mol/kg) — *an inverse mass*, the
mole reduced. -/
def ionicStrength : DimensionedKind := dimKind "ionic strength" PDim.inverseMass
/-- Degree of dissociation — item 9-43, dimension one. -/
def degreeOfDissociation : DimensionedKind := dimKind "degree of dissociation" Dim.one
/-- Electrolytic conductivity — item 9-44, dimension `M⁻¹·L⁻³·T·C²` (unit S/m). -/
def electrolyticConductivity : DimensionedKind :=
  dimKind "electrolytic conductivity" PDim.conductivity
/-- Molar conductivity — item 9-45, dimension `M⁻¹·L⁻¹·T·C²` (unit S·m²/mol; the mole
reduced). -/
def molarConductivity : DimensionedKind := dimKind "molar conductivity" PDim.molarConductivity
/-- Transport number of an ion — item 9-46, dimension one. -/
def transportNumber : DimensionedKind := dimKind "transport number of the ion" Dim.one
/-- Angle of optical rotation — item 9-47, dimension one (unit rad). -/
def opticalRotationAngle : DimensionedKind := dimKind "angle of optical rotation" Dim.one
/-- Molar optical rotatory power — item 9-48, dimension `L²` (unit rad·m²/mol; the mole
reduced). -/
def molarRotatoryPower : DimensionedKind :=
  dimKind "molar optical rotatory power" PDim.molarRotatoryPower
/-- Specific optical rotatory power — item 9-49, dimension `M⁻¹·L²` (unit rad·m²/kg). -/
def specificRotatoryPower : DimensionedKind :=
  dimKind "specific optical rotatory power" PDim.specificRotatoryPower

/-! ## The catalogue (every kind, with its source as data) -/

def numberOfEntitiesCK : CataloguedKind := cat "9-1" "N" "1" numberOfEntities
def amountOfSubstanceCK : CataloguedKind := cat "9-2" "n" "mol" amountOfSubstance
def relativeAtomicMassCK : CataloguedKind := cat "9-3" "A_r" "1" relativeAtomicMass
def molarMassCK : CataloguedKind := cat "9-4" "M" "kg/mol" molarMass
def molarVolumeCK : CataloguedKind := cat "9-5" "V_m" "m³/mol" molarVolume
def molarInternalEnergyCK : CataloguedKind := cat "9-6.1" "U_m" "J/mol" molarInternalEnergy
def molarEnthalpyCK : CataloguedKind := cat "9-6.2" "H_m" "J/mol" molarEnthalpy
def molarHelmholtzEnergyCK : CataloguedKind := cat "9-6.3" "F_m" "J/mol" molarHelmholtzEnergy
def molarGibbsEnergyCK : CataloguedKind := cat "9-6.4" "G_m" "J/mol" molarGibbsEnergy
def molarHeatCapacityCK : CataloguedKind := cat "9-7" "C_m" "J/(mol·K)" molarHeatCapacity
def molarEntropyCK : CataloguedKind := cat "9-8" "S_m" "J/(mol·K)" molarEntropy
def particleConcentrationCK : CataloguedKind := cat "9-9.1" "n" "m⁻³" particleConcentration
def molecularConcentrationCK : CataloguedKind :=
  cat "9-9.2" "C" "m⁻³" molecularConcentration
def massConcentrationCK : CataloguedKind := cat "9-10" "γ" "kg/m³" massConcentration
def massFractionCK : CataloguedKind := cat "9-11" "w" "1" massFraction
def amountConcentrationCK : CataloguedKind := cat "9-12.1" "c" "mol/m³" amountConcentration
def standardAmountConcentrationCK : CataloguedKind :=
  cat "9-12.2" "c°" "mol/m³" standardAmountConcentration
def moleFractionCK : CataloguedKind := cat "9-13" "x" "1" moleFraction
def volumeFractionCK : CataloguedKind := cat "9-14" "φ" "1" volumeFraction
def molalityCK : CataloguedKind := cat "9-15" "b" "mol/kg" molality
def latentHeatCK : CataloguedKind := cat "9-16" "C_pt" "J" latentHeat
def chemicalPotentialCK : CataloguedKind := cat "9-17" "μ" "J/mol" chemicalPotential
def absoluteActivityCK : CataloguedKind := cat "9-18" "λ" "1" absoluteActivity
def partialPressureCK : CataloguedKind := cat "9-19" "p" "Pa" partialPressure
def fugacityCK : CataloguedKind := cat "9-20" "p̃" "Pa" fugacity
def standardChemicalPotentialCK : CataloguedKind :=
  cat "9-21" "μ°" "J/mol" standardChemicalPotential
def activityFactorCK : CataloguedKind := cat "9-22" "f" "1" activityFactor
def standardAbsoluteActivityMixtureCK : CataloguedKind :=
  cat "9-23" "λ°" "1" standardAbsoluteActivityMixture
def activityOfSoluteCK : CataloguedKind := cat "9-24" "a" "1" activityOfSolute
def activityCoefficientCK : CataloguedKind := cat "9-25" "γ" "1" activityCoefficient
def standardAbsoluteActivitySolutionCK : CataloguedKind :=
  cat "9-26" "λ°" "1" standardAbsoluteActivitySolution
def activityOfSolventCK : CataloguedKind := cat "9-27.1" "a_A" "1" activityOfSolvent
def osmoticCoefficientCK : CataloguedKind := cat "9-27.2" "φ" "1" osmoticCoefficient
def standardAbsoluteActivitySolventCK : CataloguedKind :=
  cat "9-27.3" "λ_A°" "1" standardAbsoluteActivitySolvent
def osmoticPressureCK : CataloguedKind := cat "9-28" "Π" "Pa" osmoticPressure
def stoichiometricNumberCK : CataloguedKind := cat "9-29" "ν" "1" stoichiometricNumber
def affinityCK : CataloguedKind := cat "9-30" "A" "J/mol" affinity
def extentOfReactionCK : CataloguedKind := cat "9-31" "ξ" "mol" extentOfReaction
def standardEquilibriumConstantCK : CataloguedKind :=
  cat "9-32" "K°" "1" standardEquilibriumConstant
def equilibriumConstantPressureCK : CataloguedKind :=
  cat "9-33" "K_p" "Pa^(Σν)" equilibriumConstantPressure
def equilibriumConstantConcentrationCK : CataloguedKind :=
  cat "9-34" "K_c" "(mol/m³)^(Σν)" equilibriumConstantConcentration
def microcanonicalPartitionCK : CataloguedKind :=
  cat "9-35.1" "Ω" "1" microcanonicalPartition
def canonicalPartitionCK : CataloguedKind := cat "9-35.2" "Z" "1" canonicalPartition
def grandCanonicalPartitionCK : CataloguedKind :=
  cat "9-35.3" "Ξ" "1" grandCanonicalPartition
def molecularPartitionCK : CataloguedKind := cat "9-35.4" "q" "1" molecularPartition
def statisticalWeightCK : CataloguedKind := cat "9-36.1" "g" "1" statisticalWeight
def degeneracyCK : CataloguedKind := cat "9-36.2" "g" "1" degeneracy
def molarGasConstantCK : CataloguedKind := cat "9-37.1" "R" "J/(mol·K)" molarGasConstant
def specificGasConstantCK : CataloguedKind := cat "9-37.2" "R_s" "J/(kg·K)" specificGasConstant
def meanFreePathCK : CataloguedKind := cat "9-38" "l" "m" meanFreePath
def diffusionCoefficientCK : CataloguedKind := cat "9-39" "D" "m²/s" diffusionCoefficient
def thermalDiffusionRatioCK : CataloguedKind := cat "9-40.1" "k_T" "1" thermalDiffusionRatio
def thermalDiffusionFactorCK : CataloguedKind := cat "9-40.2" "α_T" "1" thermalDiffusionFactor
def thermalDiffusionCoefficientCK : CataloguedKind :=
  cat "9-41" "D_T" "m²/s" thermalDiffusionCoefficient
def ionicStrengthCK : CataloguedKind := cat "9-42" "I" "mol/kg" ionicStrength
def degreeOfDissociationCK : CataloguedKind := cat "9-43" "α" "1" degreeOfDissociation
def electrolyticConductivityCK : CataloguedKind :=
  cat "9-44" "κ" "S/m" electrolyticConductivity
def molarConductivityCK : CataloguedKind := cat "9-45" "Λ_m" "S·m²/mol" molarConductivity
def transportNumberCK : CataloguedKind := cat "9-46" "t" "1" transportNumber
def opticalRotationAngleCK : CataloguedKind := cat "9-47" "α" "rad" opticalRotationAngle
def molarRotatoryPowerCK : CataloguedKind := cat "9-48" "α_n" "rad·m²/mol" molarRotatoryPower
def specificRotatoryPowerCK : CataloguedKind :=
  cat "9-49" "α_m" "rad·m²/kg" specificRotatoryPower

/-- The full ISO 80000-9 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [numberOfEntitiesCK, amountOfSubstanceCK, relativeAtomicMassCK,
   molarMassCK, molarVolumeCK, molarInternalEnergyCK, molarEnthalpyCK,
   molarHelmholtzEnergyCK, molarGibbsEnergyCK, molarHeatCapacityCK, molarEntropyCK,
   particleConcentrationCK, molecularConcentrationCK, massConcentrationCK, massFractionCK,
   amountConcentrationCK, standardAmountConcentrationCK, moleFractionCK, volumeFractionCK,
   molalityCK, latentHeatCK, chemicalPotentialCK, absoluteActivityCK, partialPressureCK,
   fugacityCK, standardChemicalPotentialCK, activityFactorCK,
   standardAbsoluteActivityMixtureCK, activityOfSoluteCK, activityCoefficientCK,
   standardAbsoluteActivitySolutionCK, activityOfSolventCK, osmoticCoefficientCK,
   standardAbsoluteActivitySolventCK, osmoticPressureCK, stoichiometricNumberCK,
   affinityCK, extentOfReactionCK, standardEquilibriumConstantCK,
   equilibriumConstantPressureCK, equilibriumConstantConcentrationCK,
   microcanonicalPartitionCK, canonicalPartitionCK, grandCanonicalPartitionCK,
   molecularPartitionCK, statisticalWeightCK, degeneracyCK, molarGasConstantCK,
   specificGasConstantCK, meanFreePathCK, diffusionCoefficientCK, thermalDiffusionRatioCK,
   thermalDiffusionFactorCK, thermalDiffusionCoefficientCK, ionicStrengthCK,
   degreeOfDissociationCK, electrolyticConductivityCK, molarConductivityCK,
   transportNumberCK, opticalRotationAngleCK, molarRotatoryPowerCK,
   specificRotatoryPowerCK]

/-! ## (H) Units — a few coherent SI units of these kinds

The molar internal energy and the molar Gibbs energy both carry the unit `J/mol` and the
dimension `M·L²·T⁻²` (the mole reduced), yet are not commensurable; and molality and ionic
strength both carry `mol/kg` and the dimension `M⁻¹`, yet are not commensurable either. -/

/-- The joule-per-mole of molar internal energy (item 9-6.1). -/
def jPerMolInternalEnergy : MetrologicalUnit := molarInternalEnergy.kind.unit "J/mol"
/-- The joule-per-mole of molar Gibbs energy (item 9-6.4) — *also* `J/mol`, dimension
`M·L²·T⁻²`. -/
def jPerMolGibbs : MetrologicalUnit := molarGibbsEnergy.kind.unit "J/mol"
/-- The mole-per-kilogram of molality (item 9-15). -/
def molPerKgMolality : MetrologicalUnit := molality.kind.unit "mol/kg"
/-- The mole-per-kilogram of ionic strength (item 9-42) — *also* `mol/kg`. -/
def molPerKgIonicStrength : MetrologicalUnit := ionicStrength.kind.unit "mol/kg"

/-! ## (I) Checked dimensional facts — the mole reduces (R13) -/

/-- **The mole reduces to dimension one.** Amount of substance carries dimension one — the
scale-spanning count `N_A`, not a base dimension (R13). -/
theorem amountOfSubstance_dim_eq_one : amountOfSubstance.dim = 1 := rfl

/-- **Molar mass is a mass.** With the mole dimension one, `kg/mol` carries the dimension
of mass, `M` (item 9-4). -/
theorem molarMass_dim_eq_mass : molarMass.dim = Dim.mass := rfl

/-- **The amount-of-substance concentration is a number density.** `mol/m³` carries the
dimension `L⁻³` — the same as the particle concentration (item 9-12.1 ≡ 9-9.1, the mole
reduced). -/
theorem amountConcentration_dim_eq_particleConcentration :
    amountConcentration.dim = particleConcentration.dim := rfl

/-- **Molality is an inverse mass.** `mol/kg` carries the dimension `M⁻¹` (item 9-15). -/
theorem molality_dim_eq_inverseMass : molality.dim = Dim.mass⁻¹ := rfl

/-- Molar internal energy is an energy, `M·L²·T⁻²` — its time-exponent is `-2` (item
9-6.1). -/
theorem molarInternalEnergy_dim_time : molarInternalEnergy.dim.time = -2 := Dim.energy_time

/-! ## (J) Unit well-formedness and (in)commensurability -/

/-- The joule-per-mole of molar internal energy is a well-formed unit. -/
theorem jPerMolInternalEnergy_wellFormed : jPerMolInternalEnergy.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- **The joule-per-mole of molar internal energy and that of molar Gibbs energy are not
commensurable, though both are `J/mol` and `M·L²·T⁻²`.** Same unit string, same dimension
(the mole reduced), different kind — the kind layer keeps them apart. -/
theorem jPerMol_internalEnergy_gibbs_not_commensurable :
    ¬ jPerMolInternalEnergy.Commensurable jPerMolGibbs := by
  unfold MetrologicalUnit.Commensurable jPerMolInternalEnergy jPerMolGibbs
    molarInternalEnergy molarGibbsEnergy dimKind KindOfProperty.unit
  decide

/-- **Molality and ionic strength are not commensurable, though both are `mol/kg` and
`M⁻¹`.** -/
theorem molPerKg_molality_ionicStrength_not_commensurable :
    ¬ molPerKgMolality.Commensurable molPerKgIonicStrength := by
  unfold MetrologicalUnit.Commensurable molPerKgMolality molPerKgIonicStrength
    molality ionicStrength dimKind KindOfProperty.unit
  decide

/-! ## (K) Dimension collisions — the mole reduced, the kind classifies

The mole reducing to dimension one, the molar energies all collide on `M·L²·T⁻²` and the
molar heat capacities on `M·L²·T⁻²·Θ⁻¹`; the fractions, activities, and partition
functions all collide on dimension one. -/

/-- Molar internal energy and molar Gibbs energy share dimension `M·L²·T⁻²` (the mole
reduced). -/
theorem molarInternalEnergy_dim_eq_molarGibbsEnergy_dim :
    molarInternalEnergy.dim = molarGibbsEnergy.dim := rfl

/-- The molar heat capacity and the molar entropy share dimension `M·L²·T⁻²·Θ⁻¹`. -/
theorem molarHeatCapacity_dim_eq_molarEntropy_dim :
    molarHeatCapacity.dim = molarEntropy.dim := rfl

/-- Amount of substance is not the number of entities, though both are dimension one. -/
theorem amountOfSubstance_ne_numberOfEntities :
    amountOfSubstance.kind ≠ numberOfEntities.kind := by
  unfold amountOfSubstance numberOfEntities dimKind; decide

/-- Molar internal energy is not molar Gibbs energy, though both are `M·L²·T⁻²`. -/
theorem molarInternalEnergy_ne_molarGibbsEnergy :
    molarInternalEnergy.kind ≠ molarGibbsEnergy.kind := by
  unfold molarInternalEnergy molarGibbsEnergy dimKind; decide

/-- **The `J/mol` collision capstone, on the standard.** There exist distinct ISO 80000-9
kinds with the same dimension `M·L²·T⁻²` — molar internal energy and molar Gibbs energy
witness it, alongside the molar enthalpy and Helmholtz energy, the chemical potential, the
standard chemical potential, and the affinity (all `J/mol`). The mole reduces to dimension
one, so the {dimension functor} cannot separate them; the kind layer does. -/
theorem iso80000_9_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨molarInternalEnergy, molarGibbsEnergy, molarInternalEnergy_ne_molarGibbsEnergy,
    molarInternalEnergy_dim_eq_molarGibbsEnergy_dim⟩

/-- **The dimension-one disambiguation, on the standard — with the mole inside it.** There
exist distinct ISO 80000-9 kinds with the same dimension one — amount of substance (the
mole, reduced by R13) and the number of entities witness it, alongside the fractions, the
activities, and the partition functions. Dimension cannot separate them; the kind layer
does. -/
theorem iso80000_9_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨amountOfSubstance, numberOfEntities, amountOfSubstance_ne_numberOfEntities, rfl, rfl⟩

end PropertyKindCalculus.Iso80000.Part9
