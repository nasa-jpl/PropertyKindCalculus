/-
# ISO 80000-5 — Thermodynamics (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
ISO 80000-5 *Thermodynamics* — all of items 5-1 … 5-36, including every
sub-suffixed item (5-3.1 … 5-3.3, 5-5.1/5-5.2, 5-6.1/5-6.2, 5-10.1/5-10.2,
5-16.1 … 5-16.4, 5-17.1/5-17.2, 5-20.1 … 5-20.5, 5-21.1 … 5-21.5,
5-25.1/5-25.2) — each carrying its exact source as data: the part
(`iso80000_5`), the printed item designation, the principal quantity symbol, and
the coherent SI unit symbol. Only **citation locators** are recorded (item
number, symbol, coherent SI unit); no normative content (definitions, remarks)
from the licensed standard is reproduced. The defining *mathematics* of selected
remarks is formalized in the sibling module `Part5.DefiningRelations`.

Thermodynamics introduces the last axis the earlier parts did not exercise — and
sharpens the two the calculus already pressed:

* **The scale type discriminates where dimension cannot — requirement R6, on the
  real standard.** ISO 80000-5 lists *thermodynamic temperature* (item 5-1) and
  *Celsius temperature* (item 5-2) as separate items of the *same* dimension `Θ`.
  But they are not the same kind of quantity: thermodynamic temperature has an
  absolute zero and so is **ratio-scale** (ratios of temperatures are meaningful;
  the kelvin bears a unit and admits `×`,`÷`), whereas Celsius temperature is
  measured from the arbitrary zero of the ice point and so is **interval-scale**
  (only *differences* are meaningful; the degree Celsius bears a unit but does
  *not* admit `×`,`÷`). The {scale type} keeps them apart where neither dimension
  nor kind-identity alone would — this is requirement R6 realized on the standard,
  the axis Part 3 and Part 4 (all ratio-scale) could not show.

* **Dimension does not classify; the kind does — the entropy/heat-capacity case.**
  *Entropy* (item 5-18), *heat capacity* (item 5-15), the *Massieu function*
  (5-22), and the *Planck function* (5-23) are *all* dimension `M·L²·T⁻²·Θ⁻¹` (the
  joule per kelvin) — distinct kinds the dimension cannot separate, distinguished
  only by their prose definitions. *Specific entropy* (5-19), *specific heat
  capacity* (5-16.1), and the *specific gas constant* (5-26) collide the same way
  at `J/(kg·K)`. The {dimension functor} `dim` identifies the members of each
  collision; the kind layer keeps them apart — and so, decisively, do their units:
  the joule per kelvin of entropy is *not commensurable* with the joule per kelvin
  of heat capacity, the same unit string over a different kind.

* **The energy family is a specialization lattice (requirement R2).** Item 5-20.1,
  *energy* `<thermodynamics>`, is the broad genus; the *thermodynamic potentials* —
  internal energy (5-20.2), enthalpy (5-20.3), Helmholtz energy (5-20.4), and Gibbs
  energy (5-20.5) — are *species* of energy, same dimension `M·L²·T⁻²`, same scale,
  individuated **not by fiat** but by an explicit {examination principle}: each
  potential is defined by *which thermodynamic variables are held natural to it*
  (`U(S,V,N)`, `H = U + pV`, `A = U − TS`, `G = H − TS`). This is the length-family
  pattern of Part 3 and the force-family pattern of Part 4, now on the thermodynamic
  potentials.

* **Thermodynamic quantities are built from the earlier parts.** Many defining
  relations cross parts — specific heat capacity is heat capacity per mass, specific
  entropy is entropy per mass (mass is ISO 80000-4), the density of heat flow rate is
  heat flow rate per area (area is ISO 80000-3) — so the kind-laws in
  `Part5.DefiningRelations` compose Part-5 kinds out of Part-4 and Part-3 kinds, with
  the dimension following from the relation as a checked computation.

* **The dimensional facts are checked computations**, not annotations: heat is
  `M·L²·T⁻²`, entropy `M·L²·T⁻²·Θ⁻¹`, a linear expansion coefficient `Θ⁻¹`, all
  discharged in PhysLib's dimension group over the temperature generator `Θ`.
-/

module

public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.Iso80000.References
public import PropertyKindCalculus.Iso80000.Catalogue

@[expose] public section Blanket

namespace PropertyKindCalculus.Iso80000.Part5

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_5

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Thermodynamic dimensions

The dimensions of thermodynamics, composed in PhysLib's `Dimension` group from the
base generators mass `M`, length `L`, time `T`, and — new to this part —
temperature `Θ` (`Dim.temperature`). Naming the recurring ones once keeps each
quantity-kind's dimension readable and makes a *dimension collision* — entropy and
heat capacity, specific entropy and specific heat capacity — provable by
reflexivity. -/

namespace TDim

/-- Energy, work, heat, `M·L²·T⁻²` (force times length). -/
def energy : Dimension LTMCTDimensionBase := Dim.mass * Dim.area / (Dim.time * Dim.time)
/-- Power and heat flow rate, `M·L²·T⁻³` (energy per time). -/
def power : Dimension LTMCTDimensionBase := energy / Dim.time
/-- Pressure, `M·L⁻¹·T⁻²` (force per area). -/
def pressure : Dimension LTMCTDimensionBase := Dim.mass / (Dim.length * Dim.time * Dim.time)
/-- Expansion coefficient, `Θ⁻¹` (a relative change per temperature). -/
def expansionCoefficient : Dimension LTMCTDimensionBase := Dim.temperature⁻¹
/-- Pressure coefficient, `M·L⁻¹·T⁻²·Θ⁻¹` (pressure per temperature). -/
def pressureCoefficient : Dimension LTMCTDimensionBase := pressure / Dim.temperature
/-- Compressibility, `M⁻¹·L·T²` (the reciprocal of pressure). -/
def compressibility : Dimension LTMCTDimensionBase := pressure⁻¹
/-- Density of heat flow rate, `M·T⁻³` (power per area). -/
def densityOfHeatFlowRate : Dimension LTMCTDimensionBase := power / Dim.area
/-- Thermal conductivity, `M·L·T⁻³·Θ⁻¹` (power per length per temperature). -/
def thermalConductivity : Dimension LTMCTDimensionBase := power / (Dim.length * Dim.temperature)
/-- Coefficient of heat transfer, `M·T⁻³·Θ⁻¹` (power per area per temperature). -/
def coefficientOfHeatTransfer : Dimension LTMCTDimensionBase := power / (Dim.area * Dim.temperature)
/-- Thermal insulance, `M⁻¹·T³·Θ` (the reciprocal of the coefficient of heat
transfer). -/
def thermalInsulance : Dimension LTMCTDimensionBase := coefficientOfHeatTransfer⁻¹
/-- Thermal resistance, `M⁻¹·L⁻²·T³·Θ` (temperature per power). -/
def thermalResistance : Dimension LTMCTDimensionBase := Dim.temperature / power
/-- Thermal conductance, `M·L²·T⁻³·Θ⁻¹` (power per temperature). -/
def thermalConductance : Dimension LTMCTDimensionBase := power / Dim.temperature
/-- Thermal diffusivity, `L²·T⁻¹` (area per time). -/
def thermalDiffusivity : Dimension LTMCTDimensionBase := Dim.area / Dim.time
/-- Heat capacity and entropy, `M·L²·T⁻²·Θ⁻¹` (energy per temperature). -/
def heatCapacity : Dimension LTMCTDimensionBase := energy / Dim.temperature
/-- Specific heat capacity and specific entropy, `L²·T⁻²·Θ⁻¹` (heat capacity per
mass). -/
def specificHeatCapacity : Dimension LTMCTDimensionBase := heatCapacity / Dim.mass
/-- Specific energy, `L²·T⁻²` (energy per mass). -/
def specificEnergy : Dimension LTMCTDimensionBase := energy / Dim.mass
/-- Joule-Thomson coefficient, `M⁻¹·L·T²·Θ` (temperature per pressure). -/
def jouleThomson : Dimension LTMCTDimensionBase := Dim.temperature / pressure
/-- Mass concentration, `M·L⁻³` (mass per volume). -/
def massConcentration : Dimension LTMCTDimensionBase := Dim.mass / (Dim.area * Dim.length)

end TDim

/-! ## (A) Temperature — one dimension, two scales (items 5-1, 5-2)

Item 5-1, *thermodynamic temperature*, is one of the seven ISQ base quantities: a
**ratio-scale** kind of dimension `Θ` with an absolute zero. Item 5-2, *Celsius
temperature*, has the *same* dimension `Θ` but is measured from the arbitrary zero of
the ice point, so it is **interval-scale**: only its differences are meaningful. This
is requirement **R6** on the real standard — the scale type, not the dimension,
separates them. -/

/-- Thermodynamic temperature — item 5-1, dimension `Θ`, ratio-scale. One of the
seven ISQ base quantities. -/
def thermodynamicTemperature : DimensionedKind :=
  dimKind "thermodynamic temperature" Dim.temperature
/-- Celsius temperature — item 5-2, dimension `Θ`, **interval-scale** (an arbitrary
zero at the ice point, `t = T − T₀`). Same dimension as thermodynamic temperature, a
different *scale* — only its differences are meaningful. -/
def celsiusTemperature : DimensionedKind :=
  { kind := { id := "Celsius temperature", scale := .interval }, dim := Dim.temperature }

/-! ## (B) The expansion and pressure coefficients, compressibility (items 5-3 … 5-5)

The expansion coefficients (5-3.1 … 5-3.3) are all dimension `Θ⁻¹` — distinct kinds
the dimension cannot separate. The compressibilities (5-5.1, 5-5.2) are both `Pa⁻¹`. -/

/-- Linear expansion coefficient — item 5-3.1, dimension `Θ⁻¹`. The remark
`αl = (1/l)(dl/dT)` is formalized in `Part5.DefiningRelations`. -/
def linearExpansionCoefficient : DimensionedKind :=
  dimKind "linear expansion coefficient" TDim.expansionCoefficient
/-- Cubic expansion coefficient — item 5-3.2, dimension `Θ⁻¹`. -/
def cubicExpansionCoefficient : DimensionedKind :=
  dimKind "cubic expansion coefficient" TDim.expansionCoefficient
/-- Relative pressure coefficient — item 5-3.3, dimension `Θ⁻¹`. -/
def relativePressureCoefficient : DimensionedKind :=
  dimKind "relative pressure coefficient" TDim.expansionCoefficient
/-- Pressure coefficient — item 5-4, dimension `M·L⁻¹·T⁻²·Θ⁻¹` (unit Pa/K). -/
def pressureCoefficient : DimensionedKind :=
  dimKind "pressure coefficient" TDim.pressureCoefficient
/-- Isothermal compressibility — item 5-5.1, dimension `M⁻¹·L·T²` (unit Pa⁻¹). -/
def isothermalCompressibility : DimensionedKind :=
  dimKind "isothermal compressibility" TDim.compressibility
/-- Isentropic compressibility — item 5-5.2, dimension `M⁻¹·L·T²`. -/
def isentropicCompressibility : DimensionedKind :=
  dimKind "isentropic compressibility" TDim.compressibility

/-! ## (C) Heat and the heat-transfer quantities (items 5-6 … 5-14)

Heat (5-6.1) and latent heat (5-6.2) are energies (`M·L²·T⁻²`, unit J); heat flow
rate (5-7) is a power (`M·L²·T⁻³`, unit W). The conduction quantities (5-9 … 5-13)
carry the temperature generator and several are reciprocals of one another. -/

/-- Heat (amount of heat) — item 5-6.1, dimension `M·L²·T⁻²` (unit J). -/
def heat : DimensionedKind := dimKind "heat" TDim.energy
/-- Latent heat — item 5-6.2, dimension `M·L²·T⁻²` (unit J). -/
def latentHeat : DimensionedKind := dimKind "latent heat" TDim.energy
/-- Heat flow rate — item 5-7, dimension `M·L²·T⁻³` (unit W). -/
def heatFlowRate : DimensionedKind := dimKind "heat flow rate" TDim.power
/-- Density of heat flow rate — item 5-8, dimension `M·T⁻³` (unit W/m²). The
heat-flow-rate/area remark is formalized in `Part5.DefiningRelations`. -/
def densityOfHeatFlowRate : DimensionedKind :=
  dimKind "density of heat flow rate" TDim.densityOfHeatFlowRate
/-- Thermal conductivity — item 5-9, dimension `M·L·T⁻³·Θ⁻¹` (unit W/(m·K)). -/
def thermalConductivity : DimensionedKind :=
  dimKind "thermal conductivity" TDim.thermalConductivity
/-- Coefficient of heat transfer — item 5-10.1, dimension `M·T⁻³·Θ⁻¹` (unit
W/(m²·K)). -/
def coefficientOfHeatTransfer : DimensionedKind :=
  dimKind "coefficient of heat transfer" TDim.coefficientOfHeatTransfer
/-- Surface coefficient of heat transfer — item 5-10.2, dimension `M·T⁻³·Θ⁻¹`. -/
def surfaceCoefficientOfHeatTransfer : DimensionedKind :=
  dimKind "surface coefficient of heat transfer" TDim.coefficientOfHeatTransfer
/-- Thermal insulance — item 5-11, dimension `M⁻¹·T³·Θ` (unit m²·K/W). The
reciprocal-of-coefficient-of-heat-transfer remark is in `Part5.DefiningRelations`. -/
def thermalInsulance : DimensionedKind :=
  dimKind "thermal insulance" TDim.thermalInsulance
/-- Thermal resistance — item 5-12, dimension `M⁻¹·L⁻²·T³·Θ` (unit K/W). -/
def thermalResistance : DimensionedKind :=
  dimKind "thermal resistance" TDim.thermalResistance
/-- Thermal conductance — item 5-13, dimension `M·L²·T⁻³·Θ⁻¹` (unit W/K). The
reciprocal-of-thermal-resistance remark is in `Part5.DefiningRelations`. -/
def thermalConductance : DimensionedKind :=
  dimKind "thermal conductance" TDim.thermalConductance
/-- Thermal diffusivity — item 5-14, dimension `L²·T⁻¹` (unit m²/s). -/
def thermalDiffusivity : DimensionedKind :=
  dimKind "thermal diffusivity" TDim.thermalDiffusivity

/-! ## (D) Heat capacities and entropy (items 5-15 … 5-19)

Heat capacity (5-15) and entropy (5-18) are *both* `M·L²·T⁻²·Θ⁻¹` (the joule per
kelvin) — distinct kinds the dimension cannot separate. The specific heat
capacities (5-16.1 … 5-16.4) and specific entropy (5-19) collide the same way at
`J/(kg·K)`. -/

/-- Heat capacity — item 5-15, dimension `M·L²·T⁻²·Θ⁻¹` (unit J/K). The
heat/temperature-derivative remark is formalized in `Part5.DefiningRelations`. -/
def heatCapacity : DimensionedKind := dimKind "heat capacity" TDim.heatCapacity
/-- Specific heat capacity — item 5-16.1, dimension `L²·T⁻²·Θ⁻¹` (unit J/(kg·K)). The
heat-capacity/mass remark is in `Part5.DefiningRelations`. -/
def specificHeatCapacity : DimensionedKind :=
  dimKind "specific heat capacity" TDim.specificHeatCapacity
/-- Specific heat capacity at constant pressure — item 5-16.2, dimension
`L²·T⁻²·Θ⁻¹`. -/
def specificHeatCapacityConstantPressure : DimensionedKind :=
  dimKind "specific heat capacity at constant pressure" TDim.specificHeatCapacity
/-- Specific heat capacity at constant volume — item 5-16.3, dimension `L²·T⁻²·Θ⁻¹`. -/
def specificHeatCapacityConstantVolume : DimensionedKind :=
  dimKind "specific heat capacity at constant volume" TDim.specificHeatCapacity
/-- Specific heat capacity at saturated vapour pressure — item 5-16.4, dimension
`L²·T⁻²·Θ⁻¹`. -/
def specificHeatCapacitySaturated : DimensionedKind :=
  dimKind "specific heat capacity at saturated vapour pressure" TDim.specificHeatCapacity
/-- Ratio of specific heat capacities — item 5-17.1, dimension one (a ratio of two
specific heat capacities). The remark is formalized in `Part5.DefiningRelations`. -/
def ratioOfSpecificHeatCapacities : DimensionedKind :=
  dimKind "ratio of specific heat capacities" Dim.one
/-- Isentropic exponent — item 5-17.2, dimension one. -/
def isentropicExponent : DimensionedKind := dimKind "isentropic exponent" Dim.one
/-- Entropy — item 5-18, dimension `M·L²·T⁻²·Θ⁻¹` (unit J/K; the same dimension as
heat capacity, a distinct kind). -/
def entropy : DimensionedKind := dimKind "entropy" TDim.heatCapacity
/-- Specific entropy — item 5-19, dimension `L²·T⁻²·Θ⁻¹` (unit J/(kg·K); the same
dimension as specific heat capacity, a distinct kind). The entropy/mass remark is in
`Part5.DefiningRelations`. -/
def specificEntropy : DimensionedKind :=
  dimKind "specific entropy" TDim.specificHeatCapacity

/-! ## (E) The energy family — the thermodynamic potentials (item 5-20)

Item 5-20.1, *energy* `<thermodynamics>`, is the broad genus: a ratio-scale kind of
dimension `M·L²·T⁻²` with no distinguishing examination principle. Items 5-20.2 …
5-20.5 are *species* of energy — same dimension, same scale — individuated by an
explicit examination principle (which thermodynamic variables are natural to the
potential). This is the standards-grounded realization of requirement **R2** on the
thermodynamic potentials (see section (L)). -/

/-! ### Examination principles for the energy species

The examination principles (Dybkær §7.5) that individuate the thermodynamic
potentials. Each `id` is this work's own terse descriptor of the *defining
construction* (the potential's natural variables) that distinguishes the species —
not the standard's normative definition. -/

namespace EnergyPrinciple
/-- Internal energy — a state function of entropy, volume, and particle number. -/
def stateOfSVN : ExaminationPrinciple := { id := "natural-S-V-N" }
/-- Enthalpy — `H = U + pV`, natural in entropy and pressure. -/
def stateOfSp : ExaminationPrinciple := { id := "natural-S-p" }
/-- Helmholtz energy — `A = U − TS`, natural in temperature and volume. -/
def stateOfTV : ExaminationPrinciple := { id := "natural-T-V" }
/-- Gibbs energy — `G = H − TS`, natural in temperature and pressure. -/
def stateOfTp : ExaminationPrinciple := { id := "natural-T-p" }
end EnergyPrinciple

/-- An energy species: dimension `M·L²·T⁻²`, ratio-scale, individuated by its defining
construction (examination principle). -/
def energySpecies (id : String) (p : ExaminationPrinciple) : DimensionedKind :=
  { kind := { id := id, scale := .ratio, examPrinciple := some p.id }, dim := TDim.energy }

/-- Energy `<thermodynamics>` — item 5-20.1, dimension `M·L²·T⁻²` (unit J). The broad
genus of the thermodynamic-potential family. -/
def energy : DimensionedKind := dimKind "energy" TDim.energy
/-- Internal energy (thermodynamic energy) — item 5-20.2, an energy species (natural
in S, V, N). -/
def internalEnergy : DimensionedKind :=
  energySpecies "internal energy" EnergyPrinciple.stateOfSVN
/-- Enthalpy — item 5-20.3, an energy species (`H = U + pV`, natural in S, p). -/
def enthalpy : DimensionedKind := energySpecies "enthalpy" EnergyPrinciple.stateOfSp
/-- Helmholtz energy (Helmholtz function) — item 5-20.4, an energy species
(`A = U − TS`, natural in T, V). -/
def helmholtzEnergy : DimensionedKind :=
  energySpecies "Helmholtz energy" EnergyPrinciple.stateOfTV
/-- Gibbs energy (Gibbs function) — item 5-20.5, an energy species (`G = H − TS`,
natural in T, p). -/
def gibbsEnergy : DimensionedKind :=
  energySpecies "Gibbs energy" EnergyPrinciple.stateOfTp

/-! ## (F) The specific energies, Massieu and Planck functions, Joule-Thomson
coefficient (items 5-21 … 5-24)

The specific energies (5-21.1 … 5-21.5) are all `L²·T⁻²` (J/kg). The Massieu (5-22)
and Planck (5-23) functions are both `J/K`, joining the entropy/heat-capacity
collision. -/

/-- Specific energy — item 5-21.1, dimension `L²·T⁻²` (unit J/kg). The energy/mass
remark is formalized in `Part5.DefiningRelations`. -/
def specificEnergy : DimensionedKind := dimKind "specific energy" TDim.specificEnergy
/-- Specific internal energy (specific thermodynamic energy) — item 5-21.2, dimension
`L²·T⁻²`. -/
def specificInternalEnergy : DimensionedKind :=
  dimKind "specific internal energy" TDim.specificEnergy
/-- Specific enthalpy — item 5-21.3, dimension `L²·T⁻²`. -/
def specificEnthalpy : DimensionedKind :=
  dimKind "specific enthalpy" TDim.specificEnergy
/-- Specific Helmholtz energy — item 5-21.4, dimension `L²·T⁻²`. -/
def specificHelmholtzEnergy : DimensionedKind :=
  dimKind "specific Helmholtz energy" TDim.specificEnergy
/-- Specific Gibbs energy — item 5-21.5, dimension `L²·T⁻²`. -/
def specificGibbsEnergy : DimensionedKind :=
  dimKind "specific Gibbs energy" TDim.specificEnergy
/-- Massieu function — item 5-22, dimension `M·L²·T⁻²·Θ⁻¹` (unit J/K; `J = −A/T`). -/
def massieuFunction : DimensionedKind := dimKind "Massieu function" TDim.heatCapacity
/-- Planck function — item 5-23, dimension `M·L²·T⁻²·Θ⁻¹` (unit J/K; `Y = −G/T`). -/
def planckFunction : DimensionedKind := dimKind "Planck function" TDim.heatCapacity
/-- Joule-Thomson coefficient — item 5-24, dimension `M⁻¹·L·T²·Θ` (unit K/Pa). -/
def jouleThomsonCoefficient : DimensionedKind :=
  dimKind "Joule-Thomson coefficient" TDim.jouleThomson

/-! ## (G) Efficiency and the specific gas constant (items 5-25, 5-26)

Efficiency (5-25.1, 5-25.2) is dimension one *because* it is a ratio. The specific
gas constant (5-26) is `J/(kg·K)`, colliding with specific entropy and specific heat
capacity. -/

/-- Efficiency `<thermodynamics>` — item 5-25.1, dimension one (work delivered over
supplied heat). The remark is formalized in `Part5.DefiningRelations`. -/
def efficiency : DimensionedKind := dimKind "efficiency" Dim.one
/-- Maximum efficiency — item 5-25.2, dimension one (the Carnot bound `1 − Tc/Th`). -/
def maximumEfficiency : DimensionedKind := dimKind "maximum efficiency" Dim.one
/-- Specific gas constant — item 5-26, dimension `L²·T⁻²·Θ⁻¹` (unit J/(kg·K); the same
dimension as specific entropy, a distinct kind). -/
def specificGasConstant : DimensionedKind :=
  dimKind "specific gas constant" TDim.specificHeatCapacity

/-! ## (H) Humidity — concentrations, ratios, fractions, and the dew point
(items 5-27 … 5-36)

The mass concentrations (5-27, 5-28) are `M·L⁻³` (kg/m³); the ratios, fractions, and
relative humidities (5-29 … 5-35) are *all* dimension one — distinct kinds the
dimension cannot separate. The dew-point temperature (5-36) is a thermodynamic
temperature `Θ`. -/

/-- Mass concentration of water — item 5-27, dimension `M·L⁻³` (unit kg/m³). -/
def massConcentrationOfWater : DimensionedKind :=
  dimKind "mass concentration of water" TDim.massConcentration
/-- Mass concentration of water vapour (absolute humidity) — item 5-28, dimension
`M·L⁻³`. -/
def massConcentrationOfWaterVapour : DimensionedKind :=
  dimKind "mass concentration of water vapour" TDim.massConcentration
/-- Mass ratio of water to dry matter — item 5-29, dimension one. -/
def massRatioOfWaterToDryMatter : DimensionedKind :=
  dimKind "mass ratio of water to dry matter" Dim.one
/-- Mass ratio of water vapour to dry gas — item 5-30, dimension one. -/
def massRatioOfWaterVapourToDryGas : DimensionedKind :=
  dimKind "mass ratio of water vapour to dry gas" Dim.one
/-- Mass fraction of water — item 5-31, dimension one. -/
def massFractionOfWater : DimensionedKind :=
  dimKind "mass fraction of water" Dim.one
/-- Mass fraction of dry matter — item 5-32, dimension one. -/
def massFractionOfDryMatter : DimensionedKind :=
  dimKind "mass fraction of dry matter" Dim.one
/-- Relative humidity — item 5-33, dimension one. -/
def relativeHumidity : DimensionedKind := dimKind "relative humidity" Dim.one
/-- Relative mass concentration of vapour — item 5-34, dimension one. -/
def relativeMassConcentrationOfVapour : DimensionedKind :=
  dimKind "relative mass concentration of vapour" Dim.one
/-- Relative mass ratio of vapour — item 5-35, dimension one. -/
def relativeMassRatioOfVapour : DimensionedKind :=
  dimKind "relative mass ratio of vapour" Dim.one
/-- Dew-point temperature — item 5-36, dimension `Θ` (a thermodynamic temperature,
ratio-scale). -/
def dewPointTemperature : DimensionedKind :=
  dimKind "dew-point temperature" Dim.temperature

/-! ## The catalogue (every kind, with its source as data) -/

/-- Temperature. -/
def thermodynamicTemperatureCK : CataloguedKind :=
  cat "5-1" "T" "K" thermodynamicTemperature
def celsiusTemperatureCK : CataloguedKind := cat "5-2" "t" "°C" celsiusTemperature

/-- The expansion and pressure coefficients, compressibility. -/
def linearExpansionCoefficientCK : CataloguedKind :=
  cat "5-3.1" "α_l" "K⁻¹" linearExpansionCoefficient
def cubicExpansionCoefficientCK : CataloguedKind :=
  cat "5-3.2" "α_V" "K⁻¹" cubicExpansionCoefficient
def relativePressureCoefficientCK : CataloguedKind :=
  cat "5-3.3" "α_p" "K⁻¹" relativePressureCoefficient
def pressureCoefficientCK : CataloguedKind := cat "5-4" "β" "Pa/K" pressureCoefficient
def isothermalCompressibilityCK : CataloguedKind :=
  cat "5-5.1" "ϰ_T" "Pa⁻¹" isothermalCompressibility
def isentropicCompressibilityCK : CataloguedKind :=
  cat "5-5.2" "ϰ_S" "Pa⁻¹" isentropicCompressibility

/-- Heat and the heat-transfer quantities. -/
def heatCK : CataloguedKind := cat "5-6.1" "Q" "J" heat
def latentHeatCK : CataloguedKind := cat "5-6.2" "Q" "J" latentHeat
def heatFlowRateCK : CataloguedKind := cat "5-7" "Φ" "W" heatFlowRate
def densityOfHeatFlowRateCK : CataloguedKind :=
  cat "5-8" "q" "W/m²" densityOfHeatFlowRate
def thermalConductivityCK : CataloguedKind :=
  cat "5-9" "λ" "W/(m·K)" thermalConductivity
def coefficientOfHeatTransferCK : CataloguedKind :=
  cat "5-10.1" "K" "W/(m²·K)" coefficientOfHeatTransfer
def surfaceCoefficientOfHeatTransferCK : CataloguedKind :=
  cat "5-10.2" "h" "W/(m²·K)" surfaceCoefficientOfHeatTransfer
def thermalInsulanceCK : CataloguedKind := cat "5-11" "M" "m²·K/W" thermalInsulance
def thermalResistanceCK : CataloguedKind := cat "5-12" "R" "K/W" thermalResistance
def thermalConductanceCK : CataloguedKind := cat "5-13" "G" "W/K" thermalConductance
def thermalDiffusivityCK : CataloguedKind := cat "5-14" "a" "m²/s" thermalDiffusivity

/-- Heat capacities and entropy. -/
def heatCapacityCK : CataloguedKind := cat "5-15" "C" "J/K" heatCapacity
def specificHeatCapacityCK : CataloguedKind :=
  cat "5-16.1" "c" "J/(kg·K)" specificHeatCapacity
def specificHeatCapacityConstantPressureCK : CataloguedKind :=
  cat "5-16.2" "c_p" "J/(kg·K)" specificHeatCapacityConstantPressure
def specificHeatCapacityConstantVolumeCK : CataloguedKind :=
  cat "5-16.3" "c_V" "J/(kg·K)" specificHeatCapacityConstantVolume
def specificHeatCapacitySaturatedCK : CataloguedKind :=
  cat "5-16.4" "c_sat" "J/(kg·K)" specificHeatCapacitySaturated
def ratioOfSpecificHeatCapacitiesCK : CataloguedKind :=
  cat "5-17.1" "γ" "1" ratioOfSpecificHeatCapacities
def isentropicExponentCK : CataloguedKind := cat "5-17.2" "ϰ" "1" isentropicExponent
def entropyCK : CataloguedKind := cat "5-18" "S" "J/K" entropy
def specificEntropyCK : CataloguedKind := cat "5-19" "s" "J/(kg·K)" specificEntropy

/-- The energy family — the thermodynamic potentials. -/
def energyCK : CataloguedKind := cat "5-20.1" "E" "J" energy
def internalEnergyCK : CataloguedKind := cat "5-20.2" "U" "J" internalEnergy
def enthalpyCK : CataloguedKind := cat "5-20.3" "H" "J" enthalpy
def helmholtzEnergyCK : CataloguedKind := cat "5-20.4" "A" "J" helmholtzEnergy
def gibbsEnergyCK : CataloguedKind := cat "5-20.5" "G" "J" gibbsEnergy

/-- The specific energies, Massieu and Planck functions, Joule-Thomson coefficient. -/
def specificEnergyCK : CataloguedKind := cat "5-21.1" "e" "J/kg" specificEnergy
def specificInternalEnergyCK : CataloguedKind :=
  cat "5-21.2" "u" "J/kg" specificInternalEnergy
def specificEnthalpyCK : CataloguedKind := cat "5-21.3" "h" "J/kg" specificEnthalpy
def specificHelmholtzEnergyCK : CataloguedKind :=
  cat "5-21.4" "a" "J/kg" specificHelmholtzEnergy
def specificGibbsEnergyCK : CataloguedKind :=
  cat "5-21.5" "g" "J/kg" specificGibbsEnergy
def massieuFunctionCK : CataloguedKind := cat "5-22" "J" "J/K" massieuFunction
def planckFunctionCK : CataloguedKind := cat "5-23" "Y" "J/K" planckFunction
def jouleThomsonCoefficientCK : CataloguedKind :=
  cat "5-24" "μ_JT" "K/Pa" jouleThomsonCoefficient

/-- Efficiency and the specific gas constant. -/
def efficiencyCK : CataloguedKind := cat "5-25.1" "η" "1" efficiency
def maximumEfficiencyCK : CataloguedKind := cat "5-25.2" "η_max" "1" maximumEfficiency
def specificGasConstantCK : CataloguedKind :=
  cat "5-26" "R_s" "J/(kg·K)" specificGasConstant

/-- Humidity — concentrations, ratios, fractions, and the dew point. -/
def massConcentrationOfWaterCK : CataloguedKind :=
  cat "5-27" "w" "kg/m³" massConcentrationOfWater
def massConcentrationOfWaterVapourCK : CataloguedKind :=
  cat "5-28" "v" "kg/m³" massConcentrationOfWaterVapour
def massRatioOfWaterToDryMatterCK : CataloguedKind :=
  cat "5-29" "u" "1" massRatioOfWaterToDryMatter
def massRatioOfWaterVapourToDryGasCK : CataloguedKind :=
  cat "5-30" "r" "1" massRatioOfWaterVapourToDryGas
def massFractionOfWaterCK : CataloguedKind :=
  cat "5-31" "w_H2O" "1" massFractionOfWater
def massFractionOfDryMatterCK : CataloguedKind :=
  cat "5-32" "w_d" "1" massFractionOfDryMatter
def relativeHumidityCK : CataloguedKind := cat "5-33" "φ" "1" relativeHumidity
def relativeMassConcentrationOfVapourCK : CataloguedKind :=
  cat "5-34" "φ" "1" relativeMassConcentrationOfVapour
def relativeMassRatioOfVapourCK : CataloguedKind :=
  cat "5-35" "ψ" "1" relativeMassRatioOfVapour
def dewPointTemperatureCK : CataloguedKind :=
  cat "5-36" "T_d" "K" dewPointTemperature

/-- The full ISO 80000-5 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [thermodynamicTemperatureCK, celsiusTemperatureCK,
   linearExpansionCoefficientCK, cubicExpansionCoefficientCK, relativePressureCoefficientCK,
   pressureCoefficientCK, isothermalCompressibilityCK, isentropicCompressibilityCK,
   heatCK, latentHeatCK, heatFlowRateCK, densityOfHeatFlowRateCK, thermalConductivityCK,
   coefficientOfHeatTransferCK, surfaceCoefficientOfHeatTransferCK, thermalInsulanceCK,
   thermalResistanceCK, thermalConductanceCK, thermalDiffusivityCK,
   heatCapacityCK, specificHeatCapacityCK, specificHeatCapacityConstantPressureCK,
   specificHeatCapacityConstantVolumeCK, specificHeatCapacitySaturatedCK,
   ratioOfSpecificHeatCapacitiesCK, isentropicExponentCK, entropyCK, specificEntropyCK,
   energyCK, internalEnergyCK, enthalpyCK, helmholtzEnergyCK, gibbsEnergyCK,
   specificEnergyCK, specificInternalEnergyCK, specificEnthalpyCK,
   specificHelmholtzEnergyCK, specificGibbsEnergyCK, massieuFunctionCK, planckFunctionCK,
   jouleThomsonCoefficientCK, efficiencyCK, maximumEfficiencyCK, specificGasConstantCK,
   massConcentrationOfWaterCK, massConcentrationOfWaterVapourCK, massRatioOfWaterToDryMatterCK,
   massRatioOfWaterVapourToDryGasCK, massFractionOfWaterCK, massFractionOfDryMatterCK,
   relativeHumidityCK, relativeMassConcentrationOfVapourCK, relativeMassRatioOfVapourCK,
   dewPointTemperatureCK]

/-! ## (I) Units — a few coherent SI units of these kinds

Each unit references its kind, so a kelvin and a joule are not commensurable; and a
joule-per-kelvin of entropy is not commensurable with a joule-per-kelvin of heat
capacity *though both carry that same unit string and dimension* — all type-level
facts, not runtime checks. -/

/-- The kelvin, the SI unit of thermodynamic temperature (item 5-1). -/
def kelvin : MetrologicalUnit := thermodynamicTemperature.kind.unit "K"
/-- The degree Celsius, the unit of Celsius temperature (item 5-2) — an
*interval-scale* unit. -/
def degreeCelsius : MetrologicalUnit := celsiusTemperature.kind.unit "°C"
/-- The joule, the SI unit of energy (item 5-20.1) — dimension `M·L²·T⁻²`. -/
def joule : MetrologicalUnit := energy.kind.unit "J"
/-- The watt, the SI unit of heat flow rate (item 5-7) — dimension `M·L²·T⁻³`. -/
def watt : MetrologicalUnit := heatFlowRate.kind.unit "W"
/-- The joule per kelvin **of entropy** (item 5-18) — dimension `M·L²·T⁻²·Θ⁻¹`. -/
def joulePerKelvinEntropy : MetrologicalUnit := entropy.kind.unit "J/K"
/-- The joule per kelvin **of heat capacity** (item 5-15) — *also* `M·L²·T⁻²·Θ⁻¹` and
*also* written "J/K", but a unit of heat capacity, not of entropy. -/
def joulePerKelvinHeatCapacity : MetrologicalUnit := heatCapacity.kind.unit "J/K"

/-! ## (J) Checked dimensional facts (the dimensional algebra) -/

/-- Thermodynamic temperature carries the temperature dimension `Θ`. -/
theorem thermodynamicTemperature_dim : thermodynamicTemperature.dim = Dim.temperature := rfl

/-- Heat is `M·L²·T⁻²`: its length-exponent is `2` (ISO 80000-5 item 5-6.1). -/
theorem heat_dim_length : heat.dim.length = 2 := by
  norm_num [heat, dimKind, TDim.energy, Dim.mass, Dim.area, Dim.time,
    Dimension.div_length, Dimension.length_mul, Dimension.L𝓭_length, Dimension.T𝓭_length,
    Dimension.M𝓭]

/-- Entropy is `M·L²·T⁻²·Θ⁻¹`: its temperature-exponent is `-1` (ISO 80000-5 item
5-18). The temperature generator `Θ` enters through the `energy / temperature`
quotient. -/
theorem entropy_dim_temperature : entropy.dim.temperature = -1 := by
  norm_num [entropy, dimKind, TDim.heatCapacity, TDim.energy, Dim.mass, Dim.area,
    Dim.time, Dim.temperature, Dimension.div_temperature, Dimension.temperature_mul,
    Dimension.L𝓭_temperature, Dimension.T𝓭_temperature, Dimension.M𝓭, Dimension.Θ𝓭]

/-- Heat capacity is `M·L²·T⁻²·Θ⁻¹`: its temperature-exponent is `-1` (item 5-15). -/
theorem heatCapacity_dim_temperature : heatCapacity.dim.temperature = -1 := by
  norm_num [heatCapacity, dimKind, TDim.heatCapacity, TDim.energy, Dim.mass, Dim.area,
    Dim.time, Dim.temperature, Dimension.div_temperature, Dimension.temperature_mul,
    Dimension.L𝓭_temperature, Dimension.T𝓭_temperature, Dimension.M𝓭, Dimension.Θ𝓭]

/-- A linear expansion coefficient is `Θ⁻¹`: its temperature-exponent is `-1` (item
5-3.1). -/
theorem linearExpansionCoefficient_dim_temperature :
    linearExpansionCoefficient.dim.temperature = -1 := by
  simp [linearExpansionCoefficient, dimKind, TDim.expansionCoefficient, Dim.temperature,
    Dimension.inv_temperature, Dimension.Θ𝓭]

/-! ## (K) Unit well-formedness, scale, and (in)commensurability -/

/-- The kelvin is a well-formed unit (thermodynamic temperature is ratio-scale, so it
bears a unit). -/
theorem kelvin_wellFormed : kelvin.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- The joule is a well-formed unit of energy. -/
theorem joule_wellFormed : joule.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- **The degree Celsius is a well-formed unit, though Celsius temperature is only
interval-scale.** A kind bears a metrological unit from the *differential* (interval)
scale upward (Dybkær §13.3.4), not only from ratio scale — so the degree Celsius is a
legitimate unit even though `×`,`÷` are undefined on Celsius temperatures. -/
theorem degreeCelsius_wellFormed : degreeCelsius.WellFormed := by
  unfold MetrologicalUnit.WellFormed KindOfProperty.BearsUnit degreeCelsius
    celsiusTemperature KindOfProperty.unit
  trivial

/-- The kelvin and the joule are **not** commensurable — thermodynamic temperature and
energy are distinct kinds (a type-level fact). -/
theorem kelvin_joule_not_commensurable : ¬ kelvin.Commensurable joule := by
  unfold MetrologicalUnit.Commensurable kelvin joule thermodynamicTemperature energy
    dimKind KindOfProperty.unit
  decide

/-- **The entropy joule-per-kelvin is not the heat-capacity joule-per-kelvin, though
both are "J/K" and both `M·L²·T⁻²·Θ⁻¹`.** The units of entropy and heat capacity carry
the same symbol and the same dimension, yet are not commensurable, because their kinds
differ — the sharpest form of "a dimension (or a unit string) does not determine a
kind". -/
theorem entropy_heatCapacity_unit_not_commensurable :
    ¬ joulePerKelvinEntropy.Commensurable joulePerKelvinHeatCapacity := by
  unfold MetrologicalUnit.Commensurable joulePerKelvinEntropy joulePerKelvinHeatCapacity
    entropy heatCapacity dimKind KindOfProperty.unit
  decide

/-! ### The scale-type distinction (requirement R6)

Thermodynamic temperature (5-1) and Celsius temperature (5-2) have the *same*
dimension `Θ` and are *both* "temperatures", yet are different kinds — separated not
by dimension and not by an examination principle, but by their **scale type**: ratio
versus interval. -/

/-- Thermodynamic temperature is **ratio-scale**: it admits `×`,`÷` (an absolute
zero). -/
theorem thermodynamicTemperature_allowsRatio :
    ScaleType.AllowsRatio thermodynamicTemperature.kind.scale := by
  unfold thermodynamicTemperature dimKind ScaleType.AllowsRatio; trivial

/-- **Celsius temperature does *not* admit `×`,`÷`.** It is interval-scale (an
arbitrary zero at the ice point), so a ratio of Celsius temperatures is not a
meaningful operation — the kind layer refuses it where dimension would not. -/
theorem celsiusTemperature_not_allowsRatio :
    ¬ ScaleType.AllowsRatio celsiusTemperature.kind.scale := by
  unfold celsiusTemperature ScaleType.AllowsRatio; exact id

/-- **Thermodynamic temperature and Celsius temperature are distinct kinds — by scale,
not by dimension.** They share the dimension `Θ`, yet differ in scale type (ratio vs
interval), so they are different kinds of quantity. -/
theorem thermodynamicTemperature_ne_celsiusTemperature :
    thermodynamicTemperature.kind ≠ celsiusTemperature.kind := by
  unfold thermodynamicTemperature celsiusTemperature dimKind; decide

/-! ## (L) The energy family as a specialization lattice (requirement R2)

The direct-parent edges of the thermodynamic-potential family, mirroring the
standard's own definitions: internal energy, enthalpy, the Helmholtz energy, and the
Gibbs energy are each a *species* of energy (item 5-20.1), individuated by which
thermodynamic variables are natural to the potential. Specialization is the
reflexive-transitive closure of these edges. -/

/-- This application's system of energy quantities — the direct-parent edges among the
thermodynamic potentials of the energy family (item 5-20). -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  /-- Internal energy is a kind of energy (item 5-20.2 via energy). -/
  | internalEnergy_energy : Edge internalEnergy.kind energy.kind
  /-- Enthalpy is a kind of energy (item 5-20.3 via energy). -/
  | enthalpy_energy : Edge enthalpy.kind energy.kind
  /-- The Helmholtz energy is a kind of energy (item 5-20.4 via energy). -/
  | helmholtzEnergy_energy : Edge helmholtzEnergy.kind energy.kind
  /-- The Gibbs energy is a kind of energy (item 5-20.5 via energy). -/
  | gibbsEnergy_energy : Edge gibbsEnergy.kind energy.kind

/-- Internal energy specializes energy. -/
theorem internalEnergy_specializes_energy :
    Specializes Edge internalEnergy.kind energy.kind :=
  Specializes.of_edge Edge.internalEnergy_energy

/-- Each energy species is **examined by** its declared defining construction. -/
theorem internalEnergy_examinedBy :
    internalEnergy.kind.examinedBy EnergyPrinciple.stateOfSVN := rfl

/-- **The Helmholtz and Gibbs energies are distinct kinds — by defining construction,
not by fiat.** They have the same dimension `M·L²·T⁻²` and are both "free energies",
yet they are different kinds *because they are defined by different natural variables*
(`A = U − TS`, natural in T,V; `G = H − TS`, natural in T,p), proved through
`distinct_of_examPrinciple` (§7.5) rather than by appealing to their `id` strings.
This is the thermodynamic-potential analogue of width ≠ distance and static ≠ kinetic
friction force. -/
theorem helmholtzEnergy_ne_gibbsEnergy : helmholtzEnergy.kind ≠ gibbsEnergy.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- Internal energy and enthalpy are distinct kinds, again by their differing defining
constructions (natural in S,V,N vs S,p). -/
theorem internalEnergy_ne_enthalpy : internalEnergy.kind ≠ enthalpy.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- An energy species is distinct from the general energy kind: a species carries an
examination principle (its defining construction), the genus carries none. -/
theorem internalEnergy_ne_energy : internalEnergy.kind ≠ energy.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- **Mutual comparability is preserved.** The Helmholtz and Gibbs energies, though
distinct kinds, remain *mutually comparable* — they share the super-kind energy, so
combining them is possible but only via an explicit up-cast, never silently. -/
theorem helmholtzEnergy_gibbsEnergy_comparable :
    MutuallyComparable Edge helmholtzEnergy.kind gibbsEnergy.kind :=
  ⟨energy.kind, Specializes.of_edge Edge.helmholtzEnergy_energy,
    Specializes.of_edge Edge.gibbsEnergy_energy⟩

/-! ## (M) Dimension collisions — the kind classifies where the dimension cannot

Same-dimension/distinct-kind pairs drawn from the catalogue above. The {dimension
functor} `dim` identifies the members of each pair; the kind layer keeps them apart. -/

/-- Entropy and heat capacity share dimension `M·L²·T⁻²·Θ⁻¹` (the joule per kelvin). -/
theorem entropy_dim_eq_heatCapacity_dim : entropy.dim = heatCapacity.dim := rfl

/-- **Entropy is not heat capacity, though both are `M·L²·T⁻²·Θ⁻¹`.** They are distinct
kinds despite sharing the joule-per-kelvin dimension — the textbook thermodynamic case
the kind layer resolves and the dimension cannot. -/
theorem entropy_ne_heatCapacity : entropy.kind ≠ heatCapacity.kind := by
  unfold entropy heatCapacity dimKind; decide

/-- Specific entropy and specific heat capacity share dimension `L²·T⁻²·Θ⁻¹`. -/
theorem specificEntropy_dim_eq_specificHeatCapacity_dim :
    specificEntropy.dim = specificHeatCapacity.dim := rfl

/-- Specific entropy and specific heat capacity are distinct kinds (unit J/(kg·K)). -/
theorem specificEntropy_ne_specificHeatCapacity :
    specificEntropy.kind ≠ specificHeatCapacity.kind := by
  unfold specificEntropy specificHeatCapacity dimKind; decide

/-- The ratio of specific heat capacities and the efficiency are distinct kinds, both
dimension one. -/
theorem ratioOfSpecificHeatCapacities_ne_efficiency :
    ratioOfSpecificHeatCapacities.kind ≠ efficiency.kind := by
  unfold ratioOfSpecificHeatCapacities efficiency dimKind; decide

/-- **The entropy/heat-capacity collision, on standard quantities.** There exist
distinct ISO 80000-5 kinds with the same dimension `M·L²·T⁻²·Θ⁻¹` — entropy and heat
capacity witness it (alongside the Massieu and Planck functions). PhysLib's
`Dimension`, and any dimension-only type system, cannot separate them; the kind layer
does. This is the thermodynamic dimension-does-not-classify case. -/
theorem iso80000_5_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨entropy, heatCapacity, entropy_ne_heatCapacity, entropy_dim_eq_heatCapacity_dim⟩

/-- **The dimension-1 disambiguation, on standard quantities.** There exist distinct
ISO 80000-5 kinds with the same dimension one — the ratio of specific heat capacities
and the efficiency witness it (alongside the isentropic exponent and the humidity
ratios and fractions). Dimension cannot separate them; the kind layer does. -/
theorem iso80000_5_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨ratioOfSpecificHeatCapacities, efficiency,
    ratioOfSpecificHeatCapacities_ne_efficiency, rfl, rfl⟩

/-- **The scale disambiguation, on standard quantities.** There exist distinct
ISO 80000-5 kinds with the same dimension `Θ` that are separated by *scale type* alone
— thermodynamic temperature (ratio) and Celsius temperature (interval) witness it.
Neither the dimension nor an examination principle tells them apart; the scale layer
does. This is requirement R6 on the standard, the axis Parts 3 and 4 could not show. -/
theorem iso80000_5_scale_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
      a.kind.scale ≠ b.kind.scale :=
  ⟨thermodynamicTemperature, celsiusTemperature,
    thermodynamicTemperature_ne_celsiusTemperature, rfl, by decide⟩

end PropertyKindCalculus.Iso80000.Part5

end Blanket
