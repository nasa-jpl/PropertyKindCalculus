/-
# ISO 80000-4 — Mechanics (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
ISO 80000-4 *Mechanics* — all of items 4-1 … 4-32 — each carrying its exact source
as data: the part (`iso80000_4`), the printed item designation, the principal
quantity symbol, and the coherent SI unit symbol. Only **citation locators** are
recorded (item number, symbol, coherent SI unit); no normative content
(definitions, remarks) from the licensed standard is reproduced. The defining
*mathematics* of selected remarks is formalized in the sibling module
`Part4.DefiningRelations`.

Mechanics is where the calculus's two theses bite hardest, because the standard's
own quantities force the issues:

* **The force family is a specialization lattice (requirement R2), realized on the
  real standard.** ISO 80000-4 lists weight, static friction force, kinetic friction
  force, rolling resistance, and drag force as separate items, all of dimension
  `M·L·T⁻²` and all ratio-scale — distinguished in the standard only by their *prose
  definitions* (a weight acts in a gravitational field; a static friction force
  resists motion *before* sliding; a kinetic friction force resists motion *during*
  sliding; …). Here each is a {kind} that {specializes} the general force kind
  (item 4-9.1) and is individuated **not by fiat** but by an explicit {examination
  principle} (Dybkær §7.5): static and kinetic friction forces, physically of the
  same dimension and both "friction forces", are proved distinct kinds *because they
  are examined under different conditions*, while all remain mutually comparable as
  forces. This is the length-family pattern of Part 3, now on the force family.

* **Dimension does not classify; the kind does — and Part 4 holds the textbook
  case.** Torque (moment of force) and energy (work) are *both* `M·L²·T⁻²`, yet they
  are distinct kinds measured in distinct units — the newton metre is reserved for
  torque, the joule for energy. The {dimension functor} `dim` cannot separate them;
  the kind layer does. Part 4 is dense with such collisions: momentum and impulse
  (`M·L·T⁻¹`); angular momentum, angular impulse, and action (`M·L²·T⁻¹`); pressure,
  stress, and the three elastic moduli (`M·L⁻¹·T⁻²`); and a whole family of
  dimension-one quantities — the relative densities, the strains, the Poisson number,
  the friction factors, the drag coefficient, and the efficiency.

* **Mechanical quantities are built from Part 3's space-and-time quantities.** Many
  defining relations cross parts — momentum is mass × velocity, pressure is force /
  area, mass density is mass / volume — so the kind-laws in `Part4.DefiningRelations`
  compose Part-4 kinds out of Part-3 kinds, with the dimension following from the
  relation as a checked computation.

* **The dimensional facts are checked computations**, not annotations: force is
  `M·L·T⁻²`, energy `M·L²·T⁻²`, pressure `M·L⁻¹·T⁻²`, power `M·L²·T⁻³`, all discharged
  in PhysLib's dimension group.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.Iso80000.Catalogue

namespace PropertyKindCalculus.Iso80000.Part4

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_4

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Mechanical dimensions

The dimensions of mechanics, composed in PhysLib's `Dimension` group from the base
generators mass `M`, length `L`, and time `T` (and the Part-3 derivations `Dim.area`
= `L²` and `Dim.speed` = `L·T⁻¹`). Naming the recurring ones once keeps each
quantity-kind's dimension readable and makes a *dimension collision* — torque and
energy, momentum and impulse — provable by reflexivity. -/

namespace MDim

/-- Force, `M·L·T⁻²` (mass times acceleration). -/
def force : Dimension := Dim.mass * Dim.length / (Dim.time * Dim.time)
/-- Momentum (and impulse), `M·L·T⁻¹` (mass times speed). -/
def momentum : Dimension := Dim.mass * Dim.speed
/-- Energy, work, and torque, `M·L²·T⁻²` (force times length). -/
def energy : Dimension := Dim.mass * Dim.area / (Dim.time * Dim.time)
/-- Power, `M·L²·T⁻³` (energy per time). -/
def power : Dimension := Dim.mass * Dim.area / (Dim.time * Dim.time * Dim.time)
/-- Pressure, stress, and the elastic moduli, `M·L⁻¹·T⁻²` (force per area). -/
def pressure : Dimension := Dim.mass / (Dim.length * Dim.time * Dim.time)
/-- Compressibility, `M⁻¹·L·T²` (the reciprocal of pressure). -/
def compressibility : Dimension := pressure⁻¹
/-- Angular momentum, angular impulse, and action, `M·L²·T⁻¹` (energy times time). -/
def angularMomentum : Dimension := Dim.mass * Dim.area / Dim.time
/-- Moment of inertia, `M·L²` (mass times area). -/
def momentOfInertia : Dimension := Dim.mass * Dim.area
/-- Mass density, `M·L⁻³` (mass per volume). -/
def massDensity : Dimension := Dim.mass / (Dim.length * Dim.length * Dim.length)
/-- Specific volume, `M⁻¹·L³` (the reciprocal of mass density). -/
def specificVolume : Dimension := (Dim.length * Dim.length * Dim.length) / Dim.mass
/-- Surface (areal) mass density, `M·L⁻²` (mass per area). -/
def surfaceMassDensity : Dimension := Dim.mass / (Dim.length * Dim.length)
/-- Linear mass density, `M·L⁻¹` (mass per length). -/
def linearMassDensity : Dimension := Dim.mass / Dim.length
/-- Second moment of area, `L⁴` (area times area). -/
def secondMomentOfArea : Dimension := Dim.area * Dim.area
/-- Section modulus, `L³` (area times length — the volume dimension). -/
def sectionModulus : Dimension := Dim.area * Dim.length
/-- Dynamic viscosity, `M·L⁻¹·T⁻¹` (pressure times time). -/
def dynamicViscosity : Dimension := Dim.mass / (Dim.length * Dim.time)
/-- Kinematic viscosity, `L²·T⁻¹` (area per time). -/
def kinematicViscosity : Dimension := Dim.area / Dim.time
/-- Surface tension, `M·T⁻²` (force per length). -/
def surfaceTension : Dimension := Dim.mass / (Dim.time * Dim.time)
/-- Mass flow, `M·L⁻²·T⁻¹` (mass density times speed). -/
def massFlow : Dimension := Dim.mass / (Dim.area * Dim.time)
/-- Mass flow rate and mass change rate, `M·T⁻¹` (mass per time). -/
def massRate : Dimension := Dim.mass / Dim.time
/-- Volume flow rate, `L³·T⁻¹` (volume per time). -/
def volumeFlowRate : Dimension := (Dim.area * Dim.length) / Dim.time

end MDim

/-! ## (A) Mass and the densities (items 4-1 … 4-7) -/

/-- Mass — item 4-1, dimension `M`. The fundamental mechanical quantity. -/
def mass : DimensionedKind := dimKind "mass" Dim.mass
/-- Mass density (density) — item 4-2, dimension `M·L⁻³`. The mass/volume remark is
formalized in `Part4.DefiningRelations`. -/
def massDensity : DimensionedKind := dimKind "mass density" MDim.massDensity
/-- Specific volume — item 4-3, dimension `M⁻¹·L³` (the reciprocal of mass density). -/
def specificVolume : DimensionedKind := dimKind "specific volume" MDim.specificVolume
/-- Relative mass density (relative density) — item 4-4, dimension one. -/
def relativeMassDensity : DimensionedKind := dimKind "relative mass density" Dim.one
/-- Surface mass density (areal density) — item 4-5, dimension `M·L⁻²`. -/
def surfaceMassDensity : DimensionedKind :=
  dimKind "surface mass density" MDim.surfaceMassDensity
/-- Linear mass density (linear density) — item 4-6, dimension `M·L⁻¹`. -/
def linearMassDensity : DimensionedKind :=
  dimKind "linear mass density" MDim.linearMassDensity
/-- Moment of inertia — item 4-7, dimension `M·L²` (a tensor quantity). -/
def momentOfInertia : DimensionedKind := dimKind "moment of inertia" MDim.momentOfInertia

/-! ## (B) Momentum, the force family, impulse, and moments (items 4-8 … 4-13)

Item 4-9.1, *force*, is the broad genus: a ratio-scale kind of dimension `M·L·T⁻²`
with no distinguishing examination principle. Items 4-9.2 … 4-9.6 are *species* of
force — same dimension, same scale — individuated by an explicit examination
principle. This is the standards-grounded realization of requirement **R2** on the
force family (see section (L)). -/

/-! ### Examination principles for the force species

The examination principles (Dybkær §7.5) that individuate the force species. Each
`id` is this work's own terse descriptor of the *measurement principle* that
distinguishes the species — not the standard's normative definition. -/

namespace ForcePrinciple
/-- Weight — the force a gravitational field exerts on a body. -/
def gravitational : ExaminationPrinciple := { id := "gravitational-field" }
/-- Static friction force — resistance to motion *before* a body starts to slide. -/
def preSlipResistance : ExaminationPrinciple := { id := "pre-slip-resistance" }
/-- Kinetic friction force — resistance to motion *while* a body slides. -/
def slidingResistance : ExaminationPrinciple := { id := "sliding-resistance" }
/-- Rolling resistance — resistance to motion while a body rolls on a surface. -/
def rollingResistanceP : ExaminationPrinciple := { id := "rolling-resistance" }
/-- Drag force — resistance to motion of a body in a fluid. -/
def fluidResistance : ExaminationPrinciple := { id := "fluid-resistance" }
end ForcePrinciple

/-- A force species: dimension `M·L·T⁻²`, ratio-scale, individuated by its measurement
(examination) principle. -/
def forceSpecies (id : String) (p : ExaminationPrinciple) : DimensionedKind :=
  { kind := { id := id, scale := .ratio, examPrinciple := some p.id }, dim := MDim.force }

/-- Momentum — item 4-8, dimension `M·L·T⁻¹` (a vector quantity). The mass × velocity
remark is formalized in `Part4.DefiningRelations`. -/
def momentum : DimensionedKind := dimKind "momentum" MDim.momentum
/-- Force — item 4-9.1, dimension `M·L·T⁻²` (a vector quantity). The broad genus of
the force family. The mass × acceleration remark is in `Part4.DefiningRelations`. -/
def force : DimensionedKind := dimKind "force" MDim.force
/-- Weight — item 4-9.2, a force species (gravitational-field action). -/
def weight : DimensionedKind := forceSpecies "weight" ForcePrinciple.gravitational
/-- Static friction force — item 4-9.3, a force species (pre-slip resistance). -/
def staticFrictionForce : DimensionedKind :=
  forceSpecies "static friction force" ForcePrinciple.preSlipResistance
/-- Kinetic friction force — item 4-9.4, a force species (sliding resistance). -/
def kineticFrictionForce : DimensionedKind :=
  forceSpecies "kinetic friction force" ForcePrinciple.slidingResistance
/-- Rolling resistance — item 4-9.5, a force species (rolling resistance). -/
def rollingResistance : DimensionedKind :=
  forceSpecies "rolling resistance" ForcePrinciple.rollingResistanceP
/-- Drag force — item 4-9.6, a force species (fluid resistance). -/
def dragForce : DimensionedKind := forceSpecies "drag force" ForcePrinciple.fluidResistance
/-- Impulse — item 4-10, dimension `M·L·T⁻¹` (a vector quantity; the same dimension as
momentum, a distinct kind — unit N·s, not kg·m/s). -/
def impulse : DimensionedKind := dimKind "impulse" MDim.momentum
/-- Angular momentum — item 4-11, dimension `M·L²·T⁻¹` (a vector quantity). -/
def angularMomentum : DimensionedKind := dimKind "angular momentum" MDim.angularMomentum
/-- Moment of force — item 4-12.1, dimension `M·L²·T⁻²` (a vector quantity; the same
dimension as energy, a distinct kind — unit N·m, not J). -/
def momentOfForce : DimensionedKind := dimKind "moment of force" MDim.energy
/-- Torque — item 4-12.2, dimension `M·L²·T⁻²` (unit N·m). -/
def torque : DimensionedKind := dimKind "torque" MDim.energy
/-- Angular impulse — item 4-13, dimension `M·L²·T⁻¹` (the same dimension as angular
momentum, a distinct kind). -/
def angularImpulse : DimensionedKind := dimKind "angular impulse" MDim.angularMomentum

/-! ## (C) Pressure, stress, strain, the elastic moduli, compressibility (4-14 … 4-20)

Pressure, gauge pressure, stress, normal stress, shear stress, and the three elastic
moduli are *all* dimension `M·L⁻¹·T⁻²` (the pascal) — distinct kinds the dimension
cannot separate. The strains and the Poisson number are *all* dimension one. -/

/-- Pressure — item 4-14.1, dimension `M·L⁻¹·T⁻²` (unit Pa). The force/area remark is
formalized in `Part4.DefiningRelations`. -/
def pressure : DimensionedKind := dimKind "pressure" MDim.pressure
/-- Gauge pressure — item 4-14.2, dimension `M·L⁻¹·T⁻²`. -/
def gaugePressure : DimensionedKind := dimKind "gauge pressure" MDim.pressure
/-- Stress — item 4-15, dimension `M·L⁻¹·T⁻²` (a tensor quantity). -/
def stress : DimensionedKind := dimKind "stress" MDim.pressure
/-- Normal stress — item 4-16.1, dimension `M·L⁻¹·T⁻²`. -/
def normalStress : DimensionedKind := dimKind "normal stress" MDim.pressure
/-- Shear stress — item 4-16.2, dimension `M·L⁻¹·T⁻²`. -/
def shearStress : DimensionedKind := dimKind "shear stress" MDim.pressure
/-- Strain — item 4-17.1, dimension one (a tensor quantity). -/
def strain : DimensionedKind := dimKind "strain" Dim.one
/-- Relative linear strain — item 4-17.2, dimension one. -/
def relativeLinearStrain : DimensionedKind := dimKind "relative linear strain" Dim.one
/-- Shear strain — item 4-17.3, dimension one. -/
def shearStrain : DimensionedKind := dimKind "shear strain" Dim.one
/-- Relative volume strain — item 4-17.4, dimension one. -/
def relativeVolumeStrain : DimensionedKind := dimKind "relative volume strain" Dim.one
/-- Poisson number — item 4-18, dimension one. -/
def poissonNumber : DimensionedKind := dimKind "Poisson number" Dim.one
/-- Modulus of elasticity (Young modulus) — item 4-19.1, dimension `M·L⁻¹·T⁻²`. The
stress/strain remark is formalized in `Part4.DefiningRelations`. -/
def modulusOfElasticity : DimensionedKind := dimKind "modulus of elasticity" MDim.pressure
/-- Modulus of rigidity (shear modulus) — item 4-19.2, dimension `M·L⁻¹·T⁻²`. -/
def modulusOfRigidity : DimensionedKind := dimKind "modulus of rigidity" MDim.pressure
/-- Modulus of compression (bulk modulus) — item 4-19.3, dimension `M·L⁻¹·T⁻²`. -/
def modulusOfCompression : DimensionedKind :=
  dimKind "modulus of compression" MDim.pressure
/-- Compressibility — item 4-20, dimension `M⁻¹·L·T²` (the reciprocal of pressure). -/
def compressibility : DimensionedKind := dimKind "compressibility" MDim.compressibility

/-! ## (D) Second moments of area, section modulus, friction factors, viscosity,
surface tension (items 4-21 … 4-26) -/

/-- Second axial moment of area — item 4-21.1, dimension `L⁴`. -/
def secondAxialMomentOfArea : DimensionedKind :=
  dimKind "second axial moment of area" MDim.secondMomentOfArea
/-- Second polar moment of area — item 4-21.2, dimension `L⁴`. -/
def secondPolarMomentOfArea : DimensionedKind :=
  dimKind "second polar moment of area" MDim.secondMomentOfArea
/-- Section modulus — item 4-22, dimension `L³` (the volume dimension, a distinct
kind). -/
def sectionModulus : DimensionedKind := dimKind "section modulus" MDim.sectionModulus
/-- Static friction factor — item 4-23.1, dimension one. -/
def staticFrictionFactor : DimensionedKind := dimKind "static friction factor" Dim.one
/-- Kinetic friction factor — item 4-23.2, dimension one. -/
def kineticFrictionFactor : DimensionedKind := dimKind "kinetic friction factor" Dim.one
/-- Rolling resistance factor — item 4-23.3, dimension one. -/
def rollingResistanceFactor : DimensionedKind :=
  dimKind "rolling resistance factor" Dim.one
/-- Drag coefficient — item 4-23.4, dimension one. -/
def dragCoefficient : DimensionedKind := dimKind "drag coefficient" Dim.one
/-- Dynamic viscosity (viscosity) — item 4-24, dimension `M·L⁻¹·T⁻¹`. The remark
relating it to kinematic viscosity is formalized in `Part4.DefiningRelations`. -/
def dynamicViscosity : DimensionedKind := dimKind "dynamic viscosity" MDim.dynamicViscosity
/-- Kinematic viscosity — item 4-25, dimension `L²·T⁻¹`. -/
def kinematicViscosity : DimensionedKind :=
  dimKind "kinematic viscosity" MDim.kinematicViscosity
/-- Surface tension — item 4-26, dimension `M·T⁻²`. -/
def surfaceTension : DimensionedKind := dimKind "surface tension" MDim.surfaceTension

/-! ## (E) Power, the energy family, and efficiency (items 4-27 … 4-29)

Potential, kinetic, mechanical energy and mechanical work are *all* energies
(dimension `M·L²·T⁻²`, unit J) — and *all* share that dimension with torque, which is
not an energy. Efficiency is dimension one *because* it is a ratio of two powers. -/

/-- Power — item 4-27, dimension `M·L²·T⁻³` (unit W). -/
def power : DimensionedKind := dimKind "power" MDim.power
/-- Potential energy — item 4-28.1, dimension `M·L²·T⁻²` (unit J). -/
def potentialEnergy : DimensionedKind := dimKind "potential energy" MDim.energy
/-- Kinetic energy — item 4-28.2, dimension `M·L²·T⁻²` (unit J). -/
def kineticEnergy : DimensionedKind := dimKind "kinetic energy" MDim.energy
/-- Mechanical energy — item 4-28.3, dimension `M·L²·T⁻²` (unit J). -/
def mechanicalEnergy : DimensionedKind := dimKind "mechanical energy" MDim.energy
/-- Mechanical work (work) — item 4-28.4, dimension `M·L²·T⁻²` (unit J). -/
def mechanicalWork : DimensionedKind := dimKind "mechanical work" MDim.energy
/-- Efficiency — item 4-29, dimension one (a ratio of two powers). The
output/input-power remark is formalized in `Part4.DefiningRelations`. -/
def efficiency : DimensionedKind := dimKind "efficiency" Dim.one

/-! ## (F) The flows and action (items 4-30 … 4-32) -/

/-- Mass flow — item 4-30.1, dimension `M·L⁻²·T⁻¹` (a vector quantity). -/
def massFlow : DimensionedKind := dimKind "mass flow" MDim.massFlow
/-- Mass flow rate — item 4-30.2, dimension `M·T⁻¹`. -/
def massFlowRate : DimensionedKind := dimKind "mass flow rate" MDim.massRate
/-- Mass change rate — item 4-30.3, dimension `M·T⁻¹`. -/
def massChangeRate : DimensionedKind := dimKind "mass change rate" MDim.massRate
/-- Volume flow rate — item 4-31, dimension `L³·T⁻¹`. -/
def volumeFlowRate : DimensionedKind := dimKind "volume flow rate" MDim.volumeFlowRate
/-- Action — item 4-32, dimension `M·L²·T⁻¹` (the same dimension as angular momentum,
a distinct kind — unit J·s). -/
def action : DimensionedKind := dimKind "action" MDim.angularMomentum

/-! ## The catalogue (every kind, with its source as data) -/

/-- Mass and the densities. -/
def massCK : CataloguedKind := cat "4-1" "m" "kg" mass
def massDensityCK : CataloguedKind := cat "4-2" "ρ" "kg/m³" massDensity
def specificVolumeCK : CataloguedKind := cat "4-3" "v" "m³/kg" specificVolume
def relativeMassDensityCK : CataloguedKind := cat "4-4" "d" "1" relativeMassDensity
def surfaceMassDensityCK : CataloguedKind := cat "4-5" "ρ_A" "kg/m²" surfaceMassDensity
def linearMassDensityCK : CataloguedKind := cat "4-6" "ρ_l" "kg/m" linearMassDensity
def momentOfInertiaCK : CataloguedKind := cat "4-7" "J" "kg·m²" momentOfInertia

/-- Momentum, the force family, impulse, and moments. -/
def momentumCK : CataloguedKind := cat "4-8" "p" "kg·m/s" momentum
def forceCK : CataloguedKind := cat "4-9.1" "F" "N" force
def weightCK : CataloguedKind := cat "4-9.2" "F_g" "N" weight
def staticFrictionForceCK : CataloguedKind := cat "4-9.3" "F_s" "N" staticFrictionForce
def kineticFrictionForceCK : CataloguedKind := cat "4-9.4" "F_k" "N" kineticFrictionForce
def rollingResistanceCK : CataloguedKind := cat "4-9.5" "F_rr" "N" rollingResistance
def dragForceCK : CataloguedKind := cat "4-9.6" "F_D" "N" dragForce
def impulseCK : CataloguedKind := cat "4-10" "I" "N·s" impulse
def angularMomentumCK : CataloguedKind := cat "4-11" "L" "kg·m²/s" angularMomentum
def momentOfForceCK : CataloguedKind := cat "4-12.1" "M" "N·m" momentOfForce
def torqueCK : CataloguedKind := cat "4-12.2" "T" "N·m" torque
def angularImpulseCK : CataloguedKind := cat "4-13" "H" "N·m·s" angularImpulse

/-- Pressure, stress, strain, the elastic moduli, compressibility. -/
def pressureCK : CataloguedKind := cat "4-14.1" "p" "Pa" pressure
def gaugePressureCK : CataloguedKind := cat "4-14.2" "p_e" "Pa" gaugePressure
def stressCK : CataloguedKind := cat "4-15" "σ" "Pa" stress
def normalStressCK : CataloguedKind := cat "4-16.1" "σ_n" "Pa" normalStress
def shearStressCK : CataloguedKind := cat "4-16.2" "τ" "Pa" shearStress
def strainCK : CataloguedKind := cat "4-17.1" "ε" "1" strain
def relativeLinearStrainCK : CataloguedKind := cat "4-17.2" "ε" "1" relativeLinearStrain
def shearStrainCK : CataloguedKind := cat "4-17.3" "γ" "1" shearStrain
def relativeVolumeStrainCK : CataloguedKind := cat "4-17.4" "ϑ" "1" relativeVolumeStrain
def poissonNumberCK : CataloguedKind := cat "4-18" "μ" "1" poissonNumber
def modulusOfElasticityCK : CataloguedKind := cat "4-19.1" "E" "Pa" modulusOfElasticity
def modulusOfRigidityCK : CataloguedKind := cat "4-19.2" "G" "Pa" modulusOfRigidity
def modulusOfCompressionCK : CataloguedKind := cat "4-19.3" "K" "Pa" modulusOfCompression
def compressibilityCK : CataloguedKind := cat "4-20" "ϰ" "Pa⁻¹" compressibility

/-- Second moments of area, section modulus, friction factors, viscosity, surface
tension. -/
def secondAxialMomentOfAreaCK : CataloguedKind :=
  cat "4-21.1" "I_a" "m⁴" secondAxialMomentOfArea
def secondPolarMomentOfAreaCK : CataloguedKind :=
  cat "4-21.2" "I_p" "m⁴" secondPolarMomentOfArea
def sectionModulusCK : CataloguedKind := cat "4-22" "Z" "m³" sectionModulus
def staticFrictionFactorCK : CataloguedKind := cat "4-23.1" "μ_s" "1" staticFrictionFactor
def kineticFrictionFactorCK : CataloguedKind := cat "4-23.2" "μ" "1" kineticFrictionFactor
def rollingResistanceFactorCK : CataloguedKind :=
  cat "4-23.3" "C_rr" "1" rollingResistanceFactor
def dragCoefficientCK : CataloguedKind := cat "4-23.4" "C_D" "1" dragCoefficient
def dynamicViscosityCK : CataloguedKind := cat "4-24" "η" "Pa·s" dynamicViscosity
def kinematicViscosityCK : CataloguedKind := cat "4-25" "ν" "m²/s" kinematicViscosity
def surfaceTensionCK : CataloguedKind := cat "4-26" "γ" "N/m" surfaceTension

/-- Power, the energy family, and efficiency. -/
def powerCK : CataloguedKind := cat "4-27" "P" "W" power
def potentialEnergyCK : CataloguedKind := cat "4-28.1" "V" "J" potentialEnergy
def kineticEnergyCK : CataloguedKind := cat "4-28.2" "T" "J" kineticEnergy
def mechanicalEnergyCK : CataloguedKind := cat "4-28.3" "E" "J" mechanicalEnergy
def mechanicalWorkCK : CataloguedKind := cat "4-28.4" "W" "J" mechanicalWork
def efficiencyCK : CataloguedKind := cat "4-29" "η" "1" efficiency

/-- The flows and action. -/
def massFlowCK : CataloguedKind := cat "4-30.1" "j_m" "kg/(m²·s)" massFlow
def massFlowRateCK : CataloguedKind := cat "4-30.2" "q_m" "kg/s" massFlowRate
def massChangeRateCK : CataloguedKind := cat "4-30.3" "q_m" "kg/s" massChangeRate
def volumeFlowRateCK : CataloguedKind := cat "4-31" "q_V" "m³/s" volumeFlowRate
def actionCK : CataloguedKind := cat "4-32" "S" "J·s" action

/-- The full ISO 80000-4 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [massCK, massDensityCK, specificVolumeCK, relativeMassDensityCK, surfaceMassDensityCK,
   linearMassDensityCK, momentOfInertiaCK, momentumCK, forceCK, weightCK,
   staticFrictionForceCK, kineticFrictionForceCK, rollingResistanceCK, dragForceCK,
   impulseCK, angularMomentumCK, momentOfForceCK, torqueCK, angularImpulseCK,
   pressureCK, gaugePressureCK, stressCK, normalStressCK, shearStressCK, strainCK,
   relativeLinearStrainCK, shearStrainCK, relativeVolumeStrainCK, poissonNumberCK,
   modulusOfElasticityCK, modulusOfRigidityCK, modulusOfCompressionCK, compressibilityCK,
   secondAxialMomentOfAreaCK, secondPolarMomentOfAreaCK, sectionModulusCK,
   staticFrictionFactorCK, kineticFrictionFactorCK, rollingResistanceFactorCK,
   dragCoefficientCK, dynamicViscosityCK, kinematicViscosityCK, surfaceTensionCK,
   powerCK, potentialEnergyCK, kineticEnergyCK, mechanicalEnergyCK, mechanicalWorkCK,
   efficiencyCK, massFlowCK, massFlowRateCK, massChangeRateCK, volumeFlowRateCK, actionCK]

/-! ## (G) Units — a few coherent SI units of these kinds

Each unit references its kind, so a kilogram and a newton are not commensurable; a
newton metre and a joule are not commensurable *though both are `M·L²·T⁻²`* — all
type-level facts, not runtime checks. -/

/-- The kilogram, the SI unit of mass (item 4-1). -/
def kilogram : MetrologicalUnit := mass.kind.unit "kg"
/-- The newton, the SI unit of force (item 4-9.1). -/
def newton : MetrologicalUnit := force.kind.unit "N"
/-- The pascal, the SI unit of pressure (item 4-14.1) — dimension `M·L⁻¹·T⁻²`. -/
def pascal : MetrologicalUnit := pressure.kind.unit "Pa"
/-- The joule, the SI unit of mechanical energy (item 4-28.3) — dimension `M·L²·T⁻²`. -/
def joule : MetrologicalUnit := mechanicalEnergy.kind.unit "J"
/-- The newton metre, the SI unit of torque (item 4-12.2) — *also* `M·L²·T⁻²`, but a
unit of torque, not of energy. -/
def newtonMetre : MetrologicalUnit := torque.kind.unit "N·m"
/-- The watt, the SI unit of power (item 4-27) — dimension `M·L²·T⁻³`. -/
def watt : MetrologicalUnit := power.kind.unit "W"

/-! ## (H) Checked dimensional facts (the dimensional algebra) -/

/-- Mass carries the mass dimension `M`. -/
theorem mass_dim : mass.dim = Dim.mass := rfl

/-- Momentum is `M·L·T⁻¹`: its mass-exponent is `1` (ISO 80000-4 item 4-8). -/
theorem momentum_dim_mass : momentum.dim.mass = 1 := by
  simp [momentum, dimKind, MDim.momentum, Dim.mass, Dim.speed, Dimension.mass_mul,
    Dimension.div_mass, Dimension.L𝓭_mass, Dimension.T𝓭_mass, Dimension.M𝓭]

/-- Force is `M·L·T⁻²`: its time-exponent is `-2` (ISO 80000-4 item 4-9.1). -/
theorem force_dim_time : force.dim.time = -2 := by
  norm_num [force, dimKind, MDim.force, Dim.mass, Dim.length, Dim.time,
    Dimension.div_time, Dimension.time_mul, Dimension.L𝓭_time, Dimension.T𝓭_time,
    Dimension.M𝓭]

/-- Energy (and torque) is `M·L²·T⁻²`: its length-exponent is `2` (item 4-28). -/
theorem energy_dim_length : mechanicalEnergy.dim.length = 2 := by
  norm_num [mechanicalEnergy, dimKind, MDim.energy, Dim.mass, Dim.area, Dim.time,
    Dimension.div_length, Dimension.length_mul, Dimension.L𝓭_length, Dimension.T𝓭_length,
    Dimension.M𝓭]

/-- Pressure is `M·L⁻¹·T⁻²`: its length-exponent is `-1` (ISO 80000-4 item 4-14.1). -/
theorem pressure_dim_length : pressure.dim.length = -1 := by
  simp [pressure, dimKind, MDim.pressure, Dim.mass, Dim.length, Dim.time,
    Dimension.div_length, Dimension.length_mul, Dimension.L𝓭_length, Dimension.T𝓭_length,
    Dimension.M𝓭]

/-- Power is `M·L²·T⁻³`: its time-exponent is `-3` (ISO 80000-4 item 4-27). -/
theorem power_dim_time : power.dim.time = -3 := by
  norm_num [power, dimKind, MDim.power, Dim.mass, Dim.area, Dim.time,
    Dimension.div_time, Dimension.time_mul, Dimension.L𝓭_time, Dimension.T𝓭_time,
    Dimension.M𝓭]

/-! ## (I) Unit well-formedness and (in)commensurability -/

/-- The kilogram is a well-formed unit (mass is ratio-scale, so it bears a unit). -/
theorem kilogram_wellFormed : kilogram.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- The newton is a well-formed unit of force. -/
theorem newton_wellFormed : newton.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- The kilogram and the newton are **not** commensurable — mass and force are distinct
kinds (a type-level fact). -/
theorem kilogram_newton_not_commensurable : ¬ kilogram.Commensurable newton := by
  unfold MetrologicalUnit.Commensurable kilogram newton mass force dimKind KindOfProperty.unit
  decide

/-- **The newton metre is not a joule, though both are `M·L²·T⁻²`.** The SI units of
torque and energy are not commensurable, because their kinds differ — the textbook
case that a dimension does not determine a unit. -/
theorem newtonMetre_joule_not_commensurable : ¬ newtonMetre.Commensurable joule := by
  unfold MetrologicalUnit.Commensurable newtonMetre joule torque mechanicalEnergy dimKind
    KindOfProperty.unit
  decide

/-! ## (J) The force family as a specialization lattice (requirement R2)

The direct-parent edges of the force family, mirroring the standard's own definitions:
weight, the two friction forces, the rolling resistance, and the drag force are each
defined as "force (item 4-9.1) … acting/resisting …", so each is a direct kind of
force. Specialization is the reflexive-transitive closure of these edges. -/

/-- This application's system of force quantities — the direct-parent edges among the
species of the force family (item 4-9). -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  /-- A weight is a kind of force (item 4-9.2 via force). -/
  | weight_force : Edge weight.kind force.kind
  /-- A static friction force is a kind of force (item 4-9.3 via force). -/
  | staticFriction_force : Edge staticFrictionForce.kind force.kind
  /-- A kinetic friction force is a kind of force (item 4-9.4 via force). -/
  | kineticFriction_force : Edge kineticFrictionForce.kind force.kind
  /-- A rolling resistance is a kind of force (item 4-9.5 via force). -/
  | rollingResistance_force : Edge rollingResistance.kind force.kind
  /-- A drag force is a kind of force (item 4-9.6 via force). -/
  | dragForce_force : Edge dragForce.kind force.kind

/-- Weight specializes force. -/
theorem weight_specializes_force : Specializes Edge weight.kind force.kind :=
  Specializes.of_edge Edge.weight_force

/-- Each force species is **examined by** its declared measurement principle. -/
theorem weight_examinedBy : weight.kind.examinedBy ForcePrinciple.gravitational := rfl

/-- **Static and kinetic friction forces are distinct kinds — by measurement
principle, not by fiat.** They have the same dimension `M·L·T⁻²` and are both
"friction forces", yet they are different kinds *because they are examined under
different conditions* (resistance before sliding vs during sliding), proved through
`distinct_of_examPrinciple` (§7.5) rather than by appealing to their `id` strings.
This is the force-family analogue of width ≠ distance. -/
theorem staticFriction_ne_kineticFriction :
    staticFrictionForce.kind ≠ kineticFrictionForce.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- Weight and the drag force are distinct kinds, again by their differing examination
principles (gravitational-field action vs fluid resistance). -/
theorem weight_ne_dragForce : weight.kind ≠ dragForce.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- A force species is distinct from the general force kind: a species carries an
examination principle, the genus carries none. -/
theorem weight_ne_force : weight.kind ≠ force.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- **Mutual comparability is preserved.** Weight and the drag force, though distinct
kinds, remain *mutually comparable* — they share the super-kind force, so combining
them is possible but only via an explicit up-cast, never silently. -/
theorem weight_dragForce_comparable :
    MutuallyComparable Edge weight.kind dragForce.kind :=
  ⟨force.kind, Specializes.of_edge Edge.weight_force,
    Specializes.of_edge Edge.dragForce_force⟩

/-! ## (K) Dimension collisions — the kind classifies where the dimension cannot

Same-dimension/distinct-kind pairs drawn from the catalogue above. The {dimension
functor} `dim` identifies the members of each pair; the kind layer keeps them apart. -/

/-- Torque and energy share dimension `M·L²·T⁻²`. -/
theorem torque_dim_eq_energy_dim : torque.dim = mechanicalEnergy.dim := rfl

/-- **Torque is not energy.** They are distinct kinds despite sharing the dimension
`M·L²·T⁻²` — the textbook case the kind layer resolves and the dimension cannot. -/
theorem torque_ne_energy : torque.kind ≠ mechanicalEnergy.kind := by
  unfold torque mechanicalEnergy dimKind; decide

/-- Momentum and impulse share dimension `M·L·T⁻¹`. -/
theorem momentum_dim_eq_impulse_dim : momentum.dim = impulse.dim := rfl

/-- Momentum and impulse are distinct kinds (unit kg·m/s vs N·s). -/
theorem momentum_ne_impulse : momentum.kind ≠ impulse.kind := by
  unfold momentum impulse dimKind; decide

/-- Efficiency and the relative mass density are distinct kinds, both dimension one. -/
theorem efficiency_ne_relativeMassDensity :
    efficiency.kind ≠ relativeMassDensity.kind := by
  unfold efficiency relativeMassDensity dimKind; decide

/-- **The torque/energy collision, on standard quantities.** There exist distinct
ISO 80000-4 kinds with the same dimension `M·L²·T⁻²` — torque and energy witness it.
PhysLib's `Dimension`, and any dimension-only type system, cannot separate them; the
kind layer does. This is the textbook dimension-does-not-classify case. -/
theorem iso80000_4_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨torque, mechanicalEnergy, torque_ne_energy, torque_dim_eq_energy_dim⟩

/-- **The dimension-1 disambiguation, on standard quantities.** There exist distinct
ISO 80000-4 kinds with the same dimension one — efficiency and the relative mass
density witness it (alongside the strains, the Poisson number, and the friction
factors). Dimension cannot separate them; the kind layer does. -/
theorem iso80000_4_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨efficiency, relativeMassDensity, efficiency_ne_relativeMassDensity, rfl, rfl⟩

end PropertyKindCalculus.Iso80000.Part4
