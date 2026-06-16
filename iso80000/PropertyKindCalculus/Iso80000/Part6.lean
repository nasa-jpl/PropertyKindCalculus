/-
# IEC 80000-6 — Electromagnetism (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
IEC 80000-6 *Electromagnetism* — all of items 6-1 … 6-62, including every
sub-suffixed item (6-2.1/6-2.2, 6-11.1 … 6-11.4, 6-14.1/6-14.2, 6-19.1/6-19.2,
6-22.1 … 6-22.4, 6-26.1/6-26.2, 6-35.1/6-35.2, 6-37.1 … 6-37.3, 6-41.1/6-41.2,
6-42.1/6-42.2, 6-51.1 … 6-51.5, 6-52.1 … 6-52.5) — each carrying its exact source
as data: the part (`iec80000_6`), the printed item designation, the principal
quantity symbol, and the coherent SI unit symbol. Only **citation locators** are
recorded (item number, symbol, coherent SI unit); no normative content
(definitions, remarks) from the licensed standard is reproduced. The defining
*mathematics* of selected remarks is formalized in the sibling module
`Part6.DefiningRelations`.

IEC 80000-6 is the one **IEC**-published part of the series catalogued here, and it
introduces the last SI base quantity the earlier parts did not exercise — and
sharpens the two axes the calculus already pressed:

* **A new SI base quantity — electric current.** Items 6-1 (*electric current*,
  the ampere) and 6-2.1 (*electric charge*, the coulomb) bring in the
  electromagnetic base axis. PhysLib's `Dimension` takes electric **charge** `C` as
  the base generator, so electric current appears as `charge · time⁻¹` (the ampere
  as coulomb per second); the two presentations of the electromagnetic dimension
  group are isomorphic. All of Part 6's dimensions are composed over this generator
  together with mass `M`, length `L`, and time `T`.

* **The scale type discriminates where dimension cannot — requirement R6, again on
  the real standard.** *Electric potential* (item 6-11.1) is fixed only up to an
  arbitrary additive reference (gauge freedom; "the electric potential is not
  unique"), so only its **differences** are physically meaningful — it is
  **interval-scale**. *Electric potential difference* (6-11.2) and *voltage*
  (6-11.3) are genuine differences and so are **ratio-scale**, of the *same*
  dimension `V`. The {scale type} keeps them apart exactly as thermodynamic and
  Celsius temperature were kept apart in Part 5 — the gauge-dependent potential is
  electromagnetism's Celsius temperature.

* **Dimension does not classify; the kind does — the power case, sharper than
  entropy/heat-capacity.** *Active power* (6-56), *reactive power* (6-60),
  *apparent power* (6-57), *complex power* (6-59), and *non-active power* (6-61) are
  *all* dimension `M·L²·T⁻³` — yet they carry **three different coherent-unit
  strings** (the watt `W`, the var `var`, and the volt-ampere `VA`) precisely to
  keep the kinds apart in print. The {dimension functor} `dim` collapses all of
  them to one point; the kind layer — and the unit, which is keyed on the kind —
  keeps them distinct. This is a sharper collision than Part 5's joule-per-kelvin:
  there even the unit string agreed; here the standard itself spends three unit
  strings on one dimension.

* **The power family is a specialization lattice (requirement R2).** Item 6-45,
  *power*, is the broad genus; the AC power quantities — active, reactive, apparent,
  complex, and non-active power — are *species* of power, same dimension `M·L²·T⁻³`,
  individuated **not by fiat** but by an explicit {examination principle} (which
  component of the periodic process each isolates). This is the length-family
  pattern of Part 3, the force-family pattern of Part 4, and the
  thermodynamic-potential pattern of Part 5, now on the AC power quantities.

* **Electromagnetic quantities are built from one another by the kind algebra.**
  Ohm's law (resistance is voltage per current), the reciprocal pairs
  (conductance/resistance, admittance/impedance, permeance/reluctance), and the
  product laws (power is voltage times current) compose Part-6 kinds out of one
  another — the kind-laws in `Part6.DefiningRelations` realize these as
  `QuotientKind`, `ReciprocalKind`, and `ProductKind` facts, with the dimension
  following from the relation as a checked computation.

* **The dimensional facts are checked computations**, not annotations: an electric
  current is `C·T⁻¹`, a capacitance `C²·M⁻¹·L⁻²·T²`, a resistance `M·L²·T⁻¹·C⁻²`,
  all discharged in PhysLib's dimension group over the charge generator `C`.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.Iso80000.Catalogue

namespace PropertyKindCalculus.Iso80000.Part6

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iec80000_6

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Electromagnetic dimensions

The dimensions of electromagnetism, composed in PhysLib's `Dimension` group from the
base generators mass `M`, length `L`, time `T`, and — new to this part — electric
charge `C` (`Dim.charge`), with electric current `A = C·T⁻¹` (`Dim.current`). Naming
the recurring ones once keeps each quantity-kind's dimension readable and makes the
*dimension collisions* — the three power quantities, resistance and reactance,
relative permittivity and relative permeability — provable by reflexivity. -/

namespace EDim

/-- Energy and work, `M·L²·T⁻²` (force times length). -/
def energy : Dimension := Dim.mass * Dim.area / (Dim.time * Dim.time)
/-- Power, `M·L²·T⁻³` (energy per time). -/
def power : Dimension := energy / Dim.time
/-- Volume, `L³`. -/
def volume : Dimension := Dim.area * Dim.length
/-- Electric charge density, `C·L⁻³` (charge per volume). -/
def chargeDensity : Dimension := Dim.charge / volume
/-- Surface density of charge, electric polarization, electric flux density, `C·L⁻²`
(charge per area). -/
def surfaceChargeDensity : Dimension := Dim.charge / Dim.area
/-- Linear density of charge, `C·L⁻¹` (charge per length). -/
def linearChargeDensity : Dimension := Dim.charge / Dim.length
/-- Electric dipole moment, `C·L` (charge times length). -/
def electricDipoleMoment : Dimension := Dim.charge * Dim.length
/-- Electric current density, `C·T⁻¹·L⁻²` (current per area). -/
def currentDensity : Dimension := Dim.current / Dim.area
/-- Linear electric current density, `C·T⁻¹·L⁻¹` (current per length). -/
def linearCurrentDensity : Dimension := Dim.current / Dim.length
/-- Electric potential, potential difference, voltage, `M·L²·T⁻²·C⁻¹` (energy per
charge). -/
def voltage : Dimension := energy / Dim.charge
/-- Electric field strength, `M·L·T⁻²·C⁻¹` (voltage per length). -/
def electricFieldStrength : Dimension := voltage / Dim.length
/-- Capacitance, `C²·M⁻¹·L⁻²·T²` (charge per voltage; the farad). -/
def capacitance : Dimension := Dim.charge * Dim.charge / energy
/-- Permittivity, `C²·M⁻¹·L⁻³·T²` (capacitance per length; the farad per metre). -/
def permittivity : Dimension := capacitance / Dim.length
/-- Magnetic flux density, `M·T⁻¹·C⁻¹` (voltage-second per area; the tesla). -/
def magneticFluxDensity : Dimension := voltage * Dim.time / Dim.area
/-- Magnetic flux, `M·L²·T⁻¹·C⁻¹` (voltage-second; the weber). -/
def magneticFlux : Dimension := voltage * Dim.time
/-- Magnetic moment, `C·T⁻¹·L²` (current times area). -/
def magneticMoment : Dimension := Dim.current * Dim.area
/-- Magnetization, magnetic field strength, coercivity, `C·T⁻¹·L⁻¹` (current per
length). -/
def magneticFieldStrength : Dimension := Dim.current / Dim.length
/-- Inductance, permeance, `M·L²·C⁻²` (flux per current; the henry). -/
def inductance : Dimension := magneticFlux / Dim.current
/-- Permeability, `M·L·C⁻²` (inductance per length; the henry per metre). -/
def permeability : Dimension := inductance / Dim.length
/-- Reluctance, `M⁻¹·L⁻²·C²` (the reciprocal of inductance; the reciprocal henry). -/
def reluctance : Dimension := inductance⁻¹
/-- Magnetic vector potential, `M·L·T⁻¹·C⁻¹` (flux per length; the weber per metre). -/
def magneticVectorPotential : Dimension := magneticFlux / Dim.length
/-- Magnetic dipole moment, `M·L³·T⁻¹·C⁻¹` (flux times length; the weber metre). -/
def magneticDipoleMoment : Dimension := magneticFlux * Dim.length
/-- Electromagnetic energy density, `M·L⁻¹·T⁻²` (energy per volume). -/
def energyDensity : Dimension := energy / volume
/-- Poynting vector, `M·T⁻³` (power per area). -/
def poyntingVector : Dimension := power / Dim.area
/-- Resistance, impedance, `M·L²·T⁻¹·C⁻²` (voltage per current; the ohm). -/
def resistance : Dimension := voltage / Dim.current
/-- Conductance, admittance, `M⁻¹·L⁻²·T·C²` (the reciprocal of resistance; the
siemens). -/
def conductance : Dimension := resistance⁻¹
/-- Conductivity, `M⁻¹·L⁻³·T·C²` (conductance per length; the siemens per metre). -/
def conductivity : Dimension := conductance / Dim.length
/-- Resistivity, `M·L³·T⁻¹·C⁻²` (resistance times length; the ohm metre). -/
def resistivity : Dimension := resistance * Dim.length

end EDim

/-! ## (A) Electric current and charge — the base axis (items 6-1, 6-2)

Item 6-1, *electric current*, is one of the seven ISQ base quantities — the ampere,
`C·T⁻¹` over PhysLib's charge generator. Item 6-2.1, *electric charge*, is the
coulomb `C`; the *elementary charge* (6-2.2) is a particular charge. -/

/-- Electric current — item 6-1, dimension `C·T⁻¹` (unit A). One of the seven ISQ base
quantities (taken here over PhysLib's charge generator). -/
def electricCurrent : DimensionedKind := dimKind "electric current" Dim.current
/-- Electric charge — item 6-2.1, dimension `C` (unit C, the coulomb). -/
def electricCharge : DimensionedKind := dimKind "electric charge" Dim.charge
/-- Elementary charge — item 6-2.2, dimension `C` (a fundamental constant, unit C). -/
def elementaryCharge : DimensionedKind := dimKind "elementary charge" Dim.charge

/-! ## (B) Charge and current distributions; the dipole and polarization (items 6-3 … 6-9)

The charge densities (6-3 … 6-5) are charge per volume/area/length; the dipole moment
(6-6) is charge times length; electric polarization (6-7) shares `C·L⁻²` with the
surface charge density. The current densities (6-8, 6-9) are current per area/length. -/

/-- Electric charge density — item 6-3, dimension `C·L⁻³` (unit C/m³). -/
def electricChargeDensity : DimensionedKind :=
  dimKind "electric charge density" EDim.chargeDensity
/-- Surface density of electric charge — item 6-4, dimension `C·L⁻²` (unit C/m²). -/
def surfaceChargeDensity : DimensionedKind :=
  dimKind "surface density of electric charge" EDim.surfaceChargeDensity
/-- Linear density of electric charge — item 6-5, dimension `C·L⁻¹` (unit C/m). -/
def linearChargeDensity : DimensionedKind :=
  dimKind "linear density of electric charge" EDim.linearChargeDensity
/-- Electric dipole moment — item 6-6, dimension `C·L` (unit C·m). -/
def electricDipoleMoment : DimensionedKind :=
  dimKind "electric dipole moment" EDim.electricDipoleMoment
/-- Electric polarization — item 6-7, dimension `C·L⁻²` (unit C/m²; the same dimension
as the surface charge density, a distinct kind). -/
def electricPolarization : DimensionedKind :=
  dimKind "electric polarization" EDim.surfaceChargeDensity
/-- Electric current density — item 6-8, dimension `C·T⁻¹·L⁻²` (unit A/m²). -/
def electricCurrentDensity : DimensionedKind :=
  dimKind "electric current density" EDim.currentDensity
/-- Linear electric current density — item 6-9, dimension `C·T⁻¹·L⁻¹` (unit A/m). -/
def linearCurrentDensity : DimensionedKind :=
  dimKind "linear electric current density" EDim.linearCurrentDensity

/-! ## (C) The electric field, potential, and voltage — one dimension, two scales
(items 6-10 … 6-11.4)

Item 6-11.1, *electric potential*, is fixed only up to an arbitrary additive
reference (gauge freedom), so it is **interval-scale** — only its differences are
meaningful. Item 6-11.2, *electric potential difference*, and 6-11.3, *voltage*, are
genuine differences of the *same* dimension `V` and so are **ratio-scale**. This is
requirement **R6** on the real standard — the gauge-dependent potential is
electromagnetism's Celsius temperature (Part 5). -/

/-- Electric field strength — item 6-10, dimension `M·L·T⁻²·C⁻¹` (unit V/m). -/
def electricFieldStrength : DimensionedKind :=
  dimKind "electric field strength" EDim.electricFieldStrength
/-- Electric potential — item 6-11.1, dimension `M·L²·T⁻²·C⁻¹` (unit V), **interval-scale**:
fixed only up to an arbitrary additive reference (gauge freedom), so a ratio of electric
potentials is not a meaningful operation — only their differences are. -/
def electricPotential : DimensionedKind :=
  { kind := { id := "electric potential", scale := .interval }, dim := EDim.voltage }
/-- Electric potential difference — item 6-11.2, dimension `M·L²·T⁻²·C⁻¹` (unit V),
ratio-scale (a genuine difference of potentials). -/
def electricPotentialDifference : DimensionedKind :=
  dimKind "electric potential difference" EDim.voltage
/-- Voltage — item 6-11.3, dimension `M·L²·T⁻²·C⁻¹` (unit V), ratio-scale. -/
def voltage : DimensionedKind := dimKind "voltage" EDim.voltage
/-- Induced voltage — item 6-11.4, dimension `M·L²·T⁻²·C⁻¹` (unit V), ratio-scale. -/
def inducedVoltage : DimensionedKind := dimKind "induced voltage" EDim.voltage

/-! ## (D) Electric flux density, capacitance, permittivity (items 6-12 … 6-17)

Electric flux density (6-12) shares `C·L⁻²` with electric polarization and the surface
charge density. Capacitance (6-13) is the farad; the electric constant (6-14.1) and
permittivity (6-14.2) are F/m. Relative permittivity (6-15) and electric susceptibility
(6-16) are dimension one. Electric flux (6-17) is a charge, `C`. -/

/-- Electric flux density — item 6-12, dimension `C·L⁻²` (unit C/m²). -/
def electricFluxDensity : DimensionedKind :=
  dimKind "electric flux density" EDim.surfaceChargeDensity
/-- Capacitance — item 6-13, dimension `C²·M⁻¹·L⁻²·T²` (unit F, the farad). The
charge/voltage remark is formalized in `Part6.DefiningRelations`. -/
def capacitance : DimensionedKind := dimKind "capacitance" EDim.capacitance
/-- Electric constant (vacuum permittivity) — item 6-14.1, dimension `C²·M⁻¹·L⁻³·T²`
(unit F/m). -/
def electricConstant : DimensionedKind := dimKind "electric constant" EDim.permittivity
/-- Permittivity — item 6-14.2, dimension `C²·M⁻¹·L⁻³·T²` (unit F/m). -/
def permittivity : DimensionedKind := dimKind "permittivity" EDim.permittivity
/-- Relative permittivity — item 6-15, dimension one (a ratio of permittivities). -/
def relativePermittivity : DimensionedKind :=
  dimKind "relative permittivity" Dim.one
/-- Electric susceptibility — item 6-16, dimension one. -/
def electricSusceptibility : DimensionedKind :=
  dimKind "electric susceptibility" Dim.one
/-- Electric flux — item 6-17, dimension `C` (unit C; a flux of the electric flux
density, dimension of charge). -/
def electricFlux : DimensionedKind := dimKind "electric flux" Dim.charge

/-! ## (E) Displacement and total currents (items 6-18 … 6-20)

The displacement current density (6-18) and total current density (6-20) share `A/m²`
with the conduction current density; the displacement current (6-19.1) and total
current (6-19.2) share `A` with electric current. -/

/-- Displacement current density — item 6-18, dimension `C·T⁻¹·L⁻²` (unit A/m²). -/
def displacementCurrentDensity : DimensionedKind :=
  dimKind "displacement current density" EDim.currentDensity
/-- Displacement current — item 6-19.1, dimension `C·T⁻¹` (unit A). -/
def displacementCurrent : DimensionedKind :=
  dimKind "displacement current" Dim.current
/-- Total current — item 6-19.2, dimension `C·T⁻¹` (unit A). -/
def totalCurrent : DimensionedKind := dimKind "total current" Dim.current
/-- Total current density — item 6-20, dimension `C·T⁻¹·L⁻²` (unit A/m²). -/
def totalCurrentDensity : DimensionedKind :=
  dimKind "total current density" EDim.currentDensity

/-! ## (F) The magnetic field — flux density, flux, moment, magnetization (items 6-21 … 6-25)

Magnetic flux density (6-21) is the tesla; magnetic flux and its variants (6-22.1 …
6-22.4) are all the weber, `Wb`. Magnetic moment (6-23) is `A·m²`; magnetization (6-24)
and magnetic field strength (6-25) are both `A/m`. -/

/-- Magnetic flux density — item 6-21, dimension `M·T⁻¹·C⁻¹` (unit T, the tesla). -/
def magneticFluxDensity : DimensionedKind :=
  dimKind "magnetic flux density" EDim.magneticFluxDensity
/-- Magnetic flux — item 6-22.1, dimension `M·L²·T⁻¹·C⁻¹` (unit Wb, the weber). -/
def magneticFlux : DimensionedKind := dimKind "magnetic flux" EDim.magneticFlux
/-- Protoflux — item 6-22.2, dimension `M·L²·T⁻¹·C⁻¹` (unit Wb). -/
def protoflux : DimensionedKind := dimKind "protoflux" EDim.magneticFlux
/-- Linked magnetic flux — item 6-22.3, dimension `M·L²·T⁻¹·C⁻¹` (unit Wb). -/
def linkedMagneticFlux : DimensionedKind :=
  dimKind "linked magnetic flux" EDim.magneticFlux
/-- Total magnetic flux — item 6-22.4, dimension `M·L²·T⁻¹·C⁻¹` (unit Wb). -/
def totalMagneticFlux : DimensionedKind :=
  dimKind "total magnetic flux" EDim.magneticFlux
/-- Magnetic moment — item 6-23, dimension `C·T⁻¹·L²` (unit A·m²). -/
def magneticMoment : DimensionedKind := dimKind "magnetic moment" EDim.magneticMoment
/-- Magnetization — item 6-24, dimension `C·T⁻¹·L⁻¹` (unit A/m). -/
def magnetization : DimensionedKind :=
  dimKind "magnetization" EDim.magneticFieldStrength
/-- Magnetic field strength — item 6-25, dimension `C·T⁻¹·L⁻¹` (unit A/m). -/
def magneticFieldStrength : DimensionedKind :=
  dimKind "magnetic field strength" EDim.magneticFieldStrength

/-! ## (G) Permeability, susceptibility, the magnetic dipole, the vector potential
(items 6-26 … 6-32)

The magnetic constant (6-26.1) and permeability (6-26.2) are H/m; relative permeability
(6-27) and magnetic susceptibility (6-28) are dimension one. Magnetic polarization (6-29)
shares the tesla with magnetic flux density. The magnetic dipole moment (6-30) is Wb·m;
coercivity (6-31) is A/m; the magnetic vector potential (6-32) is Wb/m. -/

/-- Magnetic constant (vacuum permeability) — item 6-26.1, dimension `M·L·C⁻²`
(unit H/m). -/
def magneticConstant : DimensionedKind :=
  dimKind "magnetic constant" EDim.permeability
/-- Permeability — item 6-26.2, dimension `M·L·C⁻²` (unit H/m). -/
def permeability : DimensionedKind := dimKind "permeability" EDim.permeability
/-- Relative permeability — item 6-27, dimension one (a ratio of permeabilities). -/
def relativePermeability : DimensionedKind :=
  dimKind "relative permeability" Dim.one
/-- Magnetic susceptibility — item 6-28, dimension one. -/
def magneticSusceptibility : DimensionedKind :=
  dimKind "magnetic susceptibility" Dim.one
/-- Magnetic polarization — item 6-29, dimension `M·T⁻¹·C⁻¹` (unit T; the same dimension
as magnetic flux density, a distinct kind). -/
def magneticPolarization : DimensionedKind :=
  dimKind "magnetic polarization" EDim.magneticFluxDensity
/-- Magnetic dipole moment — item 6-30, dimension `M·L³·T⁻¹·C⁻¹` (unit Wb·m). -/
def magneticDipoleMoment : DimensionedKind :=
  dimKind "magnetic dipole moment" EDim.magneticDipoleMoment
/-- Coercivity — item 6-31, dimension `C·T⁻¹·L⁻¹` (unit A/m). -/
def coercivity : DimensionedKind := dimKind "coercivity" EDim.magneticFieldStrength
/-- Magnetic vector potential — item 6-32, dimension `M·L·T⁻¹·C⁻¹` (unit Wb/m,
written J/(A·m)). -/
def magneticVectorPotential : DimensionedKind :=
  dimKind "magnetic vector potential" EDim.magneticVectorPotential

/-! ## (H) Electromagnetic energy density, the Poynting vector, wave speeds
(items 6-33 … 6-35.2)

Electromagnetic energy density (6-33) is J/m³; the Poynting vector (6-34) is W/m². The
phase speed of electromagnetic waves (6-35.1) and the speed of light in vacuum (6-35.2)
are both speeds, `L·T⁻¹` — drawing on ISO 80000-3. -/

/-- Electromagnetic energy density — item 6-33, dimension `M·L⁻¹·T⁻²` (unit J/m³). -/
def electromagneticEnergyDensity : DimensionedKind :=
  dimKind "electromagnetic energy density" EDim.energyDensity
/-- Poynting vector — item 6-34, dimension `M·T⁻³` (unit W/m²). -/
def poyntingVector : DimensionedKind := dimKind "Poynting vector" EDim.poyntingVector
/-- Phase speed of electromagnetic waves — item 6-35.1, dimension `L·T⁻¹` (unit m/s). -/
def phaseSpeed : DimensionedKind :=
  dimKind "phase speed of electromagnetic waves" Dim.speed
/-- Speed of light in vacuum — item 6-35.2, dimension `L·T⁻¹` (unit m/s; a fundamental
constant). -/
def speedOfLight : DimensionedKind := dimKind "speed of light in vacuum" Dim.speed

/-! ## (I) Magnetic potentials and the magnetic circuit (items 6-36 … 6-41.2)

Source voltage (6-36) is a voltage, `V`. The magnetic potential, magnetic tension, and
magnetomotive force (6-37.1 … 6-37.3) are all `A`. The number of turns (6-38) is
dimension one. Reluctance (6-39) is H⁻¹; permeance (6-40) and the inductances (6-41.1,
6-41.2) are the henry, `H`. -/

/-- Source voltage (the deprecated "electromotive force") — item 6-36, dimension
`M·L²·T⁻²·C⁻¹` (unit V; a voltage). -/
def sourceVoltage : DimensionedKind := dimKind "source voltage" EDim.voltage
/-- Magnetic potential (magnetic scalar potential) — item 6-37.1, dimension `C·T⁻¹`
(unit A). -/
def magneticPotential : DimensionedKind := dimKind "magnetic potential" Dim.current
/-- Magnetic tension — item 6-37.2, dimension `C·T⁻¹` (unit A). -/
def magneticTension : DimensionedKind := dimKind "magnetic tension" Dim.current
/-- Magnetomotive force — item 6-37.3, dimension `C·T⁻¹` (unit A). -/
def magnetomotiveForce : DimensionedKind := dimKind "magnetomotive force" Dim.current
/-- Number of turns in a winding — item 6-38, dimension one. -/
def numberOfTurns : DimensionedKind := dimKind "number of turns in a winding" Dim.one
/-- Reluctance — item 6-39, dimension `M⁻¹·L⁻²·C²` (unit H⁻¹). The
reciprocal-of-permeance remark is in `Part6.DefiningRelations`. -/
def reluctance : DimensionedKind := dimKind "reluctance" EDim.reluctance
/-- Permeance — item 6-40, dimension `M·L²·C⁻²` (unit H, the henry). -/
def permeance : DimensionedKind := dimKind "permeance" EDim.inductance
/-- Inductance (self-inductance) — item 6-41.1, dimension `M·L²·C⁻²` (unit H). -/
def inductance : DimensionedKind := dimKind "inductance" EDim.inductance
/-- Mutual inductance — item 6-41.2, dimension `M·L²·C⁻²` (unit H). -/
def mutualInductance : DimensionedKind := dimKind "mutual inductance" EDim.inductance

/-! ## (J) Coupling, conductivity, resistivity, power (items 6-42.1 … 6-45)

The coupling factor (6-42.1) and leakage factor (6-42.2) are dimension one. Conductivity
(6-43) is S/m; resistivity (6-44) is Ω·m. Power (6-45) is the watt, `W` — the genus of
the AC power family (section (M)). -/

/-- Coupling factor — item 6-42.1, dimension one. -/
def couplingFactor : DimensionedKind := dimKind "coupling factor" Dim.one
/-- Leakage factor — item 6-42.2, dimension one. -/
def leakageFactor : DimensionedKind := dimKind "leakage factor" Dim.one
/-- Conductivity — item 6-43, dimension `M⁻¹·L⁻³·T·C²` (unit S/m). The
reciprocal-of-resistivity remark is in `Part6.DefiningRelations`. -/
def conductivity : DimensionedKind := dimKind "conductivity" EDim.conductivity
/-- Resistivity — item 6-44, dimension `M·L³·T⁻¹·C⁻²` (unit Ω·m). -/
def resistivity : DimensionedKind := dimKind "resistivity" EDim.resistivity
/-- Power `<electromagnetism>` — item 6-45, dimension `M·L²·T⁻³` (unit W). The broad
genus of the AC power family. The voltage-times-current remark is in
`Part6.DefiningRelations`. -/
def power : DimensionedKind := dimKind "power" EDim.power

/-! ## (K) Resistance, conductance, phase, phasors (items 6-46 … 6-50)

Resistance (6-46) is the ohm, `Ω`; conductance (6-47) is the siemens, `S`. The phase
difference (6-48) is an angle, `rad`. The electric current phasor (6-49) is `A` and the
voltage phasor (6-50) is `V`. -/

/-- Resistance — item 6-46, dimension `M·L²·T⁻¹·C⁻²` (unit Ω, the ohm). The
voltage/current remark (Ohm's law) is formalized in `Part6.DefiningRelations`. -/
def resistance : DimensionedKind := dimKind "resistance" EDim.resistance
/-- Conductance — item 6-47, dimension `M⁻¹·L⁻²·T·C²` (unit S, the siemens). The
reciprocal-of-resistance remark is in `Part6.DefiningRelations`. -/
def conductance : DimensionedKind := dimKind "conductance" EDim.conductance
/-- Phase difference — item 6-48, dimension one (unit rad, an angle). -/
def phaseDifference : DimensionedKind := dimKind "phase difference" Dim.one
/-- Electric current phasor — item 6-49, dimension `C·T⁻¹` (unit A; a complex current). -/
def electricCurrentPhasor : DimensionedKind :=
  dimKind "electric current phasor" Dim.current
/-- Voltage phasor — item 6-50, dimension `M·L²·T⁻²·C⁻¹` (unit V; a complex voltage). -/
def voltagePhasor : DimensionedKind := dimKind "voltage phasor" EDim.voltage

/-! ## (L) Impedance and admittance (items 6-51.1 … 6-52.5)

Impedance and its parts (6-51.1 … 6-51.5) are all the ohm, `Ω` (the impedance of vacuum
is also written V/A). Admittance and its parts (6-52.1 … 6-52.5) are all the siemens,
`S` (the admittance of vacuum is also written A/V). -/

/-- Impedance (complex impedance) — item 6-51.1, dimension `M·L²·T⁻¹·C⁻²` (unit Ω). -/
def impedance : DimensionedKind := dimKind "impedance" EDim.resistance
/-- Impedance of vacuum (wave impedance in vacuum) — item 6-51.2, dimension
`M·L²·T⁻¹·C⁻²` (unit V/A; the same dimension as the ohm). -/
def impedanceOfVacuum : DimensionedKind := dimKind "impedance of vacuum" EDim.resistance
/-- Resistance (real part of impedance) — item 6-51.3, dimension `M·L²·T⁻¹·C⁻²`
(unit Ω). -/
def resistanceAC : DimensionedKind := dimKind "resistance" EDim.resistance
/-- Reactance (imaginary part of impedance) — item 6-51.4, dimension `M·L²·T⁻¹·C⁻²`
(unit Ω; the same dimension as resistance, a distinct kind). -/
def reactance : DimensionedKind := dimKind "reactance" EDim.resistance
/-- Apparent impedance — item 6-51.5, dimension `M·L²·T⁻¹·C⁻²` (unit Ω). -/
def apparentImpedance : DimensionedKind := dimKind "apparent impedance" EDim.resistance
/-- Admittance (complex admittance) — item 6-52.1, dimension `M⁻¹·L⁻²·T·C²` (unit S). -/
def admittance : DimensionedKind := dimKind "admittance" EDim.conductance
/-- Admittance of vacuum — item 6-52.2, dimension `M⁻¹·L⁻²·T·C²` (unit A/V). -/
def admittanceOfVacuum : DimensionedKind :=
  dimKind "admittance of vacuum" EDim.conductance
/-- Conductance (real part of admittance) — item 6-52.3, dimension `M⁻¹·L⁻²·T·C²`
(unit S). -/
def conductanceAC : DimensionedKind := dimKind "conductance" EDim.conductance
/-- Susceptance (imaginary part of admittance) — item 6-52.4, dimension `M⁻¹·L⁻²·T·C²`
(unit S). -/
def susceptance : DimensionedKind := dimKind "susceptance" EDim.conductance
/-- Apparent admittance — item 6-52.5, dimension `M⁻¹·L⁻²·T·C²` (unit S). -/
def apparentAdmittance : DimensionedKind := dimKind "apparent admittance" EDim.conductance

/-! ## (M) Quality, loss, and the AC power family (items 6-53 … 6-62)

The quality factor (6-53), loss factor (6-54), and power factor (6-58) are dimension
one; the loss angle (6-55) is an angle, `rad`. The AC power quantities — active power
(6-56), apparent power (6-57), complex power (6-59), reactive power (6-60), and
non-active power (6-61) — are *all* dimension `M·L²·T⁻³`, yet carry three different
coherent-unit strings (`W`, `VA`, `var`). Active energy (6-62) is the joule, `J`. -/

/-- Quality factor — item 6-53, dimension one. -/
def qualityFactor : DimensionedKind := dimKind "quality factor" Dim.one
/-- Loss factor (dissipation factor) — item 6-54, dimension one. -/
def lossFactor : DimensionedKind := dimKind "loss factor" Dim.one
/-- Loss angle — item 6-55, dimension one (unit rad, an angle). -/
def lossAngle : DimensionedKind := dimKind "loss angle" Dim.one

/-! ### Examination principles for the AC power species

The examination principles (Dybkær §7.5) that individuate the AC power quantities. Each
`id` is this work's own terse descriptor of the *defining construction* (which component
of the periodic process the quantity isolates) that distinguishes the species — not the
standard's normative definition. -/

namespace PowerPrinciple
/-- Active power — the time-averaged real (resistive) component of the instantaneous
power. -/
def timeAveragedReal : ExaminationPrinciple := { id := "time-averaged-real" }
/-- Apparent power — the product of the RMS voltage and the RMS current. -/
def rmsProduct : ExaminationPrinciple := { id := "rms-product" }
/-- Complex power — the complex sum `P + jQ` of active and reactive power. -/
def complexPQ : ExaminationPrinciple := { id := "complex-P-jQ" }
/-- Reactive power — the imaginary component of the complex power. -/
def reactiveImaginary : ExaminationPrinciple := { id := "reactive-imaginary" }
/-- Non-active power — the residual `√(S² − P²)` of apparent over active power. -/
def nonActiveResidual : ExaminationPrinciple := { id := "non-active-residual" }
end PowerPrinciple

/-- An AC power species: dimension `M·L²·T⁻³`, ratio-scale, individuated by its defining
construction (examination principle). -/
def powerSpecies (id : String) (p : ExaminationPrinciple) : DimensionedKind :=
  { kind := { id := id, scale := .ratio, examPrinciple := some p.id }, dim := EDim.power }

/-- Active power — item 6-56, a power species (the time-averaged real component, unit W). -/
def activePower : DimensionedKind :=
  powerSpecies "active power" PowerPrinciple.timeAveragedReal
/-- Apparent power — item 6-57, a power species (RMS voltage times RMS current, unit VA). -/
def apparentPower : DimensionedKind :=
  powerSpecies "apparent power" PowerPrinciple.rmsProduct
/-- Power factor — item 6-58, dimension one (active power over apparent power). The remark
is formalized in `Part6.DefiningRelations`. -/
def powerFactor : DimensionedKind := dimKind "power factor" Dim.one
/-- Complex power — item 6-59, a power species (`P + jQ`, unit VA). -/
def complexPower : DimensionedKind :=
  powerSpecies "complex power" PowerPrinciple.complexPQ
/-- Reactive power — item 6-60, a power species (the imaginary part of complex power,
unit var). -/
def reactivePower : DimensionedKind :=
  powerSpecies "reactive power" PowerPrinciple.reactiveImaginary
/-- Non-active power — item 6-61, a power species (`√(S² − P²)`, unit VA). -/
def nonActivePower : DimensionedKind :=
  powerSpecies "non-active power" PowerPrinciple.nonActiveResidual
/-- Active energy — item 6-62, dimension `M·L²·T⁻²` (unit J; the time-integral of
active power). -/
def activeEnergy : DimensionedKind := dimKind "active energy" EDim.energy

/-! ## The catalogue (every kind, with its source as data) -/

/-- Electric current and charge. -/
def electricCurrentCK : CataloguedKind := cat "6-1" "I" "A" electricCurrent
def electricChargeCK : CataloguedKind := cat "6-2.1" "Q" "C" electricCharge
def elementaryChargeCK : CataloguedKind := cat "6-2.2" "e" "C" elementaryCharge

/-- Charge and current distributions; the dipole and polarization. -/
def electricChargeDensityCK : CataloguedKind :=
  cat "6-3" "ρ" "C/m³" electricChargeDensity
def surfaceChargeDensityCK : CataloguedKind :=
  cat "6-4" "σ" "C/m²" surfaceChargeDensity
def linearChargeDensityCK : CataloguedKind :=
  cat "6-5" "τ" "C/m" linearChargeDensity
def electricDipoleMomentCK : CataloguedKind :=
  cat "6-6" "p" "C·m" electricDipoleMoment
def electricPolarizationCK : CataloguedKind :=
  cat "6-7" "P" "C/m²" electricPolarization
def electricCurrentDensityCK : CataloguedKind :=
  cat "6-8" "J" "A/m²" electricCurrentDensity
def linearCurrentDensityCK : CataloguedKind :=
  cat "6-9" "J_S" "A/m" linearCurrentDensity

/-- The electric field, potential, and voltage. -/
def electricFieldStrengthCK : CataloguedKind :=
  cat "6-10" "E" "V/m" electricFieldStrength
def electricPotentialCK : CataloguedKind := cat "6-11.1" "V" "V" electricPotential
def electricPotentialDifferenceCK : CataloguedKind :=
  cat "6-11.2" "V_ab" "V" electricPotentialDifference
def voltageCK : CataloguedKind := cat "6-11.3" "U" "V" voltage
def inducedVoltageCK : CataloguedKind := cat "6-11.4" "U_i" "V" inducedVoltage

/-- Electric flux density, capacitance, permittivity. -/
def electricFluxDensityCK : CataloguedKind :=
  cat "6-12" "D" "C/m²" electricFluxDensity
def capacitanceCK : CataloguedKind := cat "6-13" "C" "F" capacitance
def electricConstantCK : CataloguedKind := cat "6-14.1" "ε_0" "F/m" electricConstant
def permittivityCK : CataloguedKind := cat "6-14.2" "ε" "F/m" permittivity
def relativePermittivityCK : CataloguedKind :=
  cat "6-15" "ε_r" "1" relativePermittivity
def electricSusceptibilityCK : CataloguedKind :=
  cat "6-16" "χ" "1" electricSusceptibility
def electricFluxCK : CataloguedKind := cat "6-17" "Ψ" "C" electricFlux

/-- Displacement and total currents. -/
def displacementCurrentDensityCK : CataloguedKind :=
  cat "6-18" "J_D" "A/m²" displacementCurrentDensity
def displacementCurrentCK : CataloguedKind :=
  cat "6-19.1" "I_D" "A" displacementCurrent
def totalCurrentCK : CataloguedKind := cat "6-19.2" "I_tot" "A" totalCurrent
def totalCurrentDensityCK : CataloguedKind :=
  cat "6-20" "J_tot" "A/m²" totalCurrentDensity

/-- The magnetic field — flux density, flux, moment, magnetization. -/
def magneticFluxDensityCK : CataloguedKind :=
  cat "6-21" "B" "T" magneticFluxDensity
def magneticFluxCK : CataloguedKind := cat "6-22.1" "Φ" "Wb" magneticFlux
def protofluxCK : CataloguedKind := cat "6-22.2" "Ψ_p" "Wb" protoflux
def linkedMagneticFluxCK : CataloguedKind :=
  cat "6-22.3" "Φ_l" "Wb" linkedMagneticFlux
def totalMagneticFluxCK : CataloguedKind :=
  cat "6-22.4" "Ψ" "Wb" totalMagneticFlux
def magneticMomentCK : CataloguedKind := cat "6-23" "m" "A·m²" magneticMoment
def magnetizationCK : CataloguedKind := cat "6-24" "M" "A/m" magnetization
def magneticFieldStrengthCK : CataloguedKind :=
  cat "6-25" "H" "A/m" magneticFieldStrength

/-- Permeability, susceptibility, the magnetic dipole, the vector potential. -/
def magneticConstantCK : CataloguedKind := cat "6-26.1" "μ_0" "H/m" magneticConstant
def permeabilityCK : CataloguedKind := cat "6-26.2" "μ" "H/m" permeability
def relativePermeabilityCK : CataloguedKind :=
  cat "6-27" "μ_r" "1" relativePermeability
def magneticSusceptibilityCK : CataloguedKind :=
  cat "6-28" "κ" "1" magneticSusceptibility
def magneticPolarizationCK : CataloguedKind :=
  cat "6-29" "J_m" "T" magneticPolarization
def magneticDipoleMomentCK : CataloguedKind :=
  cat "6-30" "j_m" "Wb·m" magneticDipoleMoment
def coercivityCK : CataloguedKind := cat "6-31" "H_c" "A/m" coercivity
def magneticVectorPotentialCK : CataloguedKind :=
  cat "6-32" "A" "Wb/m" magneticVectorPotential

/-- Electromagnetic energy density, the Poynting vector, wave speeds. -/
def electromagneticEnergyDensityCK : CataloguedKind :=
  cat "6-33" "w" "J/m³" electromagneticEnergyDensity
def poyntingVectorCK : CataloguedKind := cat "6-34" "S" "W/m²" poyntingVector
def phaseSpeedCK : CataloguedKind := cat "6-35.1" "c" "m/s" phaseSpeed
def speedOfLightCK : CataloguedKind := cat "6-35.2" "c_0" "m/s" speedOfLight

/-- Magnetic potentials and the magnetic circuit. -/
def sourceVoltageCK : CataloguedKind := cat "6-36" "U_s" "V" sourceVoltage
def magneticPotentialCK : CataloguedKind := cat "6-37.1" "V_m" "A" magneticPotential
def magneticTensionCK : CataloguedKind := cat "6-37.2" "U_m" "A" magneticTension
def magnetomotiveForceCK : CataloguedKind := cat "6-37.3" "F_m" "A" magnetomotiveForce
def numberOfTurnsCK : CataloguedKind := cat "6-38" "N" "1" numberOfTurns
def reluctanceCK : CataloguedKind := cat "6-39" "R_m" "H⁻¹" reluctance
def permeanceCK : CataloguedKind := cat "6-40" "Λ" "H" permeance
def inductanceCK : CataloguedKind := cat "6-41.1" "L" "H" inductance
def mutualInductanceCK : CataloguedKind := cat "6-41.2" "L_mn" "H" mutualInductance

/-- Coupling, conductivity, resistivity, power. -/
def couplingFactorCK : CataloguedKind := cat "6-42.1" "k" "1" couplingFactor
def leakageFactorCK : CataloguedKind := cat "6-42.2" "σ" "1" leakageFactor
def conductivityCK : CataloguedKind := cat "6-43" "σ" "S/m" conductivity
def resistivityCK : CataloguedKind := cat "6-44" "ρ" "Ω·m" resistivity
def powerCK : CataloguedKind := cat "6-45" "P" "W" power

/-- Resistance, conductance, phase, phasors. -/
def resistanceCK : CataloguedKind := cat "6-46" "R" "Ω" resistance
def conductanceCK : CataloguedKind := cat "6-47" "G" "S" conductance
def phaseDifferenceCK : CataloguedKind := cat "6-48" "φ" "rad" phaseDifference
def electricCurrentPhasorCK : CataloguedKind :=
  cat "6-49" "I" "A" electricCurrentPhasor
def voltagePhasorCK : CataloguedKind := cat "6-50" "U" "V" voltagePhasor

/-- Impedance and admittance. -/
def impedanceCK : CataloguedKind := cat "6-51.1" "Z" "Ω" impedance
def impedanceOfVacuumCK : CataloguedKind :=
  cat "6-51.2" "Z_0" "V/A" impedanceOfVacuum
def resistanceACCK : CataloguedKind := cat "6-51.3" "R" "Ω" resistanceAC
def reactanceCK : CataloguedKind := cat "6-51.4" "X" "Ω" reactance
def apparentImpedanceCK : CataloguedKind := cat "6-51.5" "Z" "Ω" apparentImpedance
def admittanceCK : CataloguedKind := cat "6-52.1" "Y" "S" admittance
def admittanceOfVacuumCK : CataloguedKind :=
  cat "6-52.2" "Y_0" "A/V" admittanceOfVacuum
def conductanceACCK : CataloguedKind := cat "6-52.3" "G" "S" conductanceAC
def susceptanceCK : CataloguedKind := cat "6-52.4" "B" "S" susceptance
def apparentAdmittanceCK : CataloguedKind := cat "6-52.5" "Y" "S" apparentAdmittance

/-- Quality, loss, and the AC power family. -/
def qualityFactorCK : CataloguedKind := cat "6-53" "Q" "1" qualityFactor
def lossFactorCK : CataloguedKind := cat "6-54" "d" "1" lossFactor
def lossAngleCK : CataloguedKind := cat "6-55" "δ" "rad" lossAngle
def activePowerCK : CataloguedKind := cat "6-56" "P" "W" activePower
def apparentPowerCK : CataloguedKind := cat "6-57" "S" "VA" apparentPower
def powerFactorCK : CataloguedKind := cat "6-58" "λ" "1" powerFactor
def complexPowerCK : CataloguedKind := cat "6-59" "S" "VA" complexPower
def reactivePowerCK : CataloguedKind := cat "6-60" "Q" "var" reactivePower
def nonActivePowerCK : CataloguedKind := cat "6-61" "Q'" "VA" nonActivePower
def activeEnergyCK : CataloguedKind := cat "6-62" "W" "J" activeEnergy

/-- The full IEC 80000-6 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [electricCurrentCK, electricChargeCK, elementaryChargeCK,
   electricChargeDensityCK, surfaceChargeDensityCK, linearChargeDensityCK,
   electricDipoleMomentCK, electricPolarizationCK, electricCurrentDensityCK,
   linearCurrentDensityCK,
   electricFieldStrengthCK, electricPotentialCK, electricPotentialDifferenceCK,
   voltageCK, inducedVoltageCK,
   electricFluxDensityCK, capacitanceCK, electricConstantCK, permittivityCK,
   relativePermittivityCK, electricSusceptibilityCK, electricFluxCK,
   displacementCurrentDensityCK, displacementCurrentCK, totalCurrentCK,
   totalCurrentDensityCK,
   magneticFluxDensityCK, magneticFluxCK, protofluxCK, linkedMagneticFluxCK,
   totalMagneticFluxCK, magneticMomentCK, magnetizationCK, magneticFieldStrengthCK,
   magneticConstantCK, permeabilityCK, relativePermeabilityCK, magneticSusceptibilityCK,
   magneticPolarizationCK, magneticDipoleMomentCK, coercivityCK, magneticVectorPotentialCK,
   electromagneticEnergyDensityCK, poyntingVectorCK, phaseSpeedCK, speedOfLightCK,
   sourceVoltageCK, magneticPotentialCK, magneticTensionCK, magnetomotiveForceCK,
   numberOfTurnsCK, reluctanceCK, permeanceCK, inductanceCK, mutualInductanceCK,
   couplingFactorCK, leakageFactorCK, conductivityCK, resistivityCK, powerCK,
   resistanceCK, conductanceCK, phaseDifferenceCK, electricCurrentPhasorCK, voltagePhasorCK,
   impedanceCK, impedanceOfVacuumCK, resistanceACCK, reactanceCK, apparentImpedanceCK,
   admittanceCK, admittanceOfVacuumCK, conductanceACCK, susceptanceCK, apparentAdmittanceCK,
   qualityFactorCK, lossFactorCK, lossAngleCK, activePowerCK, apparentPowerCK,
   powerFactorCK, complexPowerCK, reactivePowerCK, nonActivePowerCK, activeEnergyCK]

/-! ## (N) Units — a few coherent SI units of these kinds

Each unit references its kind, so an ampere and a volt are not commensurable; the volt
of electric potential is not commensurable with the volt of electric potential
difference (same string, same dimension, *different scale*); and the watt of active
power, the var of reactive power, and the volt-ampere of apparent power are pairwise
not commensurable *though all three carry the dimension `M·L²·T⁻³`* — all type-level
facts, not runtime checks. -/

/-- The ampere, the SI unit of electric current (item 6-1). -/
def ampere : MetrologicalUnit := electricCurrent.kind.unit "A"
/-- The coulomb, the SI unit of electric charge (item 6-2.1). -/
def coulomb : MetrologicalUnit := electricCharge.kind.unit "C"
/-- The volt **of electric potential** (item 6-11.1) — an *interval-scale* unit. -/
def voltPotential : MetrologicalUnit := electricPotential.kind.unit "V"
/-- The volt **of electric potential difference** (item 6-11.2) — *also* "V" and *also*
`M·L²·T⁻²·C⁻¹`, but a ratio-scale unit of a different kind. -/
def voltDifference : MetrologicalUnit := electricPotentialDifference.kind.unit "V"
/-- The ohm, the SI unit of resistance (item 6-46). -/
def ohm : MetrologicalUnit := resistance.kind.unit "Ω"
/-- The watt **of active power** (item 6-56) — dimension `M·L²·T⁻³`. -/
def wattActive : MetrologicalUnit := activePower.kind.unit "W"
/-- The var **of reactive power** (item 6-60) — *also* `M·L²·T⁻³`, but a unit of reactive
power, not active power. -/
def varReactive : MetrologicalUnit := reactivePower.kind.unit "var"
/-- The volt-ampere **of apparent power** (item 6-57) — *also* `M·L²·T⁻³`, but a unit of
apparent power. -/
def voltAmpere : MetrologicalUnit := apparentPower.kind.unit "VA"

/-! ## (O) Checked dimensional facts (the dimensional algebra) -/

/-- Electric current carries charge-exponent `1` and time-exponent `-1` — the ampere as
coulomb per second (item 6-1). -/
theorem electricCurrent_dim_charge : electricCurrent.dim.charge = 1 := by
  norm_num [electricCurrent, dimKind, Dim.current, Dimension.div_charge, Dimension.C𝓭,
    Dimension.T𝓭_charge]

/-- Electric current is `C·T⁻¹`: its time-exponent is `-1` (item 6-1). -/
theorem electricCurrent_dim_time : electricCurrent.dim.time = -1 := by
  norm_num [electricCurrent, dimKind, Dim.current, Dimension.div_time, Dimension.C𝓭,
    Dimension.T𝓭_time]

/-- Electric charge carries charge-exponent `1` — the base generator `C` (item 6-2.1). -/
theorem electricCharge_dim_charge : electricCharge.dim.charge = 1 := rfl

/-- Voltage is `M·L²·T⁻²·C⁻¹`: its charge-exponent is `-1` — energy per charge (item
6-11.3). -/
theorem voltage_dim_charge : voltage.dim.charge = -1 := by
  norm_num [voltage, dimKind, EDim.voltage, EDim.energy, Dim.charge, Dim.mass, Dim.area,
    Dim.time, Dimension.div_charge, Dimension.charge_mul, Dimension.L𝓭_charge,
    Dimension.T𝓭_charge, Dimension.M𝓭, Dimension.C𝓭]

/-- **Capacitance is `C²·M⁻¹·L⁻²·T²`: its charge-exponent is `2`** — the farad carries
the charge generator squared (item 6-13). -/
theorem capacitance_dim_charge : capacitance.dim.charge = 2 := by
  norm_num [capacitance, dimKind, EDim.capacitance, EDim.energy, Dim.charge, Dim.mass,
    Dim.area, Dim.time, Dimension.div_charge, Dimension.charge_mul, Dimension.L𝓭_charge,
    Dimension.T𝓭_charge, Dimension.M𝓭, Dimension.C𝓭]

/-- Resistance is `M·L²·T⁻¹·C⁻²`: its charge-exponent is `-2` — the ohm (item 6-46). -/
theorem resistance_dim_charge : resistance.dim.charge = -2 := by
  norm_num [resistance, dimKind, EDim.resistance, EDim.voltage, EDim.energy, Dim.current,
    Dim.charge, Dim.mass, Dim.area, Dim.time, Dimension.div_charge, Dimension.charge_mul,
    Dimension.inv_charge, Dimension.L𝓭_charge, Dimension.T𝓭_charge, Dimension.M𝓭,
    Dimension.C𝓭]

/-- Magnetic flux is `M·L²·T⁻¹·C⁻¹`: its charge-exponent is `-1` — the weber (item
6-22.1). -/
theorem magneticFlux_dim_charge : magneticFlux.dim.charge = -1 := by
  norm_num [magneticFlux, dimKind, EDim.magneticFlux, EDim.voltage, EDim.energy, Dim.charge,
    Dim.mass, Dim.area, Dim.time, Dimension.div_charge, Dimension.charge_mul,
    Dimension.L𝓭_charge, Dimension.T𝓭_charge, Dimension.M𝓭, Dimension.C𝓭]

/-! ## (P) Unit well-formedness, scale, and (in)commensurability -/

/-- The ampere is a well-formed unit (electric current is ratio-scale). -/
theorem ampere_wellFormed : ampere.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- The ohm is a well-formed unit of resistance. -/
theorem ohm_wellFormed : ohm.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- **The volt of electric potential is a well-formed unit, though electric potential is
only interval-scale.** As with the degree Celsius in Part 5, a kind bears a metrological
unit from the *differential* (interval) scale upward (Dybkær §13.3.4) — so the volt is a
legitimate unit of the gauge-dependent electric potential even though `×`,`÷` are
undefined on potentials. -/
theorem voltPotential_wellFormed : voltPotential.WellFormed := by
  unfold MetrologicalUnit.WellFormed KindOfProperty.BearsUnit voltPotential
    electricPotential KindOfProperty.unit
  trivial

/-- The ampere and the volt are **not** commensurable — electric current and electric
potential are distinct kinds (a type-level fact). -/
theorem ampere_voltPotential_not_commensurable : ¬ ampere.Commensurable voltPotential := by
  unfold MetrologicalUnit.Commensurable ampere voltPotential electricCurrent
    electricPotential dimKind KindOfProperty.unit
  decide

/-- **The volt of electric potential is not the volt of electric potential difference,
though both are "V" and both `M·L²·T⁻²·C⁻¹`.** They carry the same symbol and the same
dimension, yet are not commensurable, because their kinds differ in *scale* (interval vs
ratio) — the gauge-dependent potential and the genuine difference are different kinds of
quantity. -/
theorem voltPotential_voltDifference_not_commensurable :
    ¬ voltPotential.Commensurable voltDifference := by
  unfold MetrologicalUnit.Commensurable voltPotential voltDifference electricPotential
    electricPotentialDifference dimKind KindOfProperty.unit
  decide

/-- **The watt of active power and the var of reactive power are not commensurable, though
both are `M·L²·T⁻³`.** The standard spends two different unit strings (`W`, `var`) on one
dimension precisely to keep the kinds apart — a sharper form of "a dimension does not
determine a kind" than Part 5's joule-per-kelvin, where even the unit string agreed. -/
theorem wattActive_varReactive_not_commensurable :
    ¬ wattActive.Commensurable varReactive := by
  unfold MetrologicalUnit.Commensurable wattActive varReactive activePower reactivePower
    powerSpecies KindOfProperty.unit
  decide

/-! ### The scale-type distinction (requirement R6)

Electric potential (6-11.1) and electric potential difference (6-11.2) have the *same*
dimension `M·L²·T⁻²·C⁻¹` and are *both* "potentials", yet are different kinds — separated
not by dimension and not by an examination principle, but by their **scale type**:
interval (the gauge-dependent potential) versus ratio (the genuine difference). -/

/-- Electric potential difference is **ratio-scale**: it admits `×`,`÷` (a genuine
difference of potentials). -/
theorem electricPotentialDifference_allowsRatio :
    ScaleType.AllowsRatio electricPotentialDifference.kind.scale := by
  unfold electricPotentialDifference dimKind ScaleType.AllowsRatio; trivial

/-- **Electric potential does *not* admit `×`,`÷`.** It is interval-scale (fixed only up
to an arbitrary additive reference — gauge freedom), so a ratio of electric potentials is
not a meaningful operation — the kind layer refuses it where dimension would not. -/
theorem electricPotential_not_allowsRatio :
    ¬ ScaleType.AllowsRatio electricPotential.kind.scale := by
  unfold electricPotential ScaleType.AllowsRatio; exact id

/-- **Electric potential and electric potential difference are distinct kinds — by scale,
not by dimension.** They share the dimension `M·L²·T⁻²·C⁻¹`, yet differ in scale type
(interval vs ratio), so they are different kinds of quantity. -/
theorem electricPotential_ne_electricPotentialDifference :
    electricPotential.kind ≠ electricPotentialDifference.kind := by
  unfold electricPotential electricPotentialDifference dimKind; decide

/-! ## (Q) The power family as a specialization lattice (requirement R2)

The direct-parent edges of the AC power family, mirroring the standard's own
definitions: active, reactive, apparent, complex, and non-active power are each a
*species* of power (item 6-45), individuated by which component of the periodic process
the quantity isolates. Specialization is the reflexive-transitive closure of these
edges. -/

/-- This application's system of power quantities — the direct-parent edges among the AC
power quantities of the power family (item 6-45). -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  /-- Active power is a kind of power (item 6-56 via power). -/
  | activePower_power : Edge activePower.kind power.kind
  /-- Reactive power is a kind of power (item 6-60 via power). -/
  | reactivePower_power : Edge reactivePower.kind power.kind
  /-- Apparent power is a kind of power (item 6-57 via power). -/
  | apparentPower_power : Edge apparentPower.kind power.kind
  /-- Complex power is a kind of power (item 6-59 via power). -/
  | complexPower_power : Edge complexPower.kind power.kind
  /-- Non-active power is a kind of power (item 6-61 via power). -/
  | nonActivePower_power : Edge nonActivePower.kind power.kind

/-- Active power specializes power. -/
theorem activePower_specializes_power :
    Specializes Edge activePower.kind power.kind :=
  Specializes.of_edge Edge.activePower_power

/-- Each power species is **examined by** its declared defining construction. -/
theorem activePower_examinedBy :
    activePower.kind.examinedBy PowerPrinciple.timeAveragedReal := rfl

/-- **Active power and reactive power are distinct kinds — by defining construction, not
by fiat.** They have the same dimension `M·L²·T⁻³` and are both "powers", yet they are
different kinds *because they isolate different components of the periodic process* (the
time-averaged real part vs the imaginary part of the complex power), proved through
`distinct_of_examPrinciple` (§7.5) rather than by appealing to their `id` strings. This
is the AC-power analogue of width ≠ distance, static ≠ kinetic friction, and Helmholtz ≠
Gibbs energy. -/
theorem activePower_ne_reactivePower : activePower.kind ≠ reactivePower.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- Apparent power and complex power are distinct kinds, again by their differing defining
constructions (RMS product vs the complex sum `P + jQ`). -/
theorem apparentPower_ne_complexPower : apparentPower.kind ≠ complexPower.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- A power species is distinct from the general power kind: a species carries an
examination principle (its defining construction), the genus carries none. -/
theorem activePower_ne_power : activePower.kind ≠ power.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- **Mutual comparability is preserved.** Active and reactive power, though distinct
kinds, remain *mutually comparable* — they share the super-kind power, so combining them
(into the complex power) is possible but only via an explicit up-cast, never silently. -/
theorem activePower_reactivePower_comparable :
    MutuallyComparable Edge activePower.kind reactivePower.kind :=
  ⟨power.kind, Specializes.of_edge Edge.activePower_power,
    Specializes.of_edge Edge.reactivePower_power⟩

/-! ## (R) Dimension collisions — the kind classifies where the dimension cannot

Same-dimension/distinct-kind pairs drawn from the catalogue above. The {dimension
functor} `dim` identifies the members of each pair; the kind layer keeps them apart. -/

/-- Active power and reactive power share dimension `M·L²·T⁻³`. -/
theorem activePower_dim_eq_reactivePower_dim : activePower.dim = reactivePower.dim := rfl

/-- Resistance and reactance share dimension `M·L²·T⁻¹·C⁻²` (the ohm). -/
theorem resistance_dim_eq_reactance_dim : resistance.dim = reactance.dim := rfl

/-- **Resistance is not reactance, though both are `M·L²·T⁻¹·C⁻²`.** They are distinct
kinds despite sharing the ohm — the real and imaginary parts of an impedance, which the
kind layer keeps apart and the dimension cannot. -/
theorem resistance_ne_reactance : resistance.kind ≠ reactance.kind := by
  unfold resistance reactance dimKind; decide

/-- Relative permittivity and relative permeability share dimension one. -/
theorem relativePermittivity_dim_eq_relativePermeability_dim :
    relativePermittivity.dim = relativePermeability.dim := rfl

/-- Relative permittivity and relative permeability are distinct kinds (both dimension
one). -/
theorem relativePermittivity_ne_relativePermeability :
    relativePermittivity.kind ≠ relativePermeability.kind := by
  unfold relativePermittivity relativePermeability dimKind; decide

/-- **The power collision, on standard quantities.** There exist distinct IEC 80000-6
kinds with the same dimension `M·L²·T⁻³` — active power and reactive power witness it
(alongside apparent, complex, and non-active power). PhysLib's `Dimension`, and any
dimension-only type system, cannot separate them; the kind layer does — and so do the
units, which here even differ in string (`W` vs `var`). This is the electromagnetic
dimension-does-not-classify case, sharper than Part 5's joule-per-kelvin. -/
theorem iec80000_6_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨activePower, reactivePower, activePower_ne_reactivePower,
    activePower_dim_eq_reactivePower_dim⟩

/-- **The dimension-1 disambiguation, on standard quantities.** There exist distinct
IEC 80000-6 kinds with the same dimension one — relative permittivity and relative
permeability witness it (alongside the susceptibilities, the coupling and leakage
factors, and the quality, loss, and power factors). Dimension cannot separate them; the
kind layer does. -/
theorem iec80000_6_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨relativePermittivity, relativePermeability,
    relativePermittivity_ne_relativePermeability, rfl, rfl⟩

/-- **The scale disambiguation, on standard quantities.** There exist distinct
IEC 80000-6 kinds with the same dimension `M·L²·T⁻²·C⁻¹` that are separated by *scale
type* alone — electric potential (interval, gauge-dependent) and electric potential
difference (ratio) witness it. Neither the dimension nor an examination principle tells
them apart; the scale layer does. This is requirement R6 on the standard, the
electromagnetic counterpart of Part 5's thermodynamic/Celsius temperature. -/
theorem iec80000_6_scale_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
      a.kind.scale ≠ b.kind.scale :=
  ⟨electricPotential, electricPotentialDifference,
    electricPotential_ne_electricPotentialDifference, rfl, by decide⟩

end PropertyKindCalculus.Iso80000.Part6
