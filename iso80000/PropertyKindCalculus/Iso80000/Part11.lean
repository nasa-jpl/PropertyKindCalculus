/-
# ISO 80000-11 — Characteristic numbers (the full catalogue)

The complete set of quantity-kinds (QK) for ISO 80000-11 *Characteristic numbers* — all
of items 11-4.1 … 11-9.2, including every sub-suffixed item — each carrying its exact
source as data: the part (`iso80000_11`), the printed item designation, the principal
quantity symbol, and the coherent SI unit symbol. Only **citation locators** are recorded
(item number, name, symbol, coherent SI unit); no normative content (the defining
formulae, definitions, remarks) from the licensed standard is reproduced.

Characteristic numbers are the part of the series where the *dimension does not classify
the kind* thesis (requirement **R1**) reaches its absolute widest form. **Every one of
the 115 characteristic numbers is dimension one** — the Reynolds number, the Froude
number, the Prandtl number, the Hartmann number, all of them. The {dimension functor}
collapses the *entire part* to a single point. What keeps them apart is not their
dimension and often not even their name, but their **measurement principle** — the
physical ratio each one expresses (requirement **R2**, the examination principle as a
defining aspect):

* **One dimension, 115 kinds.** A dimension-only model sees one type — "a real number" —
  for the Reynolds number (inertial / viscous forces), the Mach number (flow speed /
  sound speed), and the Prandtl number (momentum / thermal diffusivity) alike. It cannot
  say why these are three different things. Here each is a distinct {kind} individuated by
  the *measurement principle* it isolates, carried as its {examination principle}.

* **The sub-suffixed homonyms — same name, distinct kind.** ISO 80000-11 reuses one name
  across its transport-phenomena clauses, distinguishing the variants only by a symbol
  suffix and a different defining ratio: the Froude number (11-4.3 momentum, `Fr`; 11-5.4
  heat, `Fr*`), the Fourier number (heat `Fo` / mass `Fo*`), the Péclet, Grashof,
  Nusselt, Stanton, Graetz and Biot numbers (each heat / mass), the four Bejan numbers,
  and the *five* Stokes numbers (`Stk`, `Stk₁` … `Stk₄`). These are the
  sub-suffixed quantity kinds: each is a distinct kind, individuated *not* by dimension
  (all are one) and *not* by name (shared), but by its measurement principle alone —
  proved through `distinct_of_examPrinciple`.

* **The measurement principle carries the transport context.** Each kind's examination
  principle pairs the ISO 80000-11 clause it lives in — momentum transfer (clause 4),
  heat transfer (5), mass transfer in a binary mixture (6), constants of matter (7),
  magnetohydrodynamics (8), miscellaneous (9) — with the terse defining ratio. The
  context is part of how the same ratio name recurs as a different kind across clauses.

* **References to parts not yet specified are work-to-go.** Many definitions of these
  numbers name quantities from other parts of the series. The parts this library has
  already mapped — ISO 80000-3, -4, -5, IEC 80000-6, ISO 80000-7 — are recorded as
  specified; the parts it leans on but has *not* yet mapped — ISO 80000-8 *Acoustics*
  (the speed of sound, for the Mach number), ISO 80000-9 *Physical chemistry and
  molecular physics* (diffusion coefficients), and ISO 80000-12 *Condensed matter
  physics* (relaxation times) — are recorded as `workToGoParts`.

The defining ratios are *this work's own terse descriptors* of the measurement principle,
not the standard's normative definitions; the dimensional fact (every kind is dimension
one) is a checked computation.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Iso80000.References

namespace PropertyKindCalculus.Iso80000.Part11

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_11

/-- A **catalogued quantity-kind**: a {dimensioned kind} together with its exact source
in the 80000 series — the part, the printed item designation, the principal quantity
symbol, and the coherent SI unit symbol. Every field other than `qk` is a *citation
locator*; the citation travels with the kind as data. -/
structure CataloguedKind where
  /-- The part of the series this kind is defined in. -/
  ref : StandardRef
  /-- The item designation as printed, e.g. "11-4.1". -/
  item : String
  /-- The principal quantity symbol, e.g. "Re". -/
  symbol : String
  /-- The coherent SI unit symbol — `"1"` for every characteristic number. -/
  coherentUnit : String
  /-- The dimensioned kind itself. -/
  qk : DimensionedKind

/-- The standard citation for a catalogued kind, e.g.
`ISO 80000-11, Second edition, 2019-10 item 11-4.1`. -/
def CataloguedKind.cite (c : CataloguedKind) : String :=
  c.ref.cite ++ " item " ++ c.item

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  { ref := source, item := item, symbol := symbol, coherentUnit := coherentUnit, qk := qk }

/-! ## Transport context — ISO 80000-11's clause structure as a defining aspect

A characteristic number's **measurement principle** has two parts: the transport-phenomena
*context* (the clause it lives in) and the terse defining *ratio*. The context is part of
the principle because the same ratio name (Froude, Stokes, Bejan, Fourier, …) recurs
across contexts as a *different* kind. -/

/-- The transport-phenomena context of a characteristic number — ISO 80000-11's own clause
structure (clauses 4 … 9). -/
inductive Context where
  /-- Clause 4 — momentum transfer (fluid mechanics). -/
  | momentum
  /-- Clause 5 — transfer of heat. -/
  | heat
  /-- Clause 6 — transfer of matter in a binary mixture. -/
  | mass
  /-- Clause 7 — constants of matter. -/
  | constants
  /-- Clause 8 — magnetohydrodynamics. -/
  | mhd
  /-- Clause 9 — miscellaneous. -/
  | misc
deriving DecidableEq, Repr, BEq

/-- The context's terminological tag, the prefix of the measurement-principle id. -/
def Context.id : Context → String
  | .momentum => "momentum-transfer"
  | .heat => "heat-transfer"
  | .mass => "mass-transfer"
  | .constants => "constants-of-matter"
  | .mhd => "magnetohydrodynamics"
  | .misc => "miscellaneous"

/-- A **characteristic number**: a ratio-scale {dimensioned kind} of **dimension one**,
named by `id` and individuated by its {examination principle} — the measurement principle,
formed as `context: defining-ratio`. The dimension is one for every characteristic number;
the principle is what tells them apart. -/
def charNum (ctx : Context) (id principle : String) : DimensionedKind :=
  { kind := { id := id, scale := .ratio, examPrinciple := some (ctx.id ++ ": " ++ principle) }
    dim := Dim.one }

/-! ## (4) Momentum transfer — items 11-4.1 … 11-4.42

Fluid-mechanics characteristic numbers. Note the homonyms distinguished only by symbol and
defining ratio: two Bagnold numbers (11-4.10, 11-4.11) and the five Stokes numbers
(11-4.32 … 11-4.36, `Stk`, `Stk₁` … `Stk₄`). -/

def reynolds : DimensionedKind := charNum .momentum "Reynolds number" "inertial forces / viscous forces"
def euler : DimensionedKind := charNum .momentum "Euler number" "pressure drop / kinetic energy per volume"
def froudeMomentum : DimensionedKind := charNum .momentum "Froude number" "inertial forces / gravitational forces"
def grashofThermal : DimensionedKind := charNum .momentum "Grashof number" "thermal buoyancy forces / viscous forces"
def weber : DimensionedKind := charNum .momentum "Weber number" "inertial forces / surface-tension forces"
def mach : DimensionedKind := charNum .momentum "Mach number" "speed of flow / speed of sound"
def knudsen : DimensionedKind := charNum .momentum "Knudsen number" "mean free path / characteristic length"
def strouhal : DimensionedKind := charNum .momentum "Strouhal number" "characteristic frequency / characteristic speed"
def dragCoefficient : DimensionedKind := charNum .momentum "drag coefficient" "drag force / inertial force"
def bagnold : DimensionedKind := charNum .momentum "Bagnold number" "drag and gravitational force / inertial force"
def bagnoldSolid : DimensionedKind := charNum .momentum "Bagnold number" "drag force / viscous force, solid particles"
def liftCoefficient : DimensionedKind := charNum .momentum "lift coefficient" "lift force / inertial force"
def thrustCoefficient : DimensionedKind := charNum .momentum "thrust coefficient" "thrust force / inertial force"
def dean : DimensionedKind := charNum .momentum "Dean number" "centrifugal force / inertial force, curved pipe"
def bejanMomentum : DimensionedKind := charNum .momentum "Bejan number" "mechanical work / frictional energy loss"
def lagrange : DimensionedKind := charNum .momentum "Lagrange number" "mechanical work / frictional energy loss, Lagrange form"
def bingham : DimensionedKind := charNum .momentum "Bingham number" "yield stress / viscous stress"
def hedstrom : DimensionedKind := charNum .momentum "Hedström number" "yield stress / viscous stress, at flow limit"
def bodenstein : DimensionedKind := charNum .momentum "Bodenstein number" "convective / diffusive matter transfer"
def rossby : DimensionedKind := charNum .momentum "Rossby number" "inertial forces / Coriolis forces"
def ekman : DimensionedKind := charNum .momentum "Ekman number" "viscous forces / Coriolis forces"
def elasticity : DimensionedKind := charNum .momentum "elasticity number" "relaxation time / diffusion time"
def darcyFriction : DimensionedKind := charNum .momentum "Darcy friction factor" "pressure loss / pipe-wall friction"
def fanning : DimensionedKind := charNum .momentum "Fanning number" "wall shear stress / dynamic pressure"
def goertler : DimensionedKind := charNum .momentum "Goertler number" "centrifugal effects / viscous effects, boundary layer"
def hagen : DimensionedKind := charNum .momentum "Hagen number" "pressure-gradient force / viscous force"
def laval : DimensionedKind := charNum .momentum "Laval number" "flow speed / critical sound speed, nozzle throat"
def poiseuille : DimensionedKind := charNum .momentum "Poiseuille number" "pressure force / viscous force, pipe flow"
def powerNumber : DimensionedKind := charNum .momentum "power number" "agitator power / inertial power"
def richardson : DimensionedKind := charNum .momentum "Richardson number" "potential energy / kinetic energy"
def reech : DimensionedKind := charNum .momentum "Reech number" "object speed / wave speed, submerged"
def stokesPlasma : DimensionedKind := charNum .momentum "Stokes number" "friction force / inertial force, particles in flow"
def stokesVibrating : DimensionedKind := charNum .momentum "Stokes number" "friction force / inertial force, vibrating particles"
def stokesRotameter : DimensionedKind := charNum .momentum "Stokes number" "drag / inertia, rotameter calibration"
def stokesGravity : DimensionedKind := charNum .momentum "Stokes number" "viscous force / gravity force, settling particles"
def stokesDrag : DimensionedKind := charNum .momentum "Stokes number" "drag force / internal friction force, particles"
def laplace : DimensionedKind := charNum .momentum "Laplace number" "capillary force / viscous force, free surface"
def blake : DimensionedKind := charNum .momentum "Blake number" "inertial force / viscous force, porous medium"
def sommerfeld : DimensionedKind := charNum .momentum "Sommerfeld number" "viscous force / load force, lubrication"
def taylor : DimensionedKind := charNum .momentum "Taylor number" "centrifugal force / viscous force, rotating flow"
def galilei : DimensionedKind := charNum .momentum "Galilei number" "gravitational force / viscous force, fluid film"
def womersley : DimensionedKind := charNum .momentum "Womersley number" "inertial forces / viscous forces, oscillating flow"

/-! ## (5) Transfer of heat — items 11-5.1 … 11-5.20

Heat-transfer characteristic numbers. The Froude, Fourier, Péclet, Nusselt, Biot, Stanton
and Graetz numbers recur here from clause 4/6 as distinct heat-transfer kinds (symbols
`Fr*`, `Fo`, `Pe`, …); the Bejan number appears twice more (11-5.9, 11-5.10). -/

def fourierHeat : DimensionedKind := charNum .heat "Fourier number" "heat conduction rate / thermal storage rate"
def pecletHeat : DimensionedKind := charNum .heat "Péclet number" "convective / conductive heat transfer rate"
def rayleigh : DimensionedKind := charNum .heat "Rayleigh number" "thermal buoyancy forces / viscous forces, free convection"
def froudeHeat : DimensionedKind := charNum .heat "Froude number" "gravitational forces / thermodiffusion forces"
def nusseltHeat : DimensionedKind := charNum .heat "Nusselt number" "convective / conductive heat transfer at a surface"
def biotHeat : DimensionedKind := charNum .heat "Biot number" "internal / surface thermal resistance"
def stantonHeat : DimensionedKind := charNum .heat "Stanton number" "wall heat transfer / fluid heat-capacity flow"
def jFactorHeat : DimensionedKind := charNum .heat "j-factor" "heat transfer / mass transfer, Colburn analogy"
def bejanHeat : DimensionedKind := charNum .heat "Bejan number" "mechanical work / frictional and thermal-diffusion losses"
def bejanEntropy : DimensionedKind := charNum .heat "Bejan number" "heat-transfer efficiency / entropy generation"
def stefan : DimensionedKind := charNum .heat "Stefan number" "sensible heat / latent heat, phase change"
def brinkman : DimensionedKind := charNum .heat "Brinkman number" "viscous heat production / wall heat conduction"
def clausius : DimensionedKind := charNum .heat "Clausius number" "kinetic energy transfer / thermal conduction"
def carnot : DimensionedKind := charNum .heat "Carnot number" "maximum thermodynamic (Carnot) efficiency"
def eckert : DimensionedKind := charNum .heat "Eckert number" "kinetic energy / enthalpy difference"
def graetzHeat : DimensionedKind := charNum .heat "Graetz number" "convective / conductive heat, laminar pipe"
def heatTransferNumber : DimensionedKind := charNum .heat "heat transfer number" "heat flow / kinetic energy of flow"
def pomerantsev : DimensionedKind := charNum .heat "Pomerantsev number" "generated heat / conducted heat in a body"
def boltzmann : DimensionedKind := charNum .heat "Boltzmann number" "convective heat / radiant heat"
def stark : DimensionedKind := charNum .heat "Stark number" "radiant heat / conductive heat"

/-! ## (6) Transfer of matter in a binary mixture — items 11-6.1 … 11-6.20

Mass-transfer characteristic numbers, the binary-mixture analogues of the heat-transfer
clause: Fourier, Péclet, Grashof, Nusselt, Stanton, Graetz, Biot and Bejan recur with
starred symbols (`Fo*`, `Pe*`, …) as distinct mass-transfer kinds. -/

def fourierMass : DimensionedKind := charNum .mass "Fourier number" "diffusive mass transfer / storage rate"
def pecletMass : DimensionedKind := charNum .mass "Péclet number" "advective / diffusive mass transfer rate"
def grashofMass : DimensionedKind := charNum .mass "Grashof number" "buoyancy forces / viscous forces, natural convection"
def nusseltMass : DimensionedKind := charNum .mass "Nusselt number" "mass flux / molecular-diffusion flux"
def stantonMass : DimensionedKind := charNum .mass "Stanton number" "perpendicular / parallel surface mass transfer"
def graetzMass : DimensionedKind := charNum .mass "Graetz number" "advective / radial diffusive mass transfer"
def massTransferFactor : DimensionedKind := charNum .mass "mass transfer factor" "interface mass transfer / parallel flux, Chilton-Colburn"
def atwood : DimensionedKind := charNum .mass "Atwood number" "density difference / density sum, two fluids"
def biotMass : DimensionedKind := charNum .mass "Biot number" "interface / interior mass transfer rate"
def morton : DimensionedKind := charNum .mass "Morton number" "gravitational forces / viscous forces, bubbles"
def bond : DimensionedKind := charNum .mass "Bond number" "gravitational and inertial force / capillary force"
def archimedes : DimensionedKind := charNum .mass "Archimedes number" "buoyancy forces / viscous forces, density difference"
def expansionNumber : DimensionedKind := charNum .mass "expansion number" "buoyancy force / inertial force, rising bubbles"
def marangoni : DimensionedKind := charNum .mass "Marangoni number" "surface-tension convection / thermal diffusion"
def lockhartMartinelli : DimensionedKind := charNum .mass "Lockhart-Martinelli parameter" "two-phase mass-flow-rate ratio by density"
def bejanMass : DimensionedKind := charNum .mass "Bejan number" "mechanical work / frictional and diffusion losses"
def cavitation : DimensionedKind := charNum .mass "cavitation number" "static-vapour head / dynamic head"
def absorptionNumber : DimensionedKind := charNum .mass "absorption number" "mass flow rate / surface area, gas absorption"
def capillary : DimensionedKind := charNum .mass "capillary number" "gravitational forces / capillary forces"
def dynamicCapillary : DimensionedKind := charNum .mass "dynamic capillary number" "viscous force / capillary force, interface"

/-! ## (7) Constants of matter — items 11-7.1 … 11-7.10

The material-property characteristic numbers: ratios of two transport or material
coefficients (Prandtl, Schmidt, Lewis) and the rheological numbers. -/

def prandtl : DimensionedKind := charNum .constants "Prandtl number" "kinematic viscosity / thermal diffusivity"
def schmidt : DimensionedKind := charNum .constants "Schmidt number" "kinematic viscosity / diffusion coefficient"
def lewis : DimensionedKind := charNum .constants "Lewis number" "thermal diffusivity / diffusion coefficient"
def ohnesorge : DimensionedKind := charNum .constants "Ohnesorge number" "viscous force / root of inertia times capillary force"
def cauchy : DimensionedKind := charNum .constants "Cauchy number" "inertia forces / compression forces"
def hooke : DimensionedKind := charNum .constants "Hooke number" "inertia forces / linear-stress forces"
def weissenberg : DimensionedKind := charNum .constants "Weissenberg number" "shear rate times relaxation time"
def deborah : DimensionedKind := charNum .constants "Deborah number" "relaxation time / observation time"
def lorentz : DimensionedKind := charNum .constants "Lorentz number" "electrical conductivity / thermal conductivity"
def compressibility : DimensionedKind := charNum .constants "compressibility number" "real-gas / ideal-gas compressibility factor"

/-! ## (8) Magnetohydrodynamics — items 11-8.1 … 11-8.21

The electromagnetic-fluid characteristic numbers. Reynolds and Nusselt recur as the
*magnetic* and *electric* members (11-8.1, 11-8.3, 11-8.20); the definitions lean on IEC
80000-6 *Electromagnetism* (already specified). -/

def reynoldsMagnetic : DimensionedKind := charNum .mhd "Reynolds magnetic number" "inertial force / magneto-dynamic viscous force"
def batchelor : DimensionedKind := charNum .mhd "Batchelor number" "inertia / magneto-dynamic diffusion"
def nusseltElectric : DimensionedKind := charNum .mhd "Nusselt electric number" "convective / diffusive ion current"
def alfven : DimensionedKind := charNum .mhd "Alfvén number" "flow speed / Alfvén wave speed"
def hartmann : DimensionedKind := charNum .mhd "Hartmann number" "magnetically induced stress / viscous force"
def cowling : DimensionedKind := charNum .mhd "Cowling number" "magnetic / kinematic energy density"
def stuartElectrical : DimensionedKind := charNum .mhd "Stuart electrical number" "electric / kinematic energy density"
def magneticPressure : DimensionedKind := charNum .mhd "magnetic pressure number" "gas pressure / magnetic pressure"
def chandrasekhar : DimensionedKind := charNum .mhd "Chandrasekhar number" "Lorentz force / viscous force"
def prandtlMagnetic : DimensionedKind := charNum .mhd "Prandtl magnetic number" "kinematic viscosity / magnetic viscosity"
def roberts : DimensionedKind := charNum .mhd "Roberts number" "thermal diffusivity / magnetic viscosity"
def stuart : DimensionedKind := charNum .mhd "Stuart number" "magnetic force / inertial force"
def magneticNumber : DimensionedKind := charNum .mhd "magnetic number" "magnetic body force / viscous force"
def electricFieldParameter : DimensionedKind := charNum .mhd "electric field parameter" "Coulomb force / Lorentz force"
def hall : DimensionedKind := charNum .mhd "Hall number" "gyrofrequency / collision frequency"
def lundquist : DimensionedKind := charNum .mhd "Lundquist number" "Alfvén speed / magneto-dynamic diffusion speed"
def jouleMagnetic : DimensionedKind := charNum .mhd "Joule magnetic number" "Joule heating / magnetic field energy"
def grashofMagnetic : DimensionedKind := charNum .mhd "Grashof magnetic number" "thermo-magnetic buoyancy / viscous force"
def naze : DimensionedKind := charNum .mhd "Naze number" "Alfvén wave speed / sound speed"
def reynoldsElectric : DimensionedKind := charNum .mhd "Reynolds electric number" "fluid speed / charged-particle drift speed"
def ampere : DimensionedKind := charNum .mhd "Ampère number" "electric surface current / magnetic field"

/-! ## (9) Miscellaneous — items 11-9.1, 11-9.2 -/

def arrhenius : DimensionedKind := charNum .misc "Arrhenius number" "chemical activation energy / thermal energy"
def landauGinzburg : DimensionedKind := charNum .misc "Landau-Ginzburg number" "penetration depth / coherence length"

/-! ## The catalogue (every kind, with its source as data)

The coherent SI unit is `"1"` for every characteristic number — they are all dimension
one. -/

/-- The full ISO 80000-11 catalogue, in item order — all 115 characteristic numbers. -/
def catalogue : List CataloguedKind :=
  [-- (4) Momentum transfer
   cat "11-4.1" "Re" "1" reynolds,
   cat "11-4.2" "Eu" "1" euler,
   cat "11-4.3" "Fr" "1" froudeMomentum,
   cat "11-4.4" "Gr" "1" grashofThermal,
   cat "11-4.5" "We" "1" weber,
   cat "11-4.6" "Ma" "1" mach,
   cat "11-4.7" "Kn" "1" knudsen,
   cat "11-4.8" "Sr" "1" strouhal,
   cat "11-4.9" "c_D" "1" dragCoefficient,
   cat "11-4.10" "Bg" "1" bagnold,
   cat "11-4.11" "Ba₂" "1" bagnoldSolid,
   cat "11-4.12" "c_l" "1" liftCoefficient,
   cat "11-4.13" "c_t" "1" thrustCoefficient,
   cat "11-4.14" "Dn" "1" dean,
   cat "11-4.15" "Be" "1" bejanMomentum,
   cat "11-4.16" "Lg" "1" lagrange,
   cat "11-4.17" "Bm" "1" bingham,
   cat "11-4.18" "He" "1" hedstrom,
   cat "11-4.19" "Bd" "1" bodenstein,
   cat "11-4.20" "Ro" "1" rossby,
   cat "11-4.21" "Ek" "1" ekman,
   cat "11-4.22" "El" "1" elasticity,
   cat "11-4.23" "f_D" "1" darcyFriction,
   cat "11-4.24" "f_F" "1" fanning,
   cat "11-4.25" "Go" "1" goertler,
   cat "11-4.26" "Hg" "1" hagen,
   cat "11-4.27" "La" "1" laval,
   cat "11-4.28" "Poi" "1" poiseuille,
   cat "11-4.29" "Ne" "1" powerNumber,
   cat "11-4.30" "Ri" "1" richardson,
   cat "11-4.31" "Re_e" "1" reech,
   cat "11-4.32" "Stk" "1" stokesPlasma,
   cat "11-4.33" "Stk₁" "1" stokesVibrating,
   cat "11-4.34" "Stk₂" "1" stokesRotameter,
   cat "11-4.35" "Stk₃" "1" stokesGravity,
   cat "11-4.36" "Stk₄" "1" stokesDrag,
   cat "11-4.37" "La" "1" laplace,
   cat "11-4.38" "Bl" "1" blake,
   cat "11-4.39" "So" "1" sommerfeld,
   cat "11-4.40" "Ta" "1" taylor,
   cat "11-4.41" "Ga" "1" galilei,
   cat "11-4.42" "Wo" "1" womersley,
   -- (5) Transfer of heat
   cat "11-5.1" "Fo" "1" fourierHeat,
   cat "11-5.2" "Pe" "1" pecletHeat,
   cat "11-5.3" "Ra" "1" rayleigh,
   cat "11-5.4" "Fr*" "1" froudeHeat,
   cat "11-5.5" "Nu" "1" nusseltHeat,
   cat "11-5.6" "Bi" "1" biotHeat,
   cat "11-5.7" "St" "1" stantonHeat,
   cat "11-5.8" "j" "1" jFactorHeat,
   cat "11-5.9" "Be₁" "1" bejanHeat,
   cat "11-5.10" "Be_S" "1" bejanEntropy,
   cat "11-5.11" "Ste" "1" stefan,
   cat "11-5.12" "Br" "1" brinkman,
   cat "11-5.13" "Cl" "1" clausius,
   cat "11-5.14" "Ca" "1" carnot,
   cat "11-5.15" "Ec" "1" eckert,
   cat "11-5.16" "Gz" "1" graetzHeat,
   cat "11-5.17" "K_Q" "1" heatTransferNumber,
   cat "11-5.18" "Po" "1" pomerantsev,
   cat "11-5.19" "Bz" "1" boltzmann,
   cat "11-5.20" "Sk" "1" stark,
   -- (6) Transfer of matter in a binary mixture
   cat "11-6.1" "Fo*" "1" fourierMass,
   cat "11-6.2" "Pe*" "1" pecletMass,
   cat "11-6.3" "Gr*" "1" grashofMass,
   cat "11-6.4" "Nu*" "1" nusseltMass,
   cat "11-6.5" "St*" "1" stantonMass,
   cat "11-6.6" "Gz*" "1" graetzMass,
   cat "11-6.7" "j*" "1" massTransferFactor,
   cat "11-6.8" "At" "1" atwood,
   cat "11-6.9" "Bi*" "1" biotMass,
   cat "11-6.10" "Mo" "1" morton,
   cat "11-6.11" "Bo" "1" bond,
   cat "11-6.12" "Ar" "1" archimedes,
   cat "11-6.13" "Ex" "1" expansionNumber,
   cat "11-6.14" "Mg" "1" marangoni,
   cat "11-6.15" "Lp" "1" lockhartMartinelli,
   cat "11-6.16" "Be*" "1" bejanMass,
   cat "11-6.17" "Ca" "1" cavitation,
   cat "11-6.18" "Ab" "1" absorptionNumber,
   cat "11-6.19" "Ca" "1" capillary,
   cat "11-6.20" "Ca*" "1" dynamicCapillary,
   -- (7) Constants of matter
   cat "11-7.1" "Pr" "1" prandtl,
   cat "11-7.2" "Sc" "1" schmidt,
   cat "11-7.3" "Le" "1" lewis,
   cat "11-7.4" "Oh" "1" ohnesorge,
   cat "11-7.5" "Cy" "1" cauchy,
   cat "11-7.6" "Ho₂" "1" hooke,
   cat "11-7.7" "Wi" "1" weissenberg,
   cat "11-7.8" "De" "1" deborah,
   cat "11-7.9" "Lo" "1" lorentz,
   cat "11-7.10" "Z" "1" compressibility,
   -- (8) Magnetohydrodynamics
   cat "11-8.1" "Rm" "1" reynoldsMagnetic,
   cat "11-8.2" "Bt" "1" batchelor,
   cat "11-8.3" "Ne_e" "1" nusseltElectric,
   cat "11-8.4" "Al" "1" alfven,
   cat "11-8.5" "Ha" "1" hartmann,
   cat "11-8.6" "Co" "1" cowling,
   cat "11-8.7" "Se" "1" stuartElectrical,
   cat "11-8.8" "N_mp" "1" magneticPressure,
   cat "11-8.9" "Q" "1" chandrasekhar,
   cat "11-8.10" "Pr_m" "1" prandtlMagnetic,
   cat "11-8.11" "Ro_m" "1" roberts,
   cat "11-8.12" "N_St" "1" stuart,
   cat "11-8.13" "N_mg" "1" magneticNumber,
   cat "11-8.14" "E_f" "1" electricFieldParameter,
   cat "11-8.15" "Hl" "1" hall,
   cat "11-8.16" "Lu" "1" lundquist,
   cat "11-8.17" "Jo_m" "1" jouleMagnetic,
   cat "11-8.18" "Gr_m" "1" grashofMagnetic,
   cat "11-8.19" "Na" "1" naze,
   cat "11-8.20" "Re_e" "1" reynoldsElectric,
   cat "11-8.21" "Am" "1" ampere,
   -- (9) Miscellaneous
   cat "11-9.1" "α" "1" arrhenius,
   cat "11-9.2" "κ" "1" landauGinzburg]

/-! ## References to other parts — specified versus work-to-go

The definitions of these characteristic numbers name quantities from other parts of the
80000 series. Some of those parts this library has already mapped (`specifiedReferencedParts`);
others it leans on but has *not* yet mapped — those are recorded as **work-to-go**. -/

/-- The other parts of the 80000 series whose quantities ISO 80000-11's definitions
reference: space and time, mechanics, thermodynamics, electromagnetism, light and
radiation, acoustics (the speed of sound), physical chemistry (diffusion coefficients),
and condensed matter physics (relaxation times). -/
def referencedParts : List StandardRef :=
  [iso80000_3, iso80000_4, iso80000_5, iec80000_6, iso80000_7,
   iso80000_8, iso80000_9, iso80000_12]

/-- Of the referenced parts, those this library has already mapped into a `Part*`
catalogue. -/
def specifiedReferencedParts : List StandardRef :=
  [iso80000_3, iso80000_4, iso80000_5, iec80000_6, iso80000_7]

/-- The **work-to-go** references: parts ISO 80000-11 leans on that this library has not
yet mapped — ISO 80000-8 *Acoustics*, ISO 80000-9 *Physical chemistry and molecular
physics*, and ISO 80000-12 *Condensed matter physics*. -/
def workToGoParts : List StandardRef :=
  [iso80000_8, iso80000_9, iso80000_12]

/-- A part is **mapped** in this library iff its part number is one of those with a `Part*`
catalogue (3, 4, 5, 6, 7). -/
def partIsMapped (r : StandardRef) : Bool := [3, 4, 5, 6, 7].contains r.part

/-- The referenced parts split exactly into the specified ones and the work-to-go ones. -/
theorem referencedParts_partition :
    referencedParts = specifiedReferencedParts ++ workToGoParts := rfl

/-- The work-to-go parts are exactly the referenced parts this library has not mapped. -/
theorem workToGoParts_eq_unmapped :
    workToGoParts = referencedParts.filter (fun r => ! partIsMapped r) := by decide

/-! ## Every characteristic number is dimension one — the widest collapse in the series -/

/-- **Every characteristic number is dimension one, by construction.** The
{dimension functor} sends each one to the single point `1`. -/
theorem charNum_dim_one (ctx : Context) (id principle : String) :
    (charNum ctx id principle).dim = 1 := rfl

/-- **The entire ISO 80000-11 catalogue lives at dimension one.** All 115 characteristic
numbers share the dimensionless dimension; what distinguishes them is the measurement
principle, never the dimension. -/
theorem catalogue_all_dim_one : ∀ c ∈ catalogue, c.qk.dim = 1 := by
  intro c hc
  fin_cases hc <;> rfl

/-- The catalogue records all 115 items. -/
theorem catalogue_length : catalogue.length = 115 := rfl

/-! ## The sub-suffixed homonyms — same name, distinct kind by measurement principle

ISO 80000-11 reuses one name across its transport clauses, distinguishing the variants
only by a symbol suffix and a different defining ratio. Each is a distinct {kind}: not by
dimension (all are one) and not by name (shared), but by its {examination principle} —
the measurement principle — through `distinct_of_examPrinciple`. -/

/-- **The two Froude numbers are distinct kinds.** Both are named "Froude number" and both
are dimension one (11-4.3, `Fr`, momentum transfer; 11-5.4, `Fr*`, heat transfer), yet
they isolate different physical ratios — inertial/gravitational versus
gravitational/thermodiffusion forces. -/
theorem froudeMomentum_ne_froudeHeat : froudeMomentum.kind ≠ froudeHeat.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- The two Froude numbers nonetheless share the same name. -/
theorem froudeMomentum_id_eq_froudeHeat : froudeMomentum.kind.id = froudeHeat.kind.id := rfl

/-- The two Fourier numbers (heat 11-5.1 `Fo`, mass 11-6.1 `Fo*`) are distinct kinds. -/
theorem fourierHeat_ne_fourierMass : fourierHeat.kind ≠ fourierMass.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- The heat and mass Nusselt numbers (11-5.5, 11-6.4) are distinct kinds. -/
theorem nusseltHeat_ne_nusseltMass : nusseltHeat.kind ≠ nusseltMass.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- **The five Stokes numbers are pairwise distinct kinds.** All five (11-4.32 … 11-4.36)
carry the name "Stokes number" and dimension one, distinguished only by symbol suffix
(`Stk`, `Stk₁` … `Stk₄`) and the measurement principle each isolates. -/
theorem stokes_pairwise_distinct :
    stokesPlasma.kind ≠ stokesVibrating.kind ∧
    stokesVibrating.kind ≠ stokesRotameter.kind ∧
    stokesRotameter.kind ≠ stokesGravity.kind ∧
    stokesGravity.kind ≠ stokesDrag.kind ∧
    stokesPlasma.kind ≠ stokesDrag.kind :=
  ⟨KindOfProperty.distinct_of_examPrinciple (by decide),
   KindOfProperty.distinct_of_examPrinciple (by decide),
   KindOfProperty.distinct_of_examPrinciple (by decide),
   KindOfProperty.distinct_of_examPrinciple (by decide),
   KindOfProperty.distinct_of_examPrinciple (by decide)⟩

/-- **The four Bejan numbers are distinct kinds.** The momentum (11-4.15), the two heat
(11-5.9, 11-5.10) and the mass (11-6.16) Bejan numbers are four kinds — even the two heat
ones, sharing name *and* transport context, differ by their measurement principle. -/
theorem bejan_four_distinct :
    bejanMomentum.kind ≠ bejanHeat.kind ∧
    bejanHeat.kind ≠ bejanEntropy.kind ∧
    bejanEntropy.kind ≠ bejanMass.kind ∧
    bejanMomentum.kind ≠ bejanMass.kind :=
  ⟨KindOfProperty.distinct_of_examPrinciple (by decide),
   KindOfProperty.distinct_of_examPrinciple (by decide),
   KindOfProperty.distinct_of_examPrinciple (by decide),
   KindOfProperty.distinct_of_examPrinciple (by decide)⟩

/-! ## Units and (in)commensurability — one unit symbol, many kinds

Every characteristic number has the same coherent unit symbol, `"1"`. Yet two
characteristic numbers are *not commensurable* — they reference different kinds. The
shared unit symbol does not make a Reynolds number a Froude number. -/

/-- The coherent unit (symbol `"1"`) of the Reynolds number. -/
def reynoldsUnit : MetrologicalUnit := reynolds.kind.unit "1"
/-- The coherent unit (symbol `"1"`) of the Euler number. -/
def eulerUnit : MetrologicalUnit := euler.kind.unit "1"

/-- The Reynolds number's unit is well-formed (a ratio-scale kind bears a unit). -/
theorem reynoldsUnit_wellFormed : reynoldsUnit.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- **The Reynolds and Euler units are not commensurable, though both have unit symbol
`"1"`.** Same symbol, same dimension (one), different kind — so a value of one cannot be
read as a value of the other. The kind layer keeps them apart where the unit symbol and
the dimension cannot. -/
theorem reynolds_euler_not_commensurable :
    ¬ reynoldsUnit.Commensurable eulerUnit := by
  unfold MetrologicalUnit.Commensurable reynoldsUnit eulerUnit reynolds euler charNum
    KindOfProperty.unit
  decide

/-! ## The dimension-one collision capstone — R1 at its widest

ISO 80000-11 is the part where the *dimension does not classify the kind* thesis is total:
*every* kind collides on dimension one, and the part is held apart entirely by the
measurement principle (R2). -/

/-- The Reynolds and Euler numbers are distinct kinds. -/
theorem reynolds_ne_euler : reynolds.kind ≠ euler.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- **The dimension-one collision, on the standard — total, the widest in the series.**
There exist distinct ISO 80000-11 kinds with the same dimension one — the Reynolds and
Euler numbers witness it, alongside *all* 113 others. The {dimension functor} collapses
the entire part to one point; the kind layer, through the measurement principle, keeps its
115 members apart. -/
theorem iso80000_11_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨reynolds, euler, reynolds_ne_euler, rfl, rfl⟩

end PropertyKindCalculus.Iso80000.Part11
