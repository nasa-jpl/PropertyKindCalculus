/-
# Exhibit E — Electromagnetism: the confirmation

**Built last, on purpose after the machinery.** Every construct this file leans on —
`kind_algebra`, `LevelKind`, `KindJoin`/`SpecializationLift`, the `Complex` carrier —
was minted against the oscillator benchmark; its job here is to solve problems it was
not built against, in `Physlib/Electromagnetism/` as it stands.

**The genuine problems, each a build artifact:**

1. **An electric field *is* a magnetic field.** `ElectricField` and `MagneticField` are
   abbreviations with the same right-hand side: their equality is `rfl`, a function
   expecting `E` accepts `B`, and `ChargeDensity` accepts any scalar field. M5's theme —
   correctness resting on *not being an abbreviation* — at the heart of a second
   directory.
2. **The dimension layer cannot fix it in every basis.** Over a Gaussian–CGS basis
   (expressible since PhysLib's `Dimension` became basis-parametric), `E` and `B` share
   the dimension `M^½ L^-½ T⁻¹` — proved below — so a `WithDim` repair of problem 1 is
   basis-relative. The kinds stay apart by `decide` over the same basis.
3. **Natural units are a silent default.** `electricField (c : SpeedOfLight := 1)`:
   the unit system rides in an optional argument that defaults at every call site — the
   probe omits it and nothing shows. The kinded answer is one greppable declaration.
4. **A potential is a position, not a value.** The scalar potential is gauge-dependent;
   stated as an *interval*-scale kind, its differences are licensed and its ratios
   refuse to elaborate — the torsor pattern at the scale gate.
5. **The green field.** PhysLib has no AC/RF physics. Impedance arrives at the complex
   carrier (MR14); dBm and dBW are distinct kinds by `decide` with a worked link budget
   and the sum `dBm + dBm` structurally unavailable; and the AC power family — one
   dimension, three unit strings (`W`, `var`, `VA`) — is a specialization lattice with
   a deliberate **curation contrast**: energy registers `T + V` at its join (MR32),
   this family registers *no* join, because `P + Q` is the domain error
   (`S² = P² + Q²`). Comparable kinds whose sum is refused is the same machinery run
   the other way — the pair is the proof that the join table is curation, not a
   loophole.

E–B mixing under boosts stays with the field-strength tensor, as PhysLib already has
it: the kind layer records what survives a boost (MR18); it does not re-derive
electrodynamics.
-/

import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Kinematics.ElectricField
import Physlib.Units.Dimension
import PropertyKindCalculus.KindAlgebra
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.Iso80000.Part5
import PropertyKindCalculus.Iso80000.Part6
import PropertyKindCalculus.SpecializationLift
import PropertyKindCalculus.Level
import PropertyKindCalculus.Complex
import PropertyKindCalculus.QuantityReal

namespace ForPhysLib.Exhibits.Electromagnetism

open PropertyKindCalculus

/-! ## Problem 1 — an electric field *is* a magnetic field -/

/-- The two field types are the *same* type — `rfl`, because both are abbreviations of
`Time → Space 3 → EuclideanSpace ℝ (Fin 3)`. -/
example : _root_.Electromagnetism.ElectricField 3
    = _root_.Electromagnetism.MagneticField 3 := rfl

/-- A function expecting an electric field. -/
def expectsE (E : _root_.Electromagnetism.ElectricField 3) :
    _root_.Electromagnetism.ElectricField 3 := E

/-- …accepts a magnetic field, with no error. -/
example (B : _root_.Electromagnetism.MagneticField 3) :
    _root_.Electromagnetism.ElectricField 3 := expectsE B

/-- And `ChargeDensity` accepts *any* scalar field — here, a temperature field. -/
example (temperature : Time → Space → ℝ) :
    _root_.Electromagnetism.ChargeDensity := temperature

/-! ### The kinded vocabulary — where the swap fails

Base kinds are the catalogue's own entries; the electrical algebra below arrives in
one `kind_algebra` block (the MR11 answer, measured on this directory). -/

/-- Electric field strength — the catalogue's own IEC 80000-6 item 6-10. -/
def electricFieldK : KindOfProperty := (Iso80000.Part6.electricFieldStrength).kind

/-- Magnetic flux density — the catalogue's own item 6-21, a distinct entry at its own
dimension. -/
def magneticFieldK : KindOfProperty := (Iso80000.Part6.magneticFluxDensity).kind

/-- Charge density — the catalogue's own 6-3: a density, not any scalar field. -/
def chargeDensityK : KindOfProperty := (Iso80000.Part6.electricChargeDensity).kind

/-- A kinded field reading: the carrier is the directory's own function type; only the
reading changed. -/
def expectsEK (E : Quantity electricFieldK (_root_.Electromagnetism.ElectricField 3)) :
    Quantity electricFieldK (_root_.Electromagnetism.ElectricField 3) := E

/- **Problem 1, closed.** The kinded swap does not elaborate. -/
#check_failure fun (B : Quantity magneticFieldK (_root_.Electromagnetism.MagneticField 3)) =>
  expectsEK B

/- Nor does a temperature field pass as a charge density. -/
#check_failure fun (temp : Quantity (Iso80000.Part5.thermodynamicTemperature).kind
    (Time → Space → ℝ)) => (temp : Quantity chargeDensityK (Time → Space → ℝ))

/-! ## Problem 2 — the Gaussian basis: dimensions coincide, kinds stay apart -/

/-- The Gaussian–CGS base dimensions: length, mass, time. Expressible because
PhysLib's `Dimension` is basis-parametric. -/
inductive GaussianBase
  | length | mass | time
deriving DecidableEq

instance : DimensionBasis GaussianBase := DimensionBasis.pi _

/-- The dimension of `E` in Gaussian units (statvolt/cm): `M^½ L^-½ T⁻¹`. -/
def dimE : Dimension GaussianBase :=
  .ofFunction fun b => match b with
    | .mass => 1/2 | .length => -(1/2) | .time => -1

/-- The dimension of `B` in Gaussian units (gauss): `M^½ L^-½ T⁻¹`. -/
def dimB : Dimension GaussianBase :=
  .ofFunction fun b => match b with
    | .mass => 1/2 | .length => -(1/2) | .time => -1

/-- **The coincidence, proved.** Over the Gaussian basis the two dimensions are equal —
so a `WithDim`-style repair of problem 1 is *basis-relative*: it separates `E` from `B`
in SI and identifies them here. -/
theorem gaussian_dimensions_coincide : dimE = dimB := rfl

/-- **And the kinds are not.** Kind identity is examination, not exponents; it does not
change with the basis. -/
theorem kinds_stay_apart : electricFieldK ≠ magneticFieldK := by decide

/-! ## Problem 3 — natural units are a silent default -/

/-- The probe: `electricField` called with no unit system at all — the
`(c : SpeedOfLight := 1)` default decided the physics at this call site, invisibly. -/
noncomputable example (A : _root_.Electromagnetism.ElectromagneticPotential 3) :
    _root_.Electromagnetism.ElectricField 3 :=
  _root_.Electromagnetism.ElectromagneticPotential.electricField (A := A)

/-- The kinded answer: the choice is a *declaration* — named, attested, greppable —
rather than an elision repeated at every call site. -/
def speedOfLightK : KindOfProperty := (Iso80000.Part6.speedOfLight).kind

/-- "This development works in natural units": stated once. -/
noncomputable def chosenC : Quantity speedOfLightK ℝ :=
  .attest "natural units: c = 1 by convention, chosen for this development" 1

/-! ## Problem 4 — a potential is a position, not a value

Gauge freedom, said as a scale: the scalar potential is *interval* — differences
licensed, ratios not. The physical extents are the differences; PhysLib's proof that
the field strength is gauge-invariant is the calculus-level fact, and this is its
value-level shadow. -/

/-- The scalar potential — the catalogue's own 6-11.1, **interval-scale in the standard
itself**: no absolute zero, by gauge freedom. -/
def potentialK : KindOfProperty := (Iso80000.Part6.electricPotential).kind

/-- A potential difference — the catalogue's own 6-11.2: the physical extent; ratio
scale. -/
def potentialDiffK : KindOfProperty := (Iso80000.Part6.electricPotentialDifference).kind

/-- The torsor's `-ᵥ`: two positions on the potential axis determine an extent. -/
def potentialSub (x y : Quantity potentialK ℝ) : Quantity potentialDiffK ℝ :=
  ⟨x.magnitude - y.magnitude⟩

/- A *ratio* of potentials is refused at the scale gate: `ofRatio`'s obligations are
unprovable at interval scale. The gauge convention cannot cancel out of a quotient, and
the calculus will not form one. -/
#check_failure (QuotientKind.ofRatio potentialK potentialK potentialDiffK)

/-! ## Problem 5 — the green field: the RF/AC annex

PhysLib has no AC or RF physics; this is where the minted machinery bites first-hand. -/

/-! ### Impedance, at the complex carrier (MR14) -/

/-- Voltage — the catalogue's own 6-11.3 (AC phasor-valued below). -/
def voltageK : KindOfProperty := (Iso80000.Part6.voltage).kind

/-- Current — the catalogue's own 6-1. -/
def currentK : KindOfProperty := (Iso80000.Part6.electricCurrent).kind

kind_algebra
  impedanceK     : "impedance"      := voltageK / currentK
  apparentRawK   : "voltage × current" := voltageK * currentK

open scoped PropertyKindCalculus.OperatorTable

/-- Ohm's law at phasors: a complex voltage over a complex current is a complex
impedance — `Quantity.div` at the `Complex Float` carrier, through the table. -/
def impedanceOf (v : Quantity voltageK (Complex Float))
    (i : Quantity currentK (Complex Float)) : Quantity impedanceK (Complex Float) :=
  v / i

/- Complex carriers do not weaken the curation: an unregistered pair still refuses. -/
#check_failure fun (v w : Quantity voltageK (Complex Float)) => v * w

/-! ### dBm, dBW and the link budget (`LevelKind`) -/

/-- Power — the catalogue's own 6-45, the root kind of dBm and dBW. -/
def elPowerK : KindOfProperty := (Iso80000.Part6.power).kind

/-- Power level re 1 mW — the dBm. -/
def dBm : LevelKind := ⟨elPowerK, .power, "1 mW"⟩

/-- Power level re 1 W — the dBW: same root, same role, different reference. -/
def dBW : LevelKind := ⟨elPowerK, .power, "1 W"⟩

/-- dBm and dBW are different kinds — the reference is kind identity. -/
theorem dBm_ne_dBW : dBm.toKind ≠ dBW.toKind := by decide

/-- …but their *gains* are one kind: the reference cancels in every difference, so an
amplifier's dB figure serves either level. -/
theorem gain_shared : dBm.gainKind = dBW.gainKind := rfl

/- Two transmitter levels do not add: `DifferenceKind` is unprovable at an ordinal
level kind, so the certified sum never forms — 30 dBm + 30 dBm is not 60 dBm, and is
not writable. -/
#check_failure fun (x y : Quantity dBm.toKind Int) =>
  Quantity.add DifferenceKind.ofScale x y

/-- **A worked link budget**, exact at `Int`: 30 dBm out, +3 dB Tx antenna, −100 dB
path, +2 dB Rx antenna → −65 dBm at the receiver. Levels shift by gains; gains are the
only thing that ever adds. -/
example :
    dBm.shift (dBm.shift (dBm.shift (⟨30⟩ : Quantity dBm.toKind Int) ⟨3⟩) ⟨-100⟩) ⟨2⟩
      = ⟨-65⟩ := rfl

/-! ### The AC power lattice — and the refused join (MR32, run backwards)

Active, reactive, apparent: one dimension, three unit strings (`W`, `var`, `VA`),
individuated by examination. They are mutually comparable as AC powers — and their sums
are **deliberately unregistered**, because `P + Q` is the domain error: powers add in
quadrature, `S² = P² + Q²`. The energy family alongside registers its join, so the pair
exhibits the same table saying yes and saying no. -/

/-- The genus: power — the catalogue's own 6-45 (the same entry `elPowerK` names: the
standard's broad genus covers DC and AC alike). -/
def acPowerK : KindOfProperty := (Iso80000.Part6.power).kind

/-- Active power — the catalogue's own 6-56 (`W`, the time-averaged real component). -/
def activePowerK : KindOfProperty := (Iso80000.Part6.activePower).kind

/-- Reactive power — the catalogue's own 6-60 (`var`, the quadrature component). -/
def reactivePowerK : KindOfProperty := (Iso80000.Part6.reactivePower).kind

/-- Apparent power — the catalogue's own 6-57 (`VA`, the RMS product). -/
def apparentPowerK : KindOfProperty := (Iso80000.Part6.apparentPower).kind

/-- The AC power family's specialization edges. -/
inductive PowerEdge : KindOfProperty → KindOfProperty → Prop
  /-- Active power is an AC power. -/
  | active : PowerEdge activePowerK acPowerK
  /-- Reactive power is an AC power. -/
  | reactive : PowerEdge reactivePowerK acPowerK
  /-- Apparent power is an AC power. -/
  | apparent : PowerEdge apparentPowerK acPowerK

/-- Comparable as AC powers while staying three kinds — R2's comparability without
identity, on the family the units already distinguish. -/
theorem active_comparable_reactive :
    MutuallyComparable PowerEdge activePowerK reactivePowerK :=
  ⟨acPowerK, .of_edge .active, .of_edge .reactive⟩

/- **The refusal.** No `KindJoin` entry exists for `(active, reactive)`, so `P + Q`
fails to elaborate — comparability did not license the sum, because the domain says the
sum is wrong. -/
#check_failure fun (P : Quantity activePowerK ℝ) (Q : Quantity reactivePowerK ℝ) => P + Q

/-- What *is* licensed: powers add in quadrature. The apparent power from `P` and `Q`,
with the law in its name. -/
noncomputable def apparentFrom (P : Quantity activePowerK ℝ) (Q : Quantity reactivePowerK ℝ) :
    Quantity apparentPowerK ℝ :=
  .attest "S² = P² + Q²: powers orthogonal, combined in quadrature"
    (Real.sqrt (P.magnitude ^ 2 + Q.magnitude ^ 2))

/-! ### The contrast: energy registers its join -/

/-- Kinetic energy — the catalogue's own 4-28.2. -/
def kineticK : KindOfProperty := (Iso80000.Part4.kineticEnergy).kind

/-- Potential energy — the catalogue's own 4-28.1. -/
def potentialEnergyK : KindOfProperty := (Iso80000.Part4.potentialEnergy).kind

/-- Their join — the catalogue's own mechanical energy (4-28.3). -/
def energyK : KindOfProperty := (Iso80000.Part4.mechanicalEnergy).kind

/-- The energy family's edges. -/
inductive EnergyEdge : KindOfProperty → KindOfProperty → Prop
  /-- Kinetic energy is an energy. -/
  | kinetic : EnergyEdge kineticK energyK
  /-- Potential energy is an energy. -/
  | potential : EnergyEdge potentialEnergyK energyK

/-- `T + V` is licensed at the join — the registration the AC family refuses. -/
instance : KindJoin EnergyEdge kineticK potentialEnergyK energyK :=
  ⟨.of_edge .kinetic, .of_edge .potential, .ofScale⟩

/-- `T + V` elaborates, lands at energy — same table, same file, opposite verdict:
the join table is curation, not a loophole. -/
noncomputable example (T : Quantity kineticK ℝ) (V : Quantity potentialEnergyK ℝ) :
    Quantity energyK ℝ := T + V

end ForPhysLib.Exhibits.Electromagnetism
