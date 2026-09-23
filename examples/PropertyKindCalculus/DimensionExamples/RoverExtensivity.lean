/-
# Worked example: one rover, three scopes of extensivity

A rover: a chassis and four arms, each arm carrying a motor hub and a wheel. Three of its
quantities aggregate over the same carving, and no two aggregate under the same license:

  1. **Mass rolls up unconditionally** (§13.5.1): the rover's mass is the sum over the parts,
     whatever tree they are carved into.
  2. **Angular momentum rolls up per reference point**: each wheel's spin is read about its
     own axle, and whether the four spins may be summed as-is against a common point is not
     a convention but a priced question — the price is each assembly's momentum
     (`angularMomentumTransport`), zero while the rover is parked, `M·v` once it drives.
  3. **The drive torques roll up by cancellation**: the motor torque on a hub and its
     reaction on the chassis are one interface, not two properties. The per-part nets are
     real — they load bearings — and their sum is the exogenous torque alone
     (`InterfaceLedger.netTotal_eq_extTotal`); additivity here is a theorem purchased by the
     third-law field, not a modeling choice, and dropping the reactions makes it fail by
     exactly `netTotal_union`'s price.

The carving is also shown *destroying* an interface: coarsen a hub and its rims into one
part and the drive torque between them lands on the diagonal, where the ledger's own law
annihilates it — two rovers with materially different drive trains coarsen to the same
ledger, so internal-versus-external is the carving's fact, not the machine's.

Positions and rates are schematic (unit masses, unit wheel radius, integer stations): the
content is the license discipline, not the chassis drawing. Lives with the
`DimensionExamples` because the transport laws use `ring`.
-/

module

public import PropertyKindCalculus.InterfaceLedger
public import PropertyKindCalculus.AggregationLaws
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.InterfaceLedger

@[expose] public section Blanket

namespace PropertyKindCalculus.DimensionExamples.RoverExtensivity

/-! ## The rover's parts and state -/

/-- The four arms. -/
inductive Arm
  | a1 | a2 | a3 | a4
deriving DecidableEq, Repr

/-- The rover's atomic parts: the chassis, and per arm a motor hub and the wheel's two rim
masses. Two rim masses are the least wheel that can *spin*: equal masses at opposite ends of
a diameter give the wheel angular momentum about its axle while its own momentum balances to
zero. -/
inductive RoverPart
  | chassis
  | hub (i : Arm)
  | rimTop (i : Arm)
  | rimBottom (i : Arm)
deriving DecidableEq, Repr

/-- Forward station of each arm's axle. -/
def axleX : Arm → Int
  | .a1 => -3 | .a2 => -1 | .a3 => 1 | .a4 => 3

/-- Masses: a heavy chassis, unit hubs and rims. -/
def mass : RoverPart → Int
  | .chassis => 10 | .hub _ => 1 | .rimTop _ => 1 | .rimBottom _ => 1

/-- Forward positions, in the plane of travel (`x` forward, `y` up). -/
def posX : RoverPart → Int
  | .chassis => 0 | .hub i => axleX i | .rimTop i => axleX i | .rimBottom i => axleX i

/-- Heights: axles at 1, rim masses at the top and bottom of a unit wheel. -/
def posY : RoverPart → Int
  | .chassis => 2 | .hub _ => 1 | .rimTop _ => 2 | .rimBottom _ => 0

/-- Parked, wheels spinning at unit rate: rim tops run backward, rim bottoms forward,
hubs and chassis sit still. -/
def spinVx : RoverPart → Int
  | .rimTop _ => -1 | .rimBottom _ => 1 | _ => 0

/-- The same spin with the rover driving forward at 5: every part carries the translation. -/
def driveVx (p : RoverPart) : Int := spinVx p + 5

/-- Nothing moves vertically. -/
def zeroVy : RoverPart → Int := fun _ => 0

/-- Arm `i`'s assembly — motor hub and the wheel's two rim masses. -/
def assembly (i : Arm) : Decomposition RoverPart :=
  .union (.atom (.hub i)) (.union (.atom (.rimTop i)) (.atom (.rimBottom i)))

/-- The chassis, as a carving of its own. -/
def chassisOnly : Decomposition RoverPart := .atom .chassis

/-- The four arms together. -/
def armsOnly : Decomposition RoverPart :=
  .union (.union (assembly .a1) (assembly .a2)) (.union (assembly .a3) (assembly .a4))

/-- The rover, carved to its thirteen parts. -/
def rover : Decomposition RoverPart := .union chassisOnly armsOnly

/-! ## 1. Mass — the unconditional rollup -/

/-- Mass, a ratio kind. -/
def massKind : KindOfProperty := { id := "mass", scale := .ratio }

/-- The rover's mass measurement: a leaf reads its part's mass, a union the sum. -/
def roverMass : Measurement RoverPart
  | .atom p => { kind := massKind, numeral := mass p, reference := "kg" }
  | .union a b =>
      { kind := massKind,
        numeral := (roverMass a).numeral + (roverMass b).numeral,
        reference := "kg" }

/-- Mass is extensive, with no side condition to discharge. -/
theorem roverMass_extensive : Extensive massKind roverMass :=
  ⟨fun d => by cases d <;> rfl, fun _ _ => rfl⟩

-- The rover reads 22 kg, and the reading is the leaf sum *as a law*, not as arithmetic.
example : (roverMass rover).numeral = 22 := by decide
example : (roverMass rover).numeral = leafSum roverMass rover :=
  extensive_additive roverMass_extensive rover

/-! ## 2. Angular momentum — the rollup is per reference point, and the price is momentum

Each assembly's spin reads 2 about its own axle, parked or driving — translation is
invisible about the assembly's own mass centre. Whether those per-axle readings may be
summed against a common point is exactly what `angularMomentumTransport` prices: the
correction from axle to origin is the assembly's own momentum, so the parked shortcut is
*licensed* (price zero) and the driving one is wrong by four measured prices. -/

/-- The rover's angular momentum about a point, parked. -/
abbrev parkedL : ParamMeasurement (Int × Int) RoverPart :=
  angularMomentumMeasurement mass posX posY spinVx zeroVy

/-- The rover's angular momentum about a point, driving. -/
abbrev drivingL : ParamMeasurement (Int × Int) RoverPart :=
  angularMomentumMeasurement mass posX posY driveVx zeroVy

/-- Arm `i`'s axle — the natural point to read its spin about. -/
def axle (i : Arm) : Int × Int := (axleX i, 1)

/-- The common reference point. -/
def origin : Int × Int := (0, 0)

-- Each assembly's spin about its own axle reads 2 — parked or driving.
example : (parkedL (axle .a1) (assembly .a1)).numeral = 2 := by decide
example : (drivingL (axle .a1) (assembly .a1)).numeral = 2 := by decide

-- Parked, the untransported sum of the four spins (plus the chassis) *is* the whole about
-- the origin …
example :
    (parkedL origin rover).numeral
      = (parkedL origin chassisOnly).numeral
        + ((parkedL (axle .a1) (assembly .a1)).numeral
           + (parkedL (axle .a2) (assembly .a2)).numeral
           + (parkedL (axle .a3) (assembly .a3)).numeral
           + (parkedL (axle .a4) (assembly .a4)).numeral) := by decide

-- … and lawfully so: the general transport prices the axle-to-origin move by the assembly's
-- momentum components, and the parked assembly's momentum vanishes.
example :
    (parkedL origin (assembly .a1)).numeral
      = (parkedL (axle .a1) (assembly .a1)).numeral
        + ((origin.1 - (axle .a1).1) * firstMoment mass zeroVy (assembly .a1)
           - (origin.2 - (axle .a1).2) * firstMoment mass spinVx (assembly .a1)) := by
  have h := (angularMomentumMeasurement_transports mass posX posY spinVx zeroVy).transport
    origin (axle .a1) (assembly .a1)
  exact h
example : firstMoment mass spinVx (assembly .a1) = 0 := by decide

-- Driving: the same carving, the same per-axle spin readings — and the untransported sum is
-- wrong (−92 for a whole at −152) …
example : (drivingL origin rover).numeral = -152 := by decide
example :
    (drivingL origin rover).numeral
      ≠ (drivingL origin chassisOnly).numeral
        + ((drivingL (axle .a1) (assembly .a1)).numeral
           + (drivingL (axle .a2) (assembly .a2)).numeral
           + (drivingL (axle .a3) (assembly .a3)).numeral
           + (drivingL (axle .a4) (assembly .a4)).numeral) := by decide

-- … by exactly four transport prices: each driving assembly carries momentum 15, so each
-- axle-to-origin move costs −15, and the four prices close the −60 gap.
example : firstMoment mass driveVx (assembly .a1) = 15 := by decide
example :
    (drivingL origin (assembly .a1)).numeral
      = (drivingL (axle .a1) (assembly .a1)).numeral + (-15) := by decide
example :
    (drivingL origin rover).numeral
      = (drivingL origin chassisOnly).numeral
        + (((drivingL (axle .a1) (assembly .a1)).numeral + (-15))
           + ((drivingL (axle .a2) (assembly .a2)).numeral + (-15))
           + ((drivingL (axle .a3) (assembly .a3)).numeral + (-15))
           + ((drivingL (axle .a4) (assembly .a4)).numeral + (-15))) := by decide

/-! ## 3. Drive torque — additivity purchased by the third law

The motor torques live on *interfaces*, not parts: the chassis-mounted motor puts 4 units on
its hub, the hub passes 2 to each rim, the road pushes back on the rim bottoms. The ledger
is entered one direction at a time and antisymmetrized, so the law is arithmetic. -/

/-- Torque about the axle axis, a ratio kind. -/
def torqueKind : KindOfProperty := { id := "torque", scale := .ratio }

/-- The drive train, entered one direction: motor to hub, hub to rims. -/
def rawDrive : RoverPart → RoverPart → Int
  | .chassis, .hub _ => 4
  | .hub i, .rimTop j => if i = j then 2 else 0
  | .hub i, .rimBottom j => if i = j then 2 else 0
  | _, _ => 0

/-- The rover's torque ledger: the raw table antisymmetrized, so every action carries its
reaction and the third-law field is `omega`. -/
def ledger : InterfaceLedger RoverPart :=
  { act := fun p q => rawDrive p q - rawDrive q p
    antisymm := fun _ _ => by omega }

/-- Ground reaction on the rim bottoms — exogenous, because the road is not a part. -/
def groundTorque : RoverPart → Int
  | .rimBottom _ => -2 | _ => 0

-- The reaction on the chassis is real per part — four motors' worth of induced torque —
-- and a hub's net balances: 4 in from its motor, 2 + 2 out to its rims.
example : netOn ledger.act groundTorque rover .chassis = -16 := by decide
example : netOn ledger.act groundTorque rover (.hub .a1) = 0 := by decide

-- The rollup is the exogenous total alone — by the general law, not by these numbers —
-- so the motor torques are real in every bearing and absent from the whole.
example : netTotal ledger.act groundTorque rover = partTotal groundTorque rover :=
  ledger.netTotal_eq_extTotal groundTorque rover
example : netTotal ledger.act groundTorque rover = -8 := by decide

-- The net over the ledger *is* extensive — additivity purchased by the `antisymm` field:
example : Extensive torqueKind (ledger.netMeasurement torqueKind "N·m" groundTorque) :=
  ledger.netMeasurement_extensive torqueKind "N·m" groundTorque

-- Log the actions and forget the reactions, and the price identity presents its invoice:
-- the raw table's rollup over the whole is not the sum of its halves' rollups, and the gap
-- is exactly the uncancelled flow across the chassis–arms cut (16, four motors' worth).
example :
    netTotal rawDrive groundTorque rover
      = (netTotal rawDrive groundTorque chassisOnly + netTotal rawDrive groundTorque armsOnly)
        + (mutualTotal rawDrive chassisOnly armsOnly
           + mutualTotal rawDrive armsOnly chassisOnly) :=
  netTotal_union rawDrive groundTorque chassisOnly armsOnly
example :
    mutualTotal rawDrive chassisOnly armsOnly
      + mutualTotal rawDrive armsOnly chassisOnly = 16 := by decide
example :
    netTotal rawDrive groundTorque rover
      ≠ netTotal rawDrive groundTorque chassisOnly
        + netTotal rawDrive groundTorque armsOnly := by decide

/-! ## The carving that destroys an interface

Coarsen each arm to a single part and the hub-to-rim torque has nowhere to live: both its
ends bear one name, so it lands on the diagonal, where the cancellation law annihilates it
(`InterfaceLedger.act_self` is the atom-level form). The destruction is real: a second rover
whose hubs feed the rims 3/1 instead of 2/2 — a materially different machine, ask the bottom
rims' bearings — coarsens to the *same* ledger. What a carving does not separate, no ledger
over it can report; internal-versus-external is the carving's fact, not the machine's. -/

/-- The coarse parts: the chassis, or a whole arm. -/
inductive CoarsePart
  | chassis
  | assembly (i : Arm)
deriving DecidableEq, Repr

/-- The fine parts a coarse part collects. -/
def partsOf : CoarsePart → List RoverPart
  | .chassis => [.chassis]
  | .assembly i => [.hub i, .rimTop i, .rimBottom i]

/-- A fine pairwise action re-read at the coarse parts: every fine entry between the two
preimages, summed. -/
def coarsen (act : RoverPart → RoverPart → Int) (p q : CoarsePart) : Int :=
  ((partsOf p).map fun a => ((partsOf q).map (act a)).foldr (· + ·) 0).foldr (· + ·) 0

-- The chassis–arm interface survives coarsening; the hub–rim interface lands on the
-- diagonal and reads zero — forced by the law, not by bookkeeping.
example : coarsen ledger.act .chassis (.assembly .a1) = 4 := by decide
example : coarsen ledger.act (.assembly .a1) (.assembly .a1) = 0 := by decide

/-- The second drive train: same motor torque, but each hub feeds its top rim 3 and its
bottom rim 1. -/
def rawDrive' : RoverPart → RoverPart → Int
  | .chassis, .hub _ => 4
  | .hub i, .rimTop j => if i = j then 3 else 0
  | .hub i, .rimBottom j => if i = j then 1 else 0
  | _, _ => 0

/-- The second rover's ledger. -/
def ledger' : InterfaceLedger RoverPart :=
  { act := fun p q => rawDrive' p q - rawDrive' q p
    antisymm := fun _ _ => by omega }

-- The two machines differ at the fine carving …
example :
    ledger.act (.hub .a1) (.rimBottom .a1) ≠ ledger'.act (.hub .a1) (.rimBottom .a1) := by
  decide

/-- … and agree, entry for entry, at the coarse one: the drive-train difference is not
recoverable from any carving that does not separate a hub from its rims. -/
theorem coarse_cannot_tell :
    ∀ p q : CoarsePart, coarsen ledger.act p q = coarsen ledger'.act p q := by
  intro p q
  cases p with
  | chassis =>
    cases q with
    | chassis => decide
    | assembly j => cases j <;> decide
  | assembly i =>
    cases q with
    | chassis => cases i <;> decide
    | assembly j => cases i <;> cases j <;> decide

end PropertyKindCalculus.DimensionExamples.RoverExtensivity

end Blanket
