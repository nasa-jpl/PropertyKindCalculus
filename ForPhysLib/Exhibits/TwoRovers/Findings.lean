/-
# Exhibit D — TwoRovers: the construction

**Not a refactor.** Two rovers, each with a chassis, a mast, four wheels and four drive
motors — the Tier-7 requirements exercised on a system built out of the same mechanics
Exhibits A–C probed, with every claim a build artifact.

**Two rovers, not one — the point of the exhibit.** With one rover, every mass in scope
is a correct summand and "the sum of the parts" cannot be told from "the sum of some
masses of the right dimension". With two:

1. **The total is a theorem** (`rover1_total_is_sum`): the stated total equals the sum
   of rover 1's *own* parts — change the parts list and the proof obligation changes.
2. **Cross-system contamination does not compile**: substituting rover 2's chassis mass
   into rover 1's sum, or adding the two chassis masses at all, is a `#check_failure`.
3. **Under-counting is caught** (`undercount_caught`): the nine-part sum that silently
   drops a wheel is provably not the total.

**And assembly is two-sided (MR21).** Mass carries the `Assembles` licence and sums;
angular velocity carries none, and the sum of the parts' angular velocities *fails to
elaborate* — a scheme that got (2) by forbidding (1) would have failed here.

The rest of the tier rides on the same construction: the wheelbase is the *system's*
quantity, not any part's (MR22); the motor-to-wheel torque names both endpoints, so the
left wheel's torque cannot be delivered to the right (MR23); every part mass carries a
dedication tag — measured, specified, derived or assumed (MR24); and `assemble` is
carrier-generic, exercised at `ℝ` and at `Float32` (MR27). The construction is not
speculative — the same requirements are discharged at scale in the author's
soil-moisture model; this file shows a PhysLib reader what they buy, small.
-/

import PropertyKindCalculus
import PropertyKindCalculus.QuantityReal
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4
import Mathlib.Tactic.NormNum

namespace ForPhysLib.Exhibits.TwoRovers

open PropertyKindCalculus

/-! ## The vocabulary and the two systems -/

/-- Mass — extensive, and licensed to assemble below; the catalogue's own 4-1. -/
def massK : KindOfProperty := (Iso80000.Part4.mass).kind

/-- Length — the wheelbase's kind; the catalogue's own 3-1.1. -/
def lengthK : KindOfProperty := (Iso80000.Part3.length).kind

/-- Angular velocity — deliberately *not* licensed to assemble; the catalogue's own
3-12. -/
def angularVelocityK : KindOfProperty := (Iso80000.Part3.angularVelocity).kind

/-- Torque — the interface quantity between a motor and its wheel; the catalogue's own
4-12.2. -/
def torqueK : KindOfProperty := (Iso80000.Part4.torque).kind

/-- The first rover. -/
def rover1 : System := ⟨"rover 1"⟩

/-- The second rover — same design, different object. -/
def rover2 : System := ⟨"rover 2"⟩

/-- The ten parts of a rover. -/
inductive RoverPart
  | chassis | mast
  | wheelFL | wheelFR | wheelRL | wheelRR
  | motorFL | motorFR | motorRL | motorRR
deriving DecidableEq, Repr

/-- A part's name — the right-hand half of its systematic term. -/
def RoverPart.name : RoverPart → String
  | .chassis => "chassis" | .mast => "mast"
  | .wheelFL => "wheel FL" | .wheelFR => "wheel FR"
  | .wheelRL => "wheel RL" | .wheelRR => "wheel RR"
  | .motorFL => "motor FL" | .motorFR => "motor FR"
  | .motorRL => "motor RL" | .motorRR => "motor RR"

/-- A part as a §20 component. -/
def RoverPart.component (p : RoverPart) : Component := ⟨p.name⟩

/-- The object "part `p` of rover `r`" — the identity arithmetic is gated on. -/
def partOf (r : System) (p : RoverPart) : Object := ⟨r.id ++ " / " ++ p.name⟩

/-- The canonical parts list — *the* definition of what rover totals sum over. -/
def parts : List RoverPart :=
  [.chassis, .mast, .wheelFL, .wheelFR, .wheelRL, .wheelRR,
   .motorFL, .motorFR, .motorRL, .motorRR]

/-! ## MR20 — a quantity belongs to a named part of a named system

Dybkær §20 dedicates a kind to a **sort** of system — one catalogue entry serves the whole
fleet — while the *named* system of the requirement is the object index `partOf r p`, which
is where the arithmetic is gated (artifact 2a below: the two chassis masses inhabit
different types). Dedication to the sort, individuation by the object. -/

/-- The sort both rovers instantiate. -/
def roverS : SortOfSystem := ⟨"rover"⟩

/-- *The* catalogue entry for a chassis mass — one dedicated kind for the fleet. -/
def chassisMassDK : DedicatedKind := massK.dedicatedTo roverS (RoverPart.component .chassis)

/-- The systematic term names the sort, as §20 says it should ("given sort of system");
the particular rover is the object index's to carry. -/
theorem chassisMassDK_term : chassisMassDK.systematicTerm = "rover — chassis ; mass" := rfl

/-- The two chassis are distinct *objects* — the distinctness that gates artifact 2a:
rover 1's chassis mass and rover 2's inhabit different quantity types. -/
theorem chassis_objects_distinct : partOf rover1 .chassis ≠ partOf rover2 .chassis := by
  decide

/-! ## MR21 — assembly is licensed per kind, and two-sided -/

/-- The assembly licence: kinds whose part-values sum to the whole's value — the
extensive kinds, curated the way the operator table curates products (the semantic
backing is `PropertyKindCalculus.Extensivity`; the instance is the curation entry).
Mass is registered; angular velocity deliberately is not. -/
class Assembles (k : KindOfProperty) : Prop

/-- Mass assembles: the whole's mass is the sum of the parts'. -/
instance : Assembles massK := ⟨⟩

/-- Summing a per-part reading over *the* parts list into the whole-system quantity.
Available only for licensed kinds, generic in the carrier (MR27). -/
def assemble {k : KindOfProperty} [Assembles k] {R : Type} [Add R] [OfNat R 0]
    (r : System) (q : (p : RoverPart) → IndividualQuantity (partOf r p) k R) :
    IndividualQuantity r k R :=
  ⟨parts.foldr (fun p acc => (q p).magnitude + acc) 0⟩

/-! ## The two rovers' masses -/

/-- Rover 1's part masses (kg): 120 + 8 + 4·3 + 4·1 = 144. -/
noncomputable def rover1Masses :
    (p : RoverPart) → IndividualQuantity (partOf rover1 p) massK ℝ
  | .chassis => ⟨120⟩ | .mast => ⟨8⟩
  | .wheelFL => ⟨3⟩ | .wheelFR => ⟨3⟩ | .wheelRL => ⟨3⟩ | .wheelRR => ⟨3⟩
  | .motorFL => ⟨1⟩ | .motorFR => ⟨1⟩ | .motorRL => ⟨1⟩ | .motorRR => ⟨1⟩

/-- Rover 2's part masses — a lighter chassis; every reading a different object. -/
noncomputable def rover2Masses :
    (p : RoverPart) → IndividualQuantity (partOf rover2 p) massK ℝ
  | .chassis => ⟨118⟩ | .mast => ⟨8⟩
  | .wheelFL => ⟨3⟩ | .wheelFR => ⟨3⟩ | .wheelRL => ⟨3⟩ | .wheelRR => ⟨3⟩
  | .motorFL => ⟨1⟩ | .motorFR => ⟨1⟩ | .motorRL => ⟨1⟩ | .motorRR => ⟨1⟩

/-- Rover 1's stated total mass — the number on the mass-properties sheet. -/
noncomputable def rover1TotalMass : IndividualQuantity rover1 massK ℝ := ⟨144⟩

/-- **Artifact 1 — the total is a theorem.** The stated total equals the assembled sum
of rover 1's own parts. Drop a part from `parts` or change a mass and this proof — not
a definition — is what breaks. -/
theorem rover1_total_is_sum :
    rover1TotalMass.magnitude = (assemble rover1 rover1Masses).magnitude := by
  simp only [rover1TotalMass, assemble, parts, rover1Masses, List.foldr]
  norm_num

/- **Artifact 2a — cross-system contamination does not compile.** Rover 2's chassis
mass cannot even be *added* to rover 1's: the objects differ. -/
#check_failure (rover1Masses .chassis).add DifferenceKind.ofScale (rover2Masses .chassis)

/- **Artifact 2b — nor substituted into the assembly.** The per-part table with rover
2's wheel spliced in does not elaborate. -/
#check_failure assemble rover1
  (fun p => match p with
    | .wheelFL => rover2Masses .wheelFL
    | q => rover1Masses q)

/-- **Artifact 3 — under-counting is caught.** The nine-part sum that silently drops
`wheelRR` is provably not the total: the wheel cannot fall off the books. -/
theorem undercount_caught :
    ([RoverPart.chassis, .mast, .wheelFL, .wheelFR, .wheelRL,
      .motorFL, .motorFR, .motorRL, .motorRR].foldr
        (fun p acc => (rover1Masses p).magnitude + acc) 0)
      ≠ rover1TotalMass.magnitude := by
  simp only [rover1TotalMass, rover1Masses, List.foldr]
  norm_num

/- **The two-sidedness (MR21).** Rover 1's body angular velocity is *not* the sum of
its parts' angular velocities: with no `Assembles angularVelocityK` instance, the sum
fails to elaborate. Mass sums (artifact 1); this must not — and does not. -/
#check_failure fun
    (w : (p : RoverPart) → IndividualQuantity (partOf rover1 p) angularVelocityK ℝ) =>
  assemble rover1 w

/-! ## MR22 — whole-system quantities are not part quantities -/

/-- Rover 1's wheelbase — the *system's* quantity: its object is `rover1` itself, not
any part. (Total angular momentum about the assembly's own centre of mass takes the
same form.) -/
noncomputable def rover1Wheelbase : IndividualQuantity rover1 lengthK ℝ := ⟨0.9⟩

/- A whole-system length and a part-level length do not add: the objects differ. -/
#check_failure fun (x : IndividualQuantity (partOf rover1 .chassis) lengthK ℝ) =>
  rover1Wheelbase.add DifferenceKind.ofScale x

/-! ## MR23 — interface quantities carry both systems they join -/

/-- A quantity of an *interface*: it names the part that produces it and the part that
consumes it, as phantom indices in the manner of `FrameChange`. -/
structure InterfaceQuantity (source sink : Object) (k : KindOfProperty) (R : Type) where
  /-- The quantity crossing the interface. -/
  q : Quantity k R

/-- The front-left drive torque: from motor FL, to wheel FL, by type. -/
noncomputable def motorFLTorque :
    InterfaceQuantity (partOf rover1 .motorFL) (partOf rover1 .wheelFL) torqueK ℝ :=
  ⟨⟨0.8⟩⟩

/-- Delivering an interface torque to the part it names as its sink. -/
def deliver {source : Object} (sink : Object)
    (τ : InterfaceQuantity source sink torqueK ℝ) : IndividualQuantity sink torqueK ℝ :=
  ⟨τ.q.magnitude⟩

/-- The front-left torque reaches the front-left wheel. -/
noncomputable example : IndividualQuantity (partOf rover1 .wheelFL) torqueK ℝ :=
  deliver _ motorFLTorque

/- **The MR23 artifact.** The same torque cannot be delivered to the front-*right*
wheel: the interface names its endpoints and the type refuses the rewiring. -/
#check_failure deliver (partOf rover1 .wheelFR) motorFLTorque

/-! ## MR24 — a dedication carries provenance -/

/-- How a parameter's value entered the model — the systems-engineering tags. -/
inductive Dedication
  | measured | specified | derived | assumed
deriving DecidableEq, Repr

/-- Rover 1's mass provenance: the chassis and mast were weighed; the wheels are at
their spec value; the motor masses are taken from the datasheet — except the rear-right
motor, still an assumption. Greppable, and queryable by `decide`. -/
def rover1MassProvenance : RoverPart → Dedication
  | .chassis => .measured | .mast => .measured
  | .wheelFL => .specified | .wheelFR => .specified
  | .wheelRL => .specified | .wheelRR => .specified
  | .motorFL => .derived | .motorFR => .derived | .motorRL => .derived
  | .motorRR => .assumed

/-- The audit question "what still rests on an assumption?" is a computation. -/
example : parts.filter (fun p => rover1MassProvenance p = .assumed) = [.motorRR] := by
  decide

/-! ## MR27 — the same assembly at another carrier

`assemble` never mentioned `ℝ`; here it executes at `Float32`, ten unit masses to the
whole. -/

/- The assembled total at binary32 executes: 10 × 1 = 10. -/
#guard (assemble (R := Float32) rover1 (fun p => (⟨1.0⟩ : IndividualQuantity (partOf rover1 p) massK Float32))).magnitude == 10.0

end ForPhysLib.Exhibits.TwoRovers
