/-
# L6 — What must hold

Three scoped requirements, each with evidence at the boundary it governs.

Edit this worksheet in place, build with `lake build HCP.Worksheets.L6_Requirements`,
and compare with the solution at `HCP/L6_Requirements.lean`.
-/

module

public import ForPhysLib.ClassicalMechanics.Feasibility
meta import ForPhysLib.ClassicalMechanics.Feasibility
public import ForPhysLib.ClassicalMechanics.Kinds
meta import ForPhysLib.ClassicalMechanics.Kinds
public import PropertyKindCalculus
meta import PropertyKindCalculus
public import PropertyKindCalculus.KindRequirement
meta import PropertyKindCalculus.KindRequirement

import all Init.Prelude
import all PropertyKindCalculus.Provenance

@[expose] public section Blanket

namespace HCP.Worksheets.L6_Requirements

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)

-- EXERCISE: pair_context
-- GIVEN:
-- TODO: identify each sort and the particulars in the pair context.
inductive PairId | P | Q
deriving DecidableEq, Repr

inductive Body | A | B
deriving DecidableEq, Repr

inductive Spring | kC
deriving DecidableEq, Repr

def pairS : SortOfSystem := ⟨"coupled oscillator pair"⟩
def bodyS : SortOfSystem := ⟨"body"⟩
def springS : SortOfSystem := ⟨"coupling spring"⟩

instance : Sorted PairId := ⟨fun _ => pairS⟩
instance : Sorted Body := ⟨fun _ => bodyS⟩
instance : Sorted Spring := ⟨fun _ => springS⟩

instance : Designated Body where
  designation
    | .A => ⟨"body A"⟩
    | .B => ⟨"body B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

instance : Designated Spring where
  designation
    | .kC => ⟨"coupling spring"⟩
  designation_inj {x y} _ := by cases x; cases y; rfl
-- EXERCISE_END: pair_context

-- GIVEN:
def massK : KindOfProperty := ForPhysLib.ClassicalMechanics.massK
def displacementK : KindOfProperty := ForPhysLib.ClassicalMechanics.displacementK
def normalModeK : KindOfProperty := ForPhysLib.ClassicalMechanics.angularFrequencyK

structure PartOf (π : PairId) where
  part : Body ⊕ Spring
deriving DecidableEq, Repr

instance {π : PairId} : Sorted (Composite pairS (PartOf π)) := ⟨fun
  | .whole => pairS
  | .part ⟨.inl b⟩ => Sorted.sortOf b
  | .part ⟨.inr s⟩ => Sorted.sortOf s⟩

def bodyPart (π : PairId) (b : Body) : PartOf π := ⟨Sum.inl b⟩
def springPart (π : PairId) (s : Spring) : PartOf π := ⟨Sum.inr s⟩

-- EXERCISE: pair_mass_model
-- TODO: use `Assembles` and `DifferenceKind.ofScale` to license pair-mass aggregation.
instance : Assembles pairS massK := ⟨DifferenceKind.ofScale⟩

def bodyParts : Decomposition Body := .union (.atom .A) (.atom .B)

/-- A pair record keeps its measured quantities on their own body or spring. -/
structure PairState (π : PairId) where
  massA : IndividualQuantity (Composite.part (σ := pairS) (bodyPart π .A)) massK Int
  massB : IndividualQuantity (Composite.part (σ := pairS) (bodyPart π .B)) massK Int
  couplingExtension :
    IndividualQuantity (Composite.part (σ := pairS) (springPart π .kC)) displacementK Int

/-- Body A's mass in a particular pair record. -/
def bodyMassA {π : PairId} (state : PairState π) :
    IndividualQuantity (Composite.part (σ := pairS) (bodyPart π .A)) massK Int :=
  state.massA

/-- Body B's mass in a particular pair record. -/
def bodyMassB {π : PairId} (state : PairState π) :
    IndividualQuantity (Composite.part (σ := pairS) (bodyPart π .B)) massK Int :=
  state.massB

/-- The pair mass, assembled from the two nominal body bearers. -/
def pairMassOf {π : PairId}
    (mA : IndividualQuantity
      (Composite.part (σ := pairS) (bodyPart π .A)) massK Int)
    (mB : IndividualQuantity
      (Composite.part (σ := pairS) (bodyPart π .B)) massK Int) :
    IndividualQuantity (Composite.whole : Composite pairS (PartOf π)) massK Int :=
  assemble (k := massK) pairS
    (Composite.whole : Composite pairS (PartOf π))
    (fun b : Body => Composite.part (σ := pairS) (bodyPart π b))
    bodyParts
    (fun b => match b with
      | .A => mA
      | .B => mB)

/-- The pair mass read from one record of the named pair. -/
def pairMassInState {π : PairId} (state : PairState π) :
    IndividualQuantity (Composite.whole : Composite pairS (PartOf π)) massK Int :=
  pairMassOf (bodyMassA state) (bodyMassB state)

/-- The pair mass equals the sum of the masses recorded for its two bodies. -/
theorem pairMass_assembled {π : PairId} (state : PairState π) :
    (pairMassInState state).magnitude = state.massA.magnitude + state.massB.magnitude := by
  rfl

/-- The pair-mass boundary: two body masses in, one pair mass out. -/
def pairMassBoundary : Provenance.Contract NodeId KindRef where
  name := "pair mass from body masses"
  members := [``pairMassOf]
  ports := [
    ⟨(NodeId.binder "mA").within ``pairMassOf, .decl ``massK, .input⟩,
    ⟨(NodeId.binder "mB").within ``pairMassOf, .decl ``massK, .input⟩,
    ⟨NodeId.result.within ``pairMassOf, .decl ``massK, .output⟩
  ]
  exits := []

#kind_contract_decide pairMassBoundary
-- EXERCISE_END: pair_mass_model

-- EXERCISE: r1_pair_mass
-- GIVEN:
/-- A spot check with body A's mass 3 and body B's mass 5. -/
def pairP_earlier : PairState PairId.P where
  massA := ⟨3⟩
  massB := ⟨5⟩
  couplingExtension := ⟨-4⟩

/-- A second record of the same nominal pair P. -/
def pairP_later : PairState PairId.P where
  massA := ⟨3⟩
  massB := ⟨5⟩
  couplingExtension := ⟨6⟩

-- GIVEN:
/-- R1's executable check: the assembled mass is 3 + 5 = 8. -/
def r1Spot : Bool := decide ((pairMassInState pairP_earlier).magnitude = 8)

-- TODO: change the expected 8 to 9, rebuild, read the requirement failure, then revert.
/-- R1: pair mass is the sum of the masses of its two bodies. -/
def r1PairMass : Provenance.Requirement where
  name := "R1"
  statement := "the pair's mass is assembled from the masses of its two bodies"
  kind := .provable
  governs := ``pairMassBoundary
  port := some (NodeId.result.within ``pairMassOf)
  scope := .sort ``pairS
  witness := ``pairMass_assembled
  spotChecks := [``r1Spot]

#kind_requirement r1PairMass
-- EXERCISE_END: r1_pair_mass

-- EXERCISE: r2_no_aggregation
-- TODO: describe the normal-mode boundary and record the absence of an assembly license.
/-- A pair's normal-mode frequency does not have a body-assembly license. -/
def pairNormalModeOf {π : PairId}
    (ω : IndividualQuantity
      (Composite.whole : Composite pairS (PartOf π)) normalModeK Int) :
    IndividualQuantity (Composite.whole : Composite pairS (PartOf π)) normalModeK Int := by
  sorry

/-- The normal-mode boundary has no operation over the bodies. -/
def pairNormalModeBoundary : Provenance.Contract NodeId KindRef where
  name := "pair normal-mode frequency"
  members := [``pairNormalModeOf]
  ports := [
    ⟨(NodeId.binder "ω").within ``pairNormalModeOf, .decl ``normalModeK, .input⟩,
    ⟨NodeId.result.within ``pairNormalModeOf, .decl ``normalModeK, .output⟩
  ]
  exits := []

#kind_contract_decide pairNormalModeBoundary

/-- The aggregation license whose absence is R2's evidence. -/
def pairNormalModeLicense : Prop := Assembles pairS normalModeK

-- TODO: state R2 and inspect its output.
/-- R2: the normal-mode frequency is a whole property, not a sum of body frequencies. -/
def r2NormalMode : Provenance.Requirement := by
  exact {
    name := "R2"
    statement := "the pair's normal-mode frequency is not assembled by summing body frequencies"
    kind := .provable
    governs := ``pairNormalModeBoundary
    port := some (NodeId.result.within ``pairNormalModeOf)
    scope := .sort ``pairS
    absent := ``pairNormalModeLicense
  }

#kind_requirement r2NormalMode
-- EXERCISE_END: r2_no_aggregation

-- EXERCISE: r3_empirical
-- TODO: register the rated range as an empirical requirement over the P-only result.
/-- P's state accessor keeps coupling extension on that pair's spring bearer. -/
def couplingExtensionOfP (state : PairState .P) :
    IndividualQuantity (Composite.part (σ := pairS) (springPart .P .kC)) displacementK Int := by
  exact state.couplingExtension

/-- The coupling-extension boundary is limited to the particular pair P. -/
def couplingExtensionBoundary : Provenance.Contract NodeId KindRef where
  name := "coupling-spring extension"
  members := [``couplingExtensionOfP]
  ports := [
    ⟨((NodeId.binder "state").field "massA").within ``couplingExtensionOfP,
      .decl ``massK, .input⟩,
    ⟨((NodeId.binder "state").field "massB").within ``couplingExtensionOfP,
      .decl ``massK, .input⟩,
    ⟨((NodeId.binder "state").field "couplingExtension").within ``couplingExtensionOfP,
      .decl ``displacementK, .input⟩,
    ⟨NodeId.result.within ``couplingExtensionOfP, .decl ``displacementK, .output⟩
  ]
  exits := []

#kind_contract_decide couplingExtensionBoundary

-- GIVEN:
/-- The spring's rated extension, from its datasheet. -/
@[kindReferent "coupling-spring manufacturer datasheet"]
def couplingSpringRatedExtension : Quantity displacementK Int := ⟨6⟩

/-- The rated-range predicate applies to every state or record of P. -/
def withinRatedRange (s : PairState .P) : Bool :=
  decide (Int.natAbs (couplingExtensionOfP s).magnitude ≤
    Int.natAbs couplingSpringRatedExtension.magnitude)

def pairP_earlierWithinRatedRange : Bool := withinRatedRange pairP_earlier
def pairP_laterWithinRatedRange : Bool := withinRatedRange pairP_later

/-- R3: every state or record of P must keep the spring within its rated range. -/
def r3CouplingSpringRange : Provenance.Requirement where
  name := "R3"
  statement := "P's coupling-spring extension stays within its rated range in every state or record"
  kind := .empirical
  governs := ``couplingExtensionBoundary
  port := some (NodeId.result.within ``couplingExtensionOfP)
  scope := .objects [``PairId.P]
  referents := [``couplingSpringRatedExtension]
  gate := ``withinRatedRange
  spotChecks := [``pairP_earlierWithinRatedRange, ``pairP_laterWithinRatedRange]

#kind_requirement r3CouplingSpringRange
-- EXERCISE_END: r3_empirical

-- EXERCISE: invalid_scopes
-- GIVEN:
/-- A bare real is not a nominal object with a sort. -/
def someBareReal : ℝ := 7

/-- A name whose declaration is not a system sort. -/
def notASort : Nat := 1

-- TODO: uncomment each command to see why those scopes are rejected.
-- @[kindCounterexample]
-- def r3BareRealScope : Provenance.Requirement :=
--   { r3CouplingSpringRange with scope := .objects [``someBareReal] }
-- #kind_requirement r3BareRealScope
-- @[kindCounterexample]
-- def r3NotASortScope : Provenance.Requirement :=
--   { r3CouplingSpringRange with scope := .sort ``notASort }
-- #kind_requirement r3NotASortScope
-- EXERCISE_END: invalid_scopes

-- EXERCISE: requirement_census
-- TODO: run the census commands and compare their output with the solution.
#kind_requirements HCP.Worksheets.L6_Requirements
#kind_requirement_coverage HCP.Worksheets.L6_Requirements
#kind_requirement_clean HCP.Worksheets.L6_Requirements
-- EXERCISE_END: requirement_census

end HCP.Worksheets.L6_Requirements

namespace HCP.Worksheets.L6_ScopeGap

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)
open HCP.Worksheets.L6_Requirements

-- EXERCISE: scope_gap
-- TODO: make the result generic over the pair, then inspect the P-only coverage gap.
/-- A generic pair-state result retains its pair index. -/
def couplingExtensionOfAny {π : PairId} (state : PairState π) :
    IndividualQuantity (Composite.part (σ := pairS) (springPart π .kC)) displacementK Int := by
  sorry

def couplingExtensionAnyBoundary : Provenance.Contract NodeId KindRef where
  name := "coupling-spring extension, generic pair"
  members := [``couplingExtensionOfAny]
  ports := [
    ⟨((NodeId.binder "state").field "massA").within ``couplingExtensionOfAny,
      .decl ``massK, .input⟩,
    ⟨((NodeId.binder "state").field "massB").within ``couplingExtensionOfAny,
      .decl ``massK, .input⟩,
    ⟨((NodeId.binder "state").field "couplingExtension").within ``couplingExtensionOfAny,
      .decl ``displacementK, .input⟩,
    ⟨NodeId.result.within ``couplingExtensionOfAny, .decl ``displacementK, .output⟩
  ]
  exits := []

#kind_contract_decide couplingExtensionAnyBoundary

def r3POnlyOnAny : Provenance.Requirement :=
  { HCP.Worksheets.L6_Requirements.r3CouplingSpringRange with
    governs := ``couplingExtensionAnyBoundary
    port := some (NodeId.result.within ``couplingExtensionOfAny) }

#kind_requirement r3POnlyOnAny
#kind_requirement_coverage HCP.Worksheets.L6_ScopeGap
-- EXERCISE_END: scope_gap

end HCP.Worksheets.L6_ScopeGap

end Blanket
