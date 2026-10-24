import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "HCP.L6_Requirements"

#doc (Manual) "L6 — What must hold" =>
%%%
tag := "hcp-l6"
%%%

The pair now has two bodies, a coupling spring, and multiple records. What must hold,
for which systems or objects? A requirement states its quantification scope. That scope is
writable because the earlier levels named the pair sort and its nominal particulars.

One name is one system: records named P are states, configurations, or rival estimates of
that same pair and can be compared; Q is a distinct pair. An object-scoped requirement on P
governs every state or record of P, not only the records used for a spot check. The full
worked requirements example is `examples/Tutorial/HarmonicOscillatorRequirements.lean`;
this lesson mirrors its machinery without importing that file.

# Risks at this step

- *Unstatable scope.* A requirement about every coupled pair needs the pair sort, and one about every state of P needs the nominal pair P; without those named systems, it has nowhere to range. The pinned `invalid_scopes` exercise rejects a bare real and a name that is not a sort.

_1. Pair mass._ R1 quantifies over every object of `pairS`. Its pair mass is assembled from
the body masses indexed to the named pair, and a witness theorem plus an executable check
shows 3 + 5 = 8:

```anchor pair_context
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
```

The body masses remain individual quantities on their body-in-pair bearers. Only pair
mass has the `Assembles pairS massK` license:

```anchor pair_mass_model
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
```

```anchor r1_pair_mass
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

/-- R1's executable check: the assembled mass is 3 + 5 = 8. -/
def r1Spot : Bool := decide ((pairMassInState pairP_earlier).magnitude = 8)

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

/--
info: kind requirement 'R1' (provable) on 'pair mass from body masses'
statement: the pair's mass is assembled from the masses of its two bodies
governs: 'pair mass from body masses' at pairMassOf/result
scope: sort HCP.L6_Requirements.pairS
witness: HCP.L6_Requirements.pairMass_assembled
axioms: propext, Classical.choice, Quot.sound
spot check: HCP.L6_Requirements.r1Spot = true
-/
#guard_msgs (whitespace := lax) in #kind_requirement r1PairMass
```

_2. Whole-only frequency._ R2 is provable by absence: the pair sort has no assembly
license for the normal-mode kind. The input and output of the boundary remain attached to
the pair whole; the absence rules out summing body frequencies:

```anchor r2_no_aggregation
/-- A pair's normal-mode frequency does not have a body-assembly license. -/
def pairNormalModeOf {π : PairId}
    (ω : IndividualQuantity
      (Composite.whole : Composite pairS (PartOf π)) normalModeK Int) :
    IndividualQuantity (Composite.whole : Composite pairS (PartOf π)) normalModeK Int :=
  ω

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

/-- R2: the normal-mode frequency is a whole property, not a sum of body frequencies. -/
def r2NormalMode : Provenance.Requirement where
  name := "R2"
  statement := "the pair's normal-mode frequency is not assembled by summing body frequencies"
  kind := .provable
  governs := ``pairNormalModeBoundary
  port := some (NodeId.result.within ``pairNormalModeOf)
  scope := .sort ``pairS
  absent := ``pairNormalModeLicense

/--
info: kind requirement 'R2' (provable) on 'pair normal-mode frequency'
statement: the pair's normal-mode frequency is not assembled by summing body frequencies
governs: 'pair normal-mode frequency' at pairNormalModeOf/result
scope: sort HCP.L6_Requirements.pairS
absent: no instance of HCP.L6_Requirements.pairNormalModeLicense
-/
#guard_msgs (whitespace := lax) in #kind_requirement r2NormalMode
```

_3. Empirical range._ R3 is scoped to the nominal object P. Under the one-name-one-system
rule, it governs every state or record of P; the predicate is defined for every P record,
and two Bool spot checks run it against the spring's datasheet limit. The gate mentions the
referent, so the requirement is discharged rather than attested:

```anchor r3_empirical
/-- P's state accessor keeps coupling extension on that pair's spring bearer. -/
def couplingExtensionOfP (state : PairState .P) :
    IndividualQuantity (Composite.part (σ := pairS) (springPart .P .kC))
      displacementK Int :=
  state.couplingExtension

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

/--
info: kind requirement 'R3' (empirical) on 'coupling-spring extension'
statement: P's coupling-spring extension stays within its rated range in every state or record
governs: 'coupling-spring extension' at couplingExtensionOfP/result
scope: objects HCP.L6_Requirements.PairId.P
referent: HCP.L6_Requirements.couplingSpringRatedExtension — coupling-spring manufacturer datasheet
gate: HCP.L6_Requirements.withinRatedRange
spot check: HCP.L6_Requirements.pairP_earlierWithinRatedRange = true
spot check: HCP.L6_Requirements.pairP_laterWithinRatedRange = true
-/
#guard_msgs (whitespace := lax) in #kind_requirement r3CouplingSpringRange
```

The two failed scopes are counterexamples, so the survey can pin their diagnostics without
counting them as valid requirements. A bare value is not a nominal object, and a name is
not a sort merely because it is a declaration:

```anchor invalid_scopes
/-- A bare real is not a nominal object with a sort. -/
def someBareReal : ℝ := 7

/-- A name whose declaration is not a system sort. -/
def notASort : Nat := 1

@[kindCounterexample]
def r3BareRealScope : Provenance.Requirement :=
  { r3CouplingSpringRange with scope := .objects [``someBareReal] }

/--
error: the scope object 'HCP.L6_Requirements.someBareReal' is of type 'ℝ', which has no
  'Sorted' instance — an object of no sort is a bare value, not a particular a requirement can quantify over
-/
#guard_msgs (whitespace := lax) in #kind_requirement r3BareRealScope

@[kindCounterexample]
def r3NotASortScope : Provenance.Requirement :=
  { r3CouplingSpringRange with scope := .sort ``notASort }

/--
error: the scope 'HCP.L6_Requirements.notASort' is not a 'SortOfSystem' — a scope over a sort names the sort, and the objects reach it through their 'Sorted' instance
-/
#guard_msgs (whitespace := lax) in #kind_requirement r3NotASortScope
```

_4. Census._ The valid requirements are surveyed, every produced model port has a
governing requirement, and the clean command enforces that result. The census infers a
result port's object domain from its member's type: R3 covers a P-only result, but leaves Q
ungoverned on a generic pair boundary. A missing index or unresolved bearer is an unchecked
violation unless exempted; `.sort` and `.decided` remain unchecked against the result
index. The optional `.decided` scope is omitted because the checker only verifies that its
named decider exists; it does not validate that the declaration is a predicate selecting a
subset of pair objects:

```anchor requirement_census
/--
info: kind requirements — 3 requirement(s), 2 exempted: 2 provable, 1 empirical, 0 attested
  HCP.L6_Requirements.r1PairMass: 'R1' (provable) on 'pair mass from body masses' — by HCP.L6_Requirements.pairMass_assembled
  HCP.L6_Requirements.r2NormalMode: 'R2' (provable) on 'pair normal-mode frequency' — absent HCP.L6_Requirements.pairNormalModeLicense
  HCP.L6_Requirements.r3CouplingSpringRange: 'R3' (empirical) on 'coupling-spring extension' — gated by HCP.L6_Requirements.withinRatedRange
  ⊘ HCP.L6_Requirements.r3BareRealScope: counterexample, exempted
  ⊘ HCP.L6_Requirements.r3NotASortScope: counterexample, exempted
-/
#guard_msgs (whitespace := lax) in #kind_requirements HCP.L6_Requirements

/--
info: requirement coverage:
[governed] HCP.L6_Requirements.couplingExtensionBoundary ('coupling-spring extension') couplingExtensionOfP/result — by 'R3'
[governed] HCP.L6_Requirements.pairMassBoundary ('pair mass from body masses') pairMassOf/result — by 'R1'
[governed] HCP.L6_Requirements.pairNormalModeBoundary ('pair normal-mode frequency') pairNormalModeOf/result — by 'R2'
3 row(s) over 3 model boundary(ies): 3 governed — clean
requirements: 2 provable, 1 empirical, 0 attested
-/
#guard_msgs (whitespace := lax) in #kind_requirement_coverage HCP.L6_Requirements

#kind_requirement_clean HCP.L6_Requirements
```

All three requirements are discharged: R1 has a theorem and a spot check, R2 has an
absent aggregation license, and R3 has a referent-backed gate. The invalid scopes remain
visible as counterexamples rather than silently entering the requirement census.

The sibling-namespace probe shows the scope gap directly: a P-scoped requirement governs
P's result while the generic pair boundary leaves Q ungoverned.

```anchor scope_gap
/-- A generic pair-state result retains its pair index. -/
def couplingExtensionOfAny {π : PairId} (state : PairState π) :
    IndividualQuantity (Composite.part (σ := pairS) (springPart π .kC)) displacementK Int :=
  state.couplingExtension

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
  { HCP.L6_Requirements.r3CouplingSpringRange with
    governs := ``couplingExtensionAnyBoundary
    port := some (NodeId.result.within ``couplingExtensionOfAny) }

/--
info: kind requirement 'R3' (empirical) on 'coupling-spring extension, generic pair'
statement: P's coupling-spring extension stays within its rated range in every state or record
governs: 'coupling-spring extension, generic pair' at couplingExtensionOfAny/result
scope: objects HCP.L6_Requirements.PairId.P
referent: HCP.L6_Requirements.couplingSpringRatedExtension — coupling-spring manufacturer datasheet
gate: HCP.L6_Requirements.withinRatedRange
spot check: HCP.L6_Requirements.pairP_earlierWithinRatedRange = true
spot check: HCP.L6_Requirements.pairP_laterWithinRatedRange = true
-/
#guard_msgs (whitespace := lax) in #kind_requirement r3POnlyOnAny

/--
info: requirement coverage:
[governed] HCP.L6_ScopeGap.couplingExtensionAnyBoundary ('coupling-spring extension, generic pair') couplingExtensionOfAny/result for HCP.L6_Requirements.PairId.P — by 'R3'
⚠ UNGOVERNED HCP.L6_ScopeGap.couplingExtensionAnyBoundary ('coupling-spring extension, generic pair') couplingExtensionOfAny/result for HCP.L6_Requirements.PairId.Q — 'R3' scoped to HCP.L6_Requirements.PairId.P
2 row(s) over 1 model boundary(ies): 1 governed, 1 UNGOVERNED — requirement-coverage violation
requirements: 0 provable, 1 empirical, 0 attested
-/
#guard_msgs (whitespace := lax) in #kind_requirement_coverage HCP.L6_ScopeGap
```
