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

/-
---
hcp: 7
id: hcp-l6
persona: "PhysLib contributor"
layer: PKC
pull: "The pair now has bodies, a coupling spring, and multiple records. What must hold, for which systems or objects?"
improvement: "State requirements over named sorts and particulars, and discharge them with proofs, referents, gates, and audited scope."
concepts:
  - informal: "the pair mass requirement quantifies over pairs"
    formal: "pairS, pairMassOf, pairMass_assembled, and the 3 + 5 = 8 spot check"
    where: "HCP.L6_Requirements#r1_pair_mass"
  - informal: "a whole-only frequency has no body-assembly license"
    formal: "pairNormalModeLicense and the absent-instance requirement"
    where: "HCP.L6_Requirements#r2_no_aggregation"
  - informal: "the rated spring extension is an empirical requirement on P"
    formal: "the datasheet referent, Bool gate, and two P-record spot checks"
    where: "HCP.L6_Requirements#r3_empirical"
  - informal: "a scope must name a sort or nominal object"
    formal: "the rejected bare-real object and non-sort pins"
    where: "HCP.L6_Requirements#invalid_scopes"
  - informal: "every produced model port is governed"
    formal: "the requirement survey, coverage census, and clean gate"
    where: "HCP.L6_Requirements#requirement_census"
artifacts: ['Lean lesson HCP.L6_Requirements', 'Blueprint chapter L6 — What must hold']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 5
disclosure: ['scope a pair-mass theorem over pairS', 'state the absence of pair-frequency aggregation', 'gate an empirical limit over P', 'pin invalid scope declarations', 'census and gate requirement coverage']
owner: 'PKC methodology lead'
state:
  completed: []
---
-/

#doc (Manual) "L6 — What must hold" =>
%%%
tag := "hcp-l6"
%%%

# Synopsis

## Purpose

State what must hold of the refined context as requirements that the build checks. Each `Provenance.Requirement` names the boundary it governs (a `Provenance.Contract`), the output port it is about, and its scope, the objects it quantifies over. R1 and R2 are scoped to the sort `pairS`: R1 is proved by a theorem, and R2 holds because no `Assembles` instance exists. R3 is scoped to pair P and is decided by a gate function over every state of P. The coverage census lists every output port of every boundary with the requirements that govern it, and `#kind_requirement_clean` fails if any port is ungoverned or unchecked.

## PKC vocabulary in scope

New at this step:
- `Provenance.Contract` — a declared model boundary with its members and ports.
- `Provenance.Requirement` (`statement`, `governs`, `port`, `scope`, `witness`, `absent`, `gate`, `referents`, `spotChecks`) — a requirement on a boundary.
- `RequirementKind.provable`, `RequirementKind.empirical` — discharged by a proof, or decided by a gate.
- `RequirementScope.sort`, `RequirementScope.objects` — what a requirement quantifies over.
- `NodeId.result`, `PortDir.output` — which port a requirement governs.
- `#kind_requirement_clean` — the gate that fails on any ungoverned or unchecked output.
- `@[kindReferent]`, `@[kindCounterexample]` — mark an empirical referent and a refuting witness.

Carried from earlier steps: `Composite`, `Decomposition`, `Assembles`, `assemble`, `IndividualQuantity`, `Quantity`, `KindOfProperty`, `SortOfSystem`, `Sorted` (`sortOf`), `Designated`, `massK`, `displacementK`, `angularFrequencyK`.

## Verifiable properties

- R1: for every pair, the pair's mass equals the assembly of its two bodies' masses, proved by a theorem (theorem) `HCP.L6_Requirements#r1_pair_mass`.
- R2: there is no `Assembles pairS normalModeK` instance, so a pair's normal-mode frequency cannot be assembled from its bodies (theorem) `HCP.L6_Requirements#r2_no_aggregation`.
- R3: in every state of pair P, the coupling spring's extension lies within its rated range, decided by the gate `withinRatedRange` (gate) `HCP.L6_Requirements#r3_empirical`.
- `#kind_requirement` rejects with an error a requirement scoped to a bare real number, or to a declaration that is not a `SortOfSystem` (refused) `HCP.L6_Requirements#invalid_scopes`.
- The pinned census lists three governed output ports and none ungoverned or unchecked, and `#kind_requirement_clean` passes (census) `HCP.L6_Requirements#requirement_census`.
- A requirement scoped to pair P, on an accessor that returns a value for every pair, leaves the row for pair Q marked ⚠ UNGOVERNED (census) `HCP.L6_Requirements#scope_gap`.

## Errors prevented

- Unstatable scope: "every pair" or "pair P" written without a declared sort or a nominal object to quantify over (`HCP.L6_Requirements#invalid_scopes`).
- Over-claimed coverage: a requirement about pair P counted as governing pair Q's output (`HCP.L6_Requirements#scope_gap`).
- Ungoverned output: a model output that no requirement governs goes unreported (`HCP.L6_Requirements#requirement_census`).

# Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; the earlier HCP levels have named the pair
sort, its particulars, and its parts.

# Pull

The pair now has two bodies, a coupling spring, and multiple records. What must hold, for which systems or objects? A requirement states its quantification scope, writable because the earlier levels named the pair sort and its nominal particulars. One name is one system: records named P are states, configurations, or rival estimates of that same pair and can be compared; Q is a distinct pair. An object-scoped requirement on P governs every state or record of P, not only records used for a spot check. The full worked requirements example is `examples/Tutorial/HarmonicOscillatorRequirements.lean`; this lesson mirrors its machinery without importing that file.

# Risks at this step

- *Unstatable scope.* A requirement about every coupled pair needs the pair sort, and one about every state of P needs the nominal pair P; without those named systems, it has nowhere to range. The pinned `invalid_scopes` exercise (`HCP.L6_Requirements#invalid_scopes`) rejects a bare real and a name that is not a sort.

# Small rigorous improvement

:::table +header
*
  * Question
  * Context change
  * Attribute change
  * Risk shown
  * PhysLib stage
*
  * The pair now has bodies, a coupling spring, and multiple records. What must hold, for which systems or objects?
  * Give the nominal pair IDs P and Q a `Sorted` instance into `pairS`, and designate bodies and the coupling spring.
  * Pair mass, normal-mode frequency, coupling-spring extension, requirement scope, referent, and gate.
  * An unscoped claim cannot say whether it applies to every pair or to every state of P; a bare real and a non-sort are rejected as scopes.
  * Stage 4 requirements and audits.
:::

# Learning path

:::table +header
*
  * #
  * Do
  * Checked by `HCP.L6_Requirements` anchor
  * Concept disclosed
*
  * 1
  * Assemble the two body masses into a pair mass and state R1 over `pairS`.
  * `r1_pair_mass`
  * The theorem reads the pair's own body quantities; the executable check evaluates 3 + 5 = 8.
*
  * 2
  * State R2 as the absence of the pair-sort assembly license for normal-mode frequency.
  * `r2_no_aggregation`
  * A whole-only frequency does not inherit the body-mass aggregation license.
*
  * 3
  * Scope the coupling-spring rating to P and compare two P records against a marked datasheet limit.
  * `r3_empirical`
  * The empirical requirement is gated by a Bool that names the referent and is spot-checked on two states of P.
*
  * 4
  * Replace P with a bare real, then replace `pairS` with a declaration that is not a sort.
  * `invalid_scopes`
  * Object scope requires a `Sorted` instance; sort scope requires a `SortOfSystem`.
*
  * 5
  * Survey requirements, census every produced model port, and run the clean gate.
  * `requirement_census`
  * Every produced port in these boundaries is governed; the invalid-scope twins are pinned counterexamples.
:::

Worksheet: `HCP/Worksheets/L6_Requirements.lean` · Solution: `HCP/L6_Requirements.lean`

# Lesson

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
ungoverned on a generic pair boundary. An unresolved bearer is an unchecked violation unless
exempted. A `.sort` scope needs an indexed result whose object type has a `Sorted` instance:
R1 and R2's results are borne by the pair whole, and the instance above maps the whole to
`pairS` and each part to its own sort, so the census checks their scope. An object of another
sort is reported ungoverned. A `.decided` scope is checked against a `deciderProof` theorem
proving its decider returns `true` for every result of the governed member; without that
proof the census reports the port unchecked.

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

## Requirement scope

The full worked requirements example is `examples/Tutorial/HarmonicOscillatorRequirements.lean`;
L6 mirrors its Provenance boundaries, witnesses, referents, gates, surveys, and coverage
commands without importing the Tutorial file. The census infers a result port's object
domain from its member's type: R3 covers a P-only result, but leaves Q ungoverned on a
generic pair boundary. An unresolved bearer is an unchecked violation unless exempted. A
`.sort` scope needs an indexed result whose object type has a `Sorted` instance: R1 and R2's
results are borne by the pair whole, and the instance above maps the whole to `pairS` and
each part to its own sort, so the census checks their scope. An object of another sort is
reported ungoverned. A `.decided` scope is checked against a `deciderProof` theorem proving
its decider returns `true` for every result of the governed member; without that proof the
census reports the port unchecked.

# AI assistance contract

- Keep L6 independent, with local nominal `PairId | P | Q`, `Body | A | B`, and the
  coupling spring.
- Preserve nominal identity: one pair name is one system; same-name records are comparable
  states or configurations; P and Q are distinct.
- Keep pair mass on the pair whole and body masses on their body-in-pair bearers.
- Use the `pairS` sort scope for R1 and the singleton object scope containing P for empirical R3.
- Mark the rated limit as an external referent; make the gate mention it and evaluate it on
  two states of P.
- Pin both invalid scopes and run the requirement survey, coverage census, and clean gate.
- Do not import the Tutorial worked example. The full worked example is
  `examples/Tutorial/HarmonicOscillatorRequirements.lean`.
- Leave optional `.decided` scope out of this lesson. If used, provide a `deciderProof`
  theorem proving that its decider returns `true` for every result of the governed member;
  without that proof the census reports the port unchecked.

# Questions to ask the model so far

:::table +header
*
  * Question
  * Check
  * What the verdict means
*
  * What does R1 quantify over?
  * `r1_pair_mass`
  * Every object of sort `pairS`; its theorem relates the assembled pair mass to the masses of the two bodies.
*
  * Does normal-mode frequency sum over the bodies?
  * `r2_no_aggregation`
  * No `Assembles pairS normalModeK` instance exists.
*
  * What does the spring rating govern?
  * `r3_empirical`
  * Every state or record of P; the gate checks two such records against the same datasheet limit.
*
  * Can a bare real or a non-sort name state the scope?
  * `invalid_scopes`
  * No; the object must have a `Sorted` instance and a sort must be a `SortOfSystem`.
*
  * Are all produced ports governed?
  * `requirement_census`
  * Yes; the census is clean and the command enforces that invariant.
:::

# System-context card

:::table +header
*
  * Scope
  * System or component
  * Sort / status
  * L6 requirements
*
  * System
  * Coupled pair P or Q
  * Nominal `PairId`, sorted into `pairS`
  * One name denotes one pair; same-name records are states or configurations, and Q differs from P.
*
  * Part
  * Body A or B
  * Designated body
  * Each body has its own mass bearer within the named pair.
*
  * Part
  * Coupling spring kC
  * Designated spring
  * Its extension is state-indexed and checked against an external rated limit.
*
  * Requirement
  * Pair mass R1
  * `pairS` sort
  * Provable from the pair's two body masses; spot check gives 8 from 3 and 5.
*
  * Requirement
  * Normal-mode frequency R2
  * `pairS` sort
  * Provable negative: no aggregation license for `normalModeK`.
*
  * Requirement
  * Spring range R3
  * Singleton object scope containing P
  * Empirical, gated by the datasheet referent; applies to every P state or record.
*
  * Audit
  * Requirement census
  * Stage 4
  * The valid requirements govern every produced model port; invalid-scope twins are counterexamples.
:::
