/-
# Validation probes — the requirement (`Provenance.Requirement`, `#kind_requirement`)

A theorem edge says how two boundaries relate; a requirement says what a boundary's
quantities must satisfy and by what evidence. `#kind_requirement` checks everything around
that statement and throws on every failure — so the command is the report and the gate at
once — and the probes below pin its acceptances and its refusals.

One probe world, Mathlib-free: a model that doubles its argument, a specification whose one
member computes the bound (three times the argument), a `boundedBy` edge between them, a
sort with two sorted objects, a license class with one instance, a datasheet referent and
a gate against it. On it, each shape the construct carries is accepted: a provable
requirement through the edge with a spot check and an object scope; one by a bare theorem
over a sort; a negative one by the absence of a license; an empirical one by a gate against
a marked referent; and an attestation of either kind. Then the refusals, one per check:
the governed boundary a specification; a port the boundary does not declare; a scope
object with no `Sorted` instance, a scope sort that is not one, an empty object list; a
provable requirement that lists referents, names a gate, names nothing, or is attested
beside its discharge; a witness that is a definition; an edge from the wrong boundary; an
edge to a model boundary; a witness statement naming a referent; an absence that is
present, and one that is not a license; an empirical requirement naming a witness, no
referent, no gate, an unmarked referent, or a gate that mentions no referent; a spot check
that is false, and one that is not a `Bool`. The survey, the census and the gate close the
file, with the two marks' own refusals.
-/

module

public import PropertyKindCalculus.KindRequirement
meta import PropertyKindCalculus.KindRequirement

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.KindRequirement

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)

/-! ## The probe world -/

/-- A probe kind — the model's argument. -/
def aK : KindOfProperty := { id := "requirement probe a", scale := .ratio }
/-- A probe kind — the model's answer. -/
def bK : KindOfProperty := { id := "requirement probe b", scale := .ratio }

/-- The model: doubles its argument. -/
def model (x : Quantity aK Int) : Quantity bK Int := ⟨2 * x.magnitude⟩

/-- The specification: the bound the model's answer must stay under. -/
def bound (x : Quantity aK Int) : Quantity bK Int := ⟨3 * x.magnitude⟩

/-- The domain the bound holds on, named so the edge can list it. -/
def NonNeg (x : Quantity aK Int) : Prop := 0 ≤ x.magnitude

/-- The witness: on the domain, the model never exceeds the specification. -/
theorem model_le_bound (x : Quantity aK Int) (h : NonNeg x) :
    (model x).magnitude ≤ (bound x).magnitude := by
  unfold NonNeg at h
  show 2 * x.magnitude ≤ 3 * x.magnitude
  omega

/-- The model's declared boundary. -/
def modelBoundary : Provenance.Contract NodeId KindRef where
  name := "requirement probe model"
  members := [``model]
  ports := [⟨(NodeId.binder "x").within ``model, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``model, .decl ``bK, .output⟩]
  exits := []

/-- The specification's declared boundary — the same structure, the other role. -/
def boundSpec : Provenance.Contract NodeId KindRef where
  name := "requirement probe specification"
  members := [``bound]
  ports := [⟨(NodeId.binder "x").within ``bound, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``bound, .decl ``bK, .output⟩]
  exits := []
  role := .specification

/-- The same member declared as a model boundary — for the refusal below. -/
def boundAsModel : Provenance.Contract NodeId KindRef where
  name := "requirement probe bound, as a model"
  members := [``bound]
  ports := [⟨(NodeId.binder "x").within ``bound, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``bound, .decl ``bK, .output⟩]
  exits := []

/-- A boundary nothing governs. -/
def orphan : Provenance.Contract NodeId KindRef where
  name := "requirement probe orphan"
  members := [``model]
  ports := [⟨(NodeId.binder "x").within ``model, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``model, .decl ``bK, .output⟩]
  exits := []

/-- A boundary declared requirement-free, in the author's words. -/
@[kindRequirementFree "pure data movement: nothing is demanded of a copy"]
def freeBoundary : Provenance.Contract NodeId KindRef where
  name := "requirement probe free"
  members := [``model]
  ports := [⟨(NodeId.binder "x").within ``model, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``model, .decl ``bK, .output⟩]
  exits := []

/-! The role prints in the contract's own report; a model boundary says nothing. -/

/--
info: kind contract over 1 steps:
contract 'requirement probe specification': 2 ports, 0 exits
role: specification
boundary agrees: true
-/
#guard_msgs in #kind_contract boundSpec

/-- The edge: the model is bounded by the specification. -/
def modelBounded : Provenance.Relation where
  left := ``modelBoundary
  right := ``boundSpec
  kind := .boundedBy
  witness := ``model_le_bound
  claim := "the model's answer never exceeds the specification's bound"
  hypotheses := [``NonNeg]

/-- The edge read the other way — a valid edge, but not from the governed boundary. -/
def boundedReversed : Provenance.Relation where
  left := ``boundSpec
  right := ``modelBoundary
  kind := .boundedBy
  witness := ``model_le_bound
  hypotheses := [``NonNeg]

/-- The edge to the bound declared as a model. -/
def boundedByModel : Provenance.Relation where
  left := ``modelBoundary
  right := ``boundAsModel
  kind := .boundedBy
  witness := ``model_le_bound
  hypotheses := [``NonNeg]

/-- A sort, and an object type whose objects are of it. -/
def probeS : SortOfSystem := ⟨"requirement probe sort"⟩

inductive Thing | one | two
deriving DecidableEq, Repr

instance : Sorted Thing := ⟨fun _ => probeS⟩

/-- An object type of no sort. -/
inductive Loose | it
deriving DecidableEq, Repr

/-- A license: a class the environment may or may not hold an instance of. -/
class ProbeLicense (k : KindOfProperty) : Prop where

instance : ProbeLicense aK := ⟨⟩

/-- The license that must be absent — and is. -/
def noLicenseB : Prop := ProbeLicense bK

/-- The license that must be absent — and is not. -/
def licenseA : Prop := ProbeLicense aK

/-- The spot check: the bound holds on an operational input. -/
def spot : Bool := (model ⟨4⟩).magnitude ≤ (bound ⟨4⟩).magnitude

/-- A spot check that fails. -/
def spotFalse : Bool := (model ⟨4⟩).magnitude ≤ 1

/-- The datasheet's ceiling for the argument — what the model does not define. -/
@[kindReferent "the probe's datasheet"]
def aMax : Quantity aK Int := ⟨10⟩

/-- The gate: within the datasheet's range. -/
def inRange (x : Quantity aK Int) : Bool := x.magnitude ≤ aMax.magnitude

/-- A gate against a threshold of the model's own. -/
def inModelRange (x : Quantity aK Int) : Bool := x.magnitude ≤ 10

/-- A theorem about the model that names the referent — the demarcation's refusal. -/
theorem model_le_referent (x : Quantity aK Int) (h : x.magnitude ≤ 5) :
    (model x).magnitude ≤ aMax.magnitude := by
  show 2 * x.magnitude ≤ 10
  omega

/-! ## The acceptances -/

namespace Good

/-- Provable through the edge, with a spot check, over named objects. -/
def p1 : Provenance.Requirement where
  name := "P1"
  statement := "the model's answer never exceeds the specification's bound"
  kind := .provable
  governs := ``modelBoundary
  port := some (NodeId.result.within ``model)
  scope := .objects [``Thing.one, ``Thing.two]
  witness := ``modelBounded
  spotChecks := [``spot]

/--
info: kind requirement 'P1' (provable) on 'requirement probe model'
statement: the model's answer never exceeds the specification's bound
governs: 'requirement probe model' at model/result
scope: objects PropertyKindCalculus.Tests.KindRequirement.Thing.one, PropertyKindCalculus.Tests.KindRequirement.Thing.two
edge: PropertyKindCalculus.Tests.KindRequirement.modelBounded — 'requirement probe model' bounded by 'requirement probe specification'
witness: PropertyKindCalculus.Tests.KindRequirement.model_le_bound
spot check: PropertyKindCalculus.Tests.KindRequirement.spot = true
-/
#guard_msgs in #kind_requirement p1

/-- Provable by a bare theorem, over every object of the sort. -/
def p2 : Provenance.Requirement where
  name := "P2"
  statement := "the model's answer is at most three times its argument"
  kind := .provable
  governs := ``modelBoundary
  scope := .sort ``probeS
  witness := ``model_le_bound

/--
info: kind requirement 'P2' (provable) on 'requirement probe model'
statement: the model's answer is at most three times its argument
governs: every produced port of 'requirement probe model'
scope: sort PropertyKindCalculus.Tests.KindRequirement.probeS
witness: PropertyKindCalculus.Tests.KindRequirement.model_le_bound
axioms: propext, Quot.sound
-/
#guard_msgs in #kind_requirement p2

/-- Negative: discharged by the absence of a license. -/
def p3 : Provenance.Requirement where
  name := "P3"
  statement := "the answer's kind carries no probe license"
  kind := .provable
  governs := ``modelBoundary
  absent := ``noLicenseB

/--
info: kind requirement 'P3' (provable) on 'requirement probe model'
statement: the answer's kind carries no probe license
governs: every produced port of 'requirement probe model'
scope: all
absent: no instance of PropertyKindCalculus.Tests.KindRequirement.noLicenseB
-/
#guard_msgs in #kind_requirement p3

/-- Empirical: gated against the datasheet, over the objects a decider selects. -/
def e1 : Provenance.Requirement where
  name := "E1"
  statement := "the argument stays within the datasheet's range"
  kind := .empirical
  governs := ``modelBoundary
  port := some ((NodeId.binder "x").within ``model)
  scope := .decided ``inRange
  referents := [``aMax]
  gate := ``inRange

/--
info: kind requirement 'E1' (empirical) on 'requirement probe model'
statement: the argument stays within the datasheet's range
governs: 'requirement probe model' at model/x
scope: decided by PropertyKindCalculus.Tests.KindRequirement.inRange
referent: PropertyKindCalculus.Tests.KindRequirement.aMax — the probe's datasheet
gate: PropertyKindCalculus.Tests.KindRequirement.inRange
-/
#guard_msgs in #kind_requirement e1

/-- Attested, provable: the theorem is owed. -/
def a1 : Provenance.Requirement where
  name := "A1"
  statement := "the answer is non-negative on non-negative arguments"
  kind := .provable
  governs := ``modelBoundary
  attested := "the proof waits on the carrier's order lemmas"

/--
info: kind requirement 'A1' (provable) on 'requirement probe model'
statement: the answer is non-negative on non-negative arguments
governs: every produced port of 'requirement probe model'
scope: all
attested: the proof waits on the carrier's order lemmas
-/
#guard_msgs in #kind_requirement a1

/-- Attested, empirical: the referent is named, the gate is owed. -/
def a2 : Provenance.Requirement where
  name := "A2"
  statement := "the answer agrees with the reference instrument within its tolerance"
  kind := .empirical
  governs := ``modelBoundary
  referents := [``aMax]
  attested := "no reference run yet"

/--
info: kind requirement 'A2' (empirical) on 'requirement probe model'
statement: the answer agrees with the reference instrument within its tolerance
governs: every produced port of 'requirement probe model'
scope: all
referent: PropertyKindCalculus.Tests.KindRequirement.aMax — the probe's datasheet
attested: no reference run yet
-/
#guard_msgs in #kind_requirement a2

end Good

/-! ## The refusals

Each is checked by `#kind_requirement` and refused; all but the two the survey below renders
are `@[kindCounterexample]`, so the census and the survey list them as exempted rather than
as requirements — a falsification probe stands beside the gate it exercises. -/

namespace Bad

/-- A requirement governs a model, and a specification is what it is checked against. -/
def governsASpecification : Provenance.Requirement where
  name := "B1"
  statement := "the bound is bounded"
  kind := .provable
  governs := ``boundSpec
  witness := ``model_le_bound

/--
error: 'B1' governs 'requirement probe specification', which is a specification boundary — a requirement governs a model boundary; a specification is what it is checked against
-/
#guard_msgs in #kind_requirement governsASpecification

/-- The port is one the boundary declares. -/
@[kindCounterexample]
def portUndeclared : Provenance.Requirement where
  name := "B2"
  statement := "something of a port that is not there"
  kind := .provable
  governs := ``modelBoundary
  port := some ((NodeId.binder "y").within ``model)
  witness := ``model_le_bound

/--
error: 'B2' governs the port 'model/y', which 'requirement probe model' does not declare
-/
#guard_msgs in #kind_requirement portUndeclared

/-- A scope object is of some sort. -/
@[kindCounterexample]
def objectOfNoSort : Provenance.Requirement where
  name := "B3"
  statement := "something of a bare value"
  kind := .provable
  governs := ``modelBoundary
  scope := .objects [``Loose.it]
  witness := ``model_le_bound

/--
error: the scope object 'PropertyKindCalculus.Tests.KindRequirement.Loose.it' is of type 'Loose', which has no 'Sorted' instance — an object of no sort is a bare value, not a particular a requirement can quantify over
-/
#guard_msgs in #kind_requirement objectOfNoSort

/-- A scope sort is a `SortOfSystem`. -/
@[kindCounterexample]
def sortIsNotOne : Provenance.Requirement where
  name := "B4"
  statement := "something over a kind"
  kind := .provable
  governs := ``modelBoundary
  scope := .sort ``aK
  witness := ``model_le_bound

/--
error: the scope 'PropertyKindCalculus.Tests.KindRequirement.aK' is not a 'SortOfSystem' — a scope over a sort names the sort, and the objects reach it through their 'Sorted' instance
-/
#guard_msgs in #kind_requirement sortIsNotOne

/-- An empty object list is a vacuous scope. -/
@[kindCounterexample]
def noObjects : Provenance.Requirement where
  name := "B5"
  statement := "something of nothing"
  kind := .provable
  governs := ``modelBoundary
  scope := .objects []
  witness := ``model_le_bound

/--
error: 'B5' quantifies over no object — an empty object list is a vacuous scope; use `.all` for every object the boundary is evaluated for
-/
#guard_msgs in #kind_requirement noObjects

/-- A provable requirement names what the model defines. -/
@[kindCounterexample]
def provableWithReferents : Provenance.Requirement where
  name := "B6"
  statement := "the answer is bounded by the datasheet"
  kind := .provable
  governs := ``modelBoundary
  witness := ``model_le_bound
  referents := [``aMax]

/--
error: 'B6' is provable but lists referents — a statement that names what the model does not define is empirical
-/
#guard_msgs in #kind_requirement provableWithReferents

/-- A provable requirement's runtime evidence is a spot check, not a gate. -/
@[kindCounterexample]
def provableWithGate : Provenance.Requirement where
  name := "B7"
  statement := "the answer is bounded"
  kind := .provable
  governs := ``modelBoundary
  witness := ``model_le_bound
  gate := ``inRange

/--
error: 'B7' is provable but names a gate — a gate decides against a referent; a provable requirement's runtime evidence is a spot check
-/
#guard_msgs in #kind_requirement provableWithGate

/-- A provable requirement is discharged or attested. -/
@[kindCounterexample]
def provableWithNothing : Provenance.Requirement where
  name := "B8"
  statement := "the answer is bounded"
  kind := .provable
  governs := ``modelBoundary

/--
error: 'B8' is provable but names no witness and no absence — a provable requirement is discharged by a theorem, or attested with a reason
-/
#guard_msgs in #kind_requirement provableWithNothing

/-- An attestation defers a discharge; it does not stand beside one. -/
@[kindCounterexample]
def attestedAndDischarged : Provenance.Requirement where
  name := "B9"
  statement := "the answer is bounded"
  kind := .provable
  governs := ``modelBoundary
  witness := ``model_le_bound
  attested := "still thinking"

/--
error: 'B9' is attested and discharged at once — an attestation defers a discharge, so drop it where the discharge exists
-/
#guard_msgs in #kind_requirement attestedAndDischarged

/-- A definition asserts nothing. -/
@[kindCounterexample]
def witnessIsADefinition : Provenance.Requirement where
  name := "B10"
  statement := "the answer is bounded"
  kind := .provable
  governs := ``modelBoundary
  witness := ``model

/--
error: the witness 'PropertyKindCalculus.Tests.KindRequirement.model' is neither a theorem nor a theorem edge — a provable requirement is discharged by a proof, and a definition asserts nothing
-/
#guard_msgs in #kind_requirement witnessIsADefinition

/-- The edge starts at the governed boundary. -/
@[kindCounterexample]
def edgeFromElsewhere : Provenance.Requirement where
  name := "B11"
  statement := "the answer is bounded"
  kind := .provable
  governs := ``modelBoundary
  witness := ``boundedReversed

/--
error: the edge 'PropertyKindCalculus.Tests.KindRequirement.boundedReversed' is between 'requirement probe specification' and 'requirement probe model', and its left side is not the governed boundary 'requirement probe model' — a requirement is checked against a specification from the boundary it governs
-/
#guard_msgs in #kind_requirement edgeFromElsewhere

/-- The edge ends at a specification. -/
@[kindCounterexample]
def edgeToAModel : Provenance.Requirement where
  name := "B12"
  statement := "the answer is bounded"
  kind := .provable
  governs := ``modelBoundary
  witness := ``boundedByModel

/--
error: the right side of the edge 'PropertyKindCalculus.Tests.KindRequirement.boundedByModel' is 'requirement probe bound, as a model', a model boundary — the bound a requirement is checked against is a specification boundary (`role := .specification`)
-/
#guard_msgs in #kind_requirement edgeToAModel

/-- The demarcation: a provable statement names no referent. -/
@[kindCounterexample]
def witnessNamesAReferent : Provenance.Requirement where
  name := "B13"
  statement := "the answer is bounded by the datasheet"
  kind := .provable
  governs := ``modelBoundary
  witness := ``model_le_referent

/--
error: 'B13' is provable, but the statement of 'PropertyKindCalculus.Tests.KindRequirement.model_le_referent' names the referent 'PropertyKindCalculus.Tests.KindRequirement.aMax' — a statement that names what the model does not define is empirical
-/
#guard_msgs in #kind_requirement witnessNamesAReferent

/-- The license that must be absent is present. -/
@[kindCounterexample]
def absencePresent : Provenance.Requirement where
  name := "B14"
  statement := "the argument's kind carries no probe license"
  kind := .provable
  governs := ``modelBoundary
  absent := ``licenseA

/--
error: an instance of 'PropertyKindCalculus.Tests.KindRequirement.ProbeLicense' at 'PropertyKindCalculus.Tests.KindRequirement.licenseA' is in the environment — the license 'B14' requires absent is present
-/
#guard_msgs in #kind_requirement absencePresent

/-- What must be absent is a license — a class application. -/
@[kindCounterexample]
def absenceNotALicense : Provenance.Requirement where
  name := "B15"
  statement := "nothing is non-negative"
  kind := .provable
  governs := ``modelBoundary
  absent := ``NonNeg

/--
error: the absence 'PropertyKindCalculus.Tests.KindRequirement.NonNeg' does not unfold to a class application — a license is an instance, and what must be absent is the instance
-/
#guard_msgs in #kind_requirement absenceNotALicense

/-- A theorem cannot discharge a statement about what the model does not define. -/
@[kindCounterexample]
def empiricalWithWitness : Provenance.Requirement where
  name := "B16"
  statement := "the argument stays within the datasheet's range"
  kind := .empirical
  governs := ``modelBoundary
  referents := [``aMax]
  gate := ``inRange
  witness := ``model_le_bound

/--
error: 'B16' is empirical but names a witness — a theorem about the model cannot discharge a statement about what the model does not define; if the statement closes over the model, the requirement is provable
-/
#guard_msgs in #kind_requirement empiricalWithWitness

/-- An empirical requirement names its referent. -/
@[kindCounterexample]
def empiricalWithoutReferent : Provenance.Requirement where
  name := "B17"
  statement := "the argument stays within range"
  kind := .empirical
  governs := ``modelBoundary
  gate := ``inRange

/--
error: 'B17' is empirical but names no referent — what the model does not define is named, and marked `@[kindReferent]` with where it comes from
-/
#guard_msgs in #kind_requirement empiricalWithoutReferent

/-- An empirical requirement is gated or attested. -/
@[kindCounterexample]
def empiricalWithoutGate : Provenance.Requirement where
  name := "B18"
  statement := "the argument stays within the datasheet's range"
  kind := .empirical
  governs := ``modelBoundary
  referents := [``aMax]

/--
error: 'B18' is empirical but names no gate — an empirical requirement is discharged by a decision against its referent, or attested with a reason
-/
#guard_msgs in #kind_requirement empiricalWithoutGate

/-- A referent carries where it comes from. -/
@[kindCounterexample]
def referentUnmarked : Provenance.Requirement where
  name := "B19"
  statement := "the argument stays within range"
  kind := .empirical
  governs := ``modelBoundary
  referents := [``bK]
  gate := ``inRange

/--
error: the referent 'PropertyKindCalculus.Tests.KindRequirement.bK' is not marked `@[kindReferent]` — a referent carries where it comes from, and the mark is what the demarcation reads
-/
#guard_msgs in #kind_requirement referentUnmarked

/-- The gate decides against the referent, not against the model's own threshold. -/
def gateNamesNoReferent : Provenance.Requirement where
  name := "B20"
  statement := "the argument stays within the datasheet's range"
  kind := .empirical
  governs := ``modelBoundary
  referents := [``aMax]
  gate := ``inModelRange

/--
error: the gate 'PropertyKindCalculus.Tests.KindRequirement.inModelRange' names none of the referents — a decision whose threshold is the model's own is not an observation
-/
#guard_msgs in #kind_requirement gateNamesNoReferent

/-- A spot check that fails fails the requirement. -/
@[kindCounterexample]
def spotCheckFails : Provenance.Requirement where
  name := "B21"
  statement := "the model's answer never exceeds the specification's bound"
  kind := .provable
  governs := ``modelBoundary
  witness := ``modelBounded
  spotChecks := [``spotFalse]

/--
error: the spot check 'PropertyKindCalculus.Tests.KindRequirement.spotFalse' evaluated to false — the requirement fails where the model runs
-/
#guard_msgs in #kind_requirement spotCheckFails

/-- A spot check is a decision the command can run. -/
@[kindCounterexample]
def spotCheckNotABool : Provenance.Requirement where
  name := "B22"
  statement := "the model's answer never exceeds the specification's bound"
  kind := .provable
  governs := ``modelBoundary
  witness := ``modelBounded
  spotChecks := [``model]

/--
error: the spot check 'PropertyKindCalculus.Tests.KindRequirement.model' is not a 'Bool' — a spot check is a decision the command can run
-/
#guard_msgs in #kind_requirement spotCheckNotABool

/-- A counterexample kept beside the gate it exercises: exempted from the sweeps. -/
@[kindCounterexample]
def kept : Provenance.Requirement where
  name := "B23"
  statement := "the bound is bounded"
  kind := .provable
  governs := ``boundSpec
  witness := ``model_le_bound

end Bad

/-! ## The survey — every requirement in a scope, violations as `✗` rows -/

/--
info: kind requirements — 6 requirement(s): 4 provable, 2 empirical, 2 attested
  PropertyKindCalculus.Tests.KindRequirement.Good.a1: 'A1' (provable) on 'requirement probe model' — attested: the proof waits on the carrier's order lemmas
  PropertyKindCalculus.Tests.KindRequirement.Good.a2: 'A2' (empirical) on 'requirement probe model' — attested: no reference run yet
  PropertyKindCalculus.Tests.KindRequirement.Good.e1: 'E1' (empirical) on 'requirement probe model' — gated by PropertyKindCalculus.Tests.KindRequirement.inRange
  PropertyKindCalculus.Tests.KindRequirement.Good.p1: 'P1' (provable) on 'requirement probe model' — by PropertyKindCalculus.Tests.KindRequirement.modelBounded
  PropertyKindCalculus.Tests.KindRequirement.Good.p2: 'P2' (provable) on 'requirement probe model' — by PropertyKindCalculus.Tests.KindRequirement.model_le_bound
  PropertyKindCalculus.Tests.KindRequirement.Good.p3: 'P3' (provable) on 'requirement probe model' — absent PropertyKindCalculus.Tests.KindRequirement.noLicenseB
-/
#guard_msgs in #kind_requirements PropertyKindCalculus.Tests.KindRequirement.Good

/-! Two of the refusals, as the survey renders them, and the counterexample exempted. -/

/--
info: kind requirements — 2 requirement(s), 2 violated, 1 exempted: 0 provable, 0 empirical, 0 attested
  ✗ PropertyKindCalculus.Tests.KindRequirement.Bad.gateNamesNoReferent: the gate 'PropertyKindCalculus.Tests.KindRequirement.inModelRange' names none of the referents — a decision whose threshold is the model's own is not an observation
  ✗ PropertyKindCalculus.Tests.KindRequirement.Bad.governsASpecification: 'B1' governs 'requirement probe specification', which is a specification boundary — a requirement governs a model boundary; a specification is what it is checked against
  ⊘ PropertyKindCalculus.Tests.KindRequirement.Bad.kept: counterexample, exempted
-/
#guard_msgs in #kind_requirements PropertyKindCalculus.Tests.KindRequirement.Bad.governsASpecification PropertyKindCalculus.Tests.KindRequirement.Bad.gateNamesNoReferent PropertyKindCalculus.Tests.KindRequirement.Bad.kept

/-! ## The census and its gate -/

/--
info: requirement coverage:
[governed] PropertyKindCalculus.Tests.KindRequirement.modelBoundary ('requirement probe model') model/result — by 'B20', 'A1', 'A2', 'P1', 'P2', 'P3'
⊘ exempted PropertyKindCalculus.Tests.KindRequirement.freeBoundary ('requirement probe free') model/result — pure data movement: nothing is demanded of a copy
⊘ specification PropertyKindCalculus.Tests.KindRequirement.boundSpec ('requirement probe specification') — the subject of no requirement
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirement.boundAsModel ('requirement probe bound, as a model') bound/result
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirement.orphan ('requirement probe orphan') model/result
5 row(s) over 4 model boundary(ies): 1 governed, 2 exempted, 2 UNGOVERNED — requirement-coverage violation
requirements: 4 provable, 3 empirical, 2 attested
-/
#guard_msgs in #kind_requirement_coverage PropertyKindCalculus.Tests.KindRequirement

/--
error: requirement coverage: 2 produced port(s) no requirement governs — requirement-coverage violation
  ⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirement.boundAsModel ('requirement probe bound, as a model') bound/result
  ⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirement.orphan ('requirement probe orphan') model/result

What a model's quantities must satisfy is stated as a `Provenance.Requirement` governing the boundary that produces them, not as prose beside the module. Give each port at issue a requirement — provable with its theorem edge or theorem, empirical with its referents and gate, or attested with a reason — or, where nothing is demanded of what the boundary produces, mark its declaration `@[kindRequirementFree "reason"]` so the exemption is data the sweep can read. Do NOT re-pin a `#kind_requirement_coverage` report whose summary says `violation` — that turns the build green and the census off.
-/
#guard_msgs in #kind_requirement_clean PropertyKindCalculus.Tests.KindRequirement

/-! ## The marks' own refusals -/

/--
error: `@[kindReferent]` expects a kinded quantity — a 'Quantity' or an 'IndividualQuantity' — and 'PropertyKindCalculus.Tests.KindRequirement.bareThreshold' is neither. A referent is a number about the world, and the kind is what says which number; a bare carrier value is invisible to every census.
-/
#guard_msgs in @[kindReferent "a datasheet"] def bareThreshold : Int := 10

/--
error: `@[kindReferent]` on 'PropertyKindCalculus.Tests.KindRequirement.unsourced' needs to say where the referent comes from: a threshold with no provenance is the docstring problem in a new place
-/
#guard_msgs in @[kindReferent " "] def unsourced : Quantity aK Int := ⟨10⟩

/--
error: `@[kindRequirementFree]` expects a 'Provenance.Contract' — 'PropertyKindCalculus.Tests.KindRequirement.notABoundary' is not one. The mark exempts a declared boundary from a census over declared boundaries, so that is where it goes.
-/
#guard_msgs in @[kindRequirementFree "nothing"] def notABoundary : Nat := 0

/--
error: `@[kindRequirementFree]` on 'PropertyKindCalculus.Tests.KindRequirement.unreasoned' needs a reason: an exemption without one is the docstring problem in a new place
-/
#guard_msgs in @[kindRequirementFree ""] def unreasoned : Provenance.Contract NodeId KindRef :=
  { name := "unreasoned", members := [``model], ports := [], exits := [] }

end PropertyKindCalculus.Tests.KindRequirement

end Blanket
