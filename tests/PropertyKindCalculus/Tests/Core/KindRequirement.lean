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
present, one that is not a license, and one whose instance search does not finish; an
empirical requirement naming a witness, no referent, no gate, an unmarked referent, or a
gate that mentions no referent; a spot check that is false, and one that is not a `Bool`.
The survey, the census and the gate close the file, with the two marks' own refusals.
The sibling scope probes pin inferred domains for generic and fixed indices, reducible and
opaque conditionals, an aliased result, a kind-index constant, object aliases, a
non-enumerable index, and a result whose type carries no object index, named structure objects,
projected and aliased composite bearers, and fail-closed missing and unresolved object indices.
-/

module

public import PropertyKindCalculus.KindRequirement
meta import PropertyKindCalculus.KindRequirement
public import PropertyKindCalculus.Composite
meta import PropertyKindCalculus.Composite

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

/-- A license whose instance search never settles: each instance asks for the next. -/
class UnsettledLicense (n : Nat) : Prop where

instance {n : Nat} [UnsettledLicense (n + 1)] : UnsettledLicense n := ⟨⟩

/-- The license whose absence cannot be decided. -/
def unsettledLicense : Prop := UnsettledLicense 0

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
  scope := .all
  witness := ``modelBounded
  spotChecks := [``spot]

/--
info: kind requirement 'P1' (provable) on 'requirement probe model'
statement: the model's answer never exceeds the specification's bound
governs: 'requirement probe model' at model/result
scope: all
edge: PropertyKindCalculus.Tests.KindRequirement.modelBounded — 'requirement probe model' bounded by 'requirement probe specification'
witness: PropertyKindCalculus.Tests.KindRequirement.model_le_bound
spot check: PropertyKindCalculus.Tests.KindRequirement.spot = true
-/
#guard_msgs in #kind_requirement p1

/-- Provable by a bare theorem, over every evaluation. -/
def p2 : Provenance.Requirement where
  name := "P2"
  statement := "the model's answer is at most three times its argument"
  kind := .provable
  governs := ``modelBoundary
  scope := .all
  witness := ``model_le_bound

/--
info: kind requirement 'P2' (provable) on 'requirement probe model'
statement: the model's answer is at most three times its argument
governs: every produced port of 'requirement probe model'
scope: all
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

/-- An instance search that does not finish is an error, not an absence. -/
@[kindCounterexample]
def absenceUndecided : Provenance.Requirement where
  name := "B24"
  statement := "the argument's kind carries no unsettled license"
  kind := .provable
  governs := ``modelBoundary
  absent := ``unsettledLicense

/--
error: could not decide whether 'PropertyKindCalculus.Tests.KindRequirement.UnsettledLicense' has an instance at 'PropertyKindCalculus.Tests.KindRequirement.unsettledLicense' — the instance search did not finish: failed to synthesize
  UnsettledLicense 0
(deterministic) timeout at `typeclass`, maximum number of heartbeats (1) has been reached

Note: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in set_option synthInstance.maxHeartbeats 1 in #kind_requirement absenceUndecided

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
error: requirement coverage: 2 produced port(s) no requirement governs or whose object scope cannot be checked — requirement-coverage violation
  ⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirement.boundAsModel ('requirement probe bound, as a model') bound/result
  ⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirement.orphan ('requirement probe orphan') model/result

What a model's quantities must satisfy is stated as a `Provenance.Requirement` governing the boundary that produces them, not as prose beside the module. Give each port at issue a requirement — provable with its theorem edge or theorem, empirical with its referents and gate, or attested with a reason — or, where nothing is demanded of what the boundary produces, mark its declaration `@[kindRequirementFree "reason"]` so the exemption is data the sweep can read. An object scope must be checkable against the result's object index. Do NOT re-pin a `#kind_requirement_coverage` report whose summary says `violation` — that turns the build green and the census off.
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

namespace PropertyKindCalculus.Tests.KindRequirementScope

open PropertyKindCalculus.Tests.KindRequirement
open PropertyKindCalculus.Provenance (NodeId KindRef)

def bareResultModel (x : Quantity aK Int) : Quantity bK Int :=
  ⟨2 * x.magnitude⟩

def bareResultBoundary : Provenance.Contract NodeId KindRef where
  name := "unindexed result"
  members := [``bareResultModel]
  ports := [
    ⟨(NodeId.binder "x").within ``bareResultModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``bareResultModel, .decl ``bK, .output⟩
  ]
  exits := []

def bareResultRequirement : Provenance.Requirement where
  name := "bare-result object scope"
  statement := "the result is governed for Thing.one"
  kind := .provable
  governs := ``bareResultBoundary
  port := some (NodeId.result.within ``bareResultModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

/--
error: 'bare-result object scope' is scoped to objects of type 'Thing', but 'bareResultModel/result' of 'unindexed result' carries no 'Thing' index — an object scope quantifies over the objects an output belongs to; scope it over a sort or `.all`, or index the result by its object
-/
#guard_msgs (whitespace := lax) in #kind_requirement bareResultRequirement

def thingModel {t : Thing} (x : IndividualQuantity t aK Int) :
    IndividualQuantity t bK Int :=
  ⟨2 * x.magnitude⟩

def thingBoundary (name : String) : Provenance.Contract NodeId KindRef where
  name := name
  members := [``thingModel]
  ports := [
    ⟨(NodeId.binder "x").within ``thingModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``thingModel, .decl ``bK, .output⟩
  ]
  exits := []

def thingOneBoundary : Provenance.Contract NodeId KindRef :=
  thingBoundary "Thing-indexed model, one scoped object"

def thingOneRequirement : Provenance.Requirement where
  name := "Thing one"
  statement := "the generic result is governed for Thing.one"
  kind := .provable
  governs := ``thingOneBoundary
  port := some (NodeId.result.within ``thingModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

def thingInputRequirement : Provenance.Requirement where
  name := "Thing scope on input port"
  statement := "the input port is covered by an object-scoped requirement"
  kind := .provable
  governs := ``thingOneBoundary
  port := some ((NodeId.binder "x").within ``thingModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

/--
error: 'Thing scope on input port' is scoped to objects or a sort, but 'thingModel/x' of 'Thing-indexed model, one scoped object' is an input — an object or sort scope quantifies over the objects an output belongs to; govern a produced port
-/
#guard_msgs (whitespace := lax) in #kind_requirement thingInputRequirement

def thingBothBoundary : Provenance.Contract NodeId KindRef :=
  thingBoundary "Thing-indexed model, both scoped objects"

def thingBothRequirement : Provenance.Requirement where
  name := "Thing one and two"
  statement := "the generic result is governed for Thing.one and Thing.two"
  kind := .provable
  governs := ``thingBothBoundary
  port := some (NodeId.result.within ``thingModel)
  scope := .objects [``Thing.one, ``Thing.two]
  attested := "coverage-domain probe"

/--
info: kind requirement 'Thing one and two' (provable) on 'Thing-indexed model, both scoped objects'
statement: the generic result is governed for Thing.one and Thing.two
governs: 'Thing-indexed model, both scoped objects' at thingModel/result
scope: objects PropertyKindCalculus.Tests.KindRequirement.Thing.one, PropertyKindCalculus.Tests.KindRequirement.Thing.two
attested: coverage-domain probe
-/
#guard_msgs in #kind_requirement thingBothRequirement

def thingTwoModel (x : IndividualQuantity Thing.two aK Int) :
    IndividualQuantity Thing.two bK Int :=
  ⟨2 * x.magnitude⟩

def thingTwoBoundary : Provenance.Contract NodeId KindRef where
  name := "Thing.two-indexed model"
  members := [``thingTwoModel]
  ports := [
    ⟨(NodeId.binder "x").within ``thingTwoModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``thingTwoModel, .decl ``bK, .output⟩
  ]
  exits := []

def thingTwoRequirement : Provenance.Requirement where
  name := "Thing one on Thing two"
  statement := "the fixed Thing.two result is governed only for Thing.one"
  kind := .provable
  governs := ``thingTwoBoundary
  port := some (NodeId.result.within ``thingTwoModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

def FixedResult := IndividualQuantity Thing.two bK Int

def aliasedThingTwoModel (x : IndividualQuantity Thing.two aK Int) : FixedResult :=
  ⟨2 * x.magnitude⟩

def aliasedThingTwoBoundary : Provenance.Contract NodeId KindRef where
  name := "aliased Thing.two result"
  members := [``aliasedThingTwoModel]
  ports := [
    ⟨(NodeId.binder "x").within ``aliasedThingTwoModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``aliasedThingTwoModel, .decl ``bK, .output⟩
  ]
  exits := []

def aliasedThingTwoRequirement : Provenance.Requirement where
  name := "Thing one on aliased Thing.two"
  statement := "the aliased fixed result is governed only for Thing.one"
  kind := .provable
  governs := ``aliasedThingTwoBoundary
  port := some (NodeId.result.within ``aliasedThingTwoModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

def kindFor : Thing → KindOfProperty
  | .one => aK
  | .two => bK

def kindIndexedModel : IndividualQuantity Thing.one (kindFor Thing.two) Int :=
  ⟨0⟩

def kindIndexedBoundary : Provenance.Contract NodeId KindRef where
  name := "Thing.one result with a kind index"
  members := [``kindIndexedModel]
  ports := [⟨NodeId.result.within ``kindIndexedModel, .decl ``bK, .output⟩]
  exits := []

def kindIndexedRequirement : Provenance.Requirement where
  name := "Thing one on kind-indexed result"
  statement := "the kind-indexed result is governed for Thing.one"
  kind := .provable
  governs := ``kindIndexedBoundary
  port := some (NodeId.result.within ``kindIndexedModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

def CondResult := IndividualQuantity (if true then Thing.one else Thing.two) bK Int

def conditionalResultModel (x : IndividualQuantity Thing.one aK Int) : CondResult :=
  ⟨2 * x.magnitude⟩

def conditionalResultBoundary : Provenance.Contract NodeId KindRef where
  name := "conditional result"
  members := [``conditionalResultModel]
  ports := [
    ⟨(NodeId.binder "x").within ``conditionalResultModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``conditionalResultModel, .decl ``bK, .output⟩
  ]
  exits := []

def conditionalResultRequirement : Provenance.Requirement where
  name := "Thing one on conditional result"
  statement := "the reducible conditional result is governed for Thing.one"
  kind := .provable
  governs := ``conditionalResultBoundary
  port := some (NodeId.result.within ``conditionalResultModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

axiom flag : Bool

def opaqueResultModel (x : IndividualQuantity Thing.one aK Int) :
    IndividualQuantity (if flag then Thing.one else Thing.two) bK Int :=
  ⟨2 * x.magnitude⟩

def opaqueResultBoundary : Provenance.Contract NodeId KindRef where
  name := "opaque conditional result"
  members := [``opaqueResultModel]
  ports := [
    ⟨(NodeId.binder "x").within ``opaqueResultModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``opaqueResultModel, .decl ``bK, .output⟩
  ]
  exits := []

def opaqueResultRequirement : Provenance.Requirement where
  name := "Thing one on opaque conditional result"
  statement := "the opaque conditional result is governed for Thing.one"
  kind := .provable
  governs := ``opaqueResultBoundary
  port := some (NodeId.result.within ``opaqueResultModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

def opaqueExemptResultModel (x : IndividualQuantity Thing.one aK Int) :
    IndividualQuantity (if flag then Thing.one else Thing.two) bK Int :=
  ⟨2 * x.magnitude⟩

@[kindRequirementFree "the opaque output's Thing object cannot be determined statically"]
def opaqueExemptBoundary : Provenance.Contract NodeId KindRef where
  name := "exempt opaque conditional result"
  members := [``opaqueExemptResultModel]
  ports := [
    ⟨(NodeId.binder "x").within ``opaqueExemptResultModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``opaqueExemptResultModel, .decl ``bK, .output⟩
  ]
  exits := []

def opaqueExemptRequirement : Provenance.Requirement where
  name := "Thing one on exempt opaque conditional result"
  statement := "the marked opaque conditional output is covered by an explicit exemption"
  kind := .provable
  governs := ``opaqueExemptBoundary
  port := some (NodeId.result.within ``opaqueExemptResultModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

namespace UnresolvedOnly

def unresolvedModel (x : IndividualQuantity Thing.one aK Int) :
    IndividualQuantity (if flag then Thing.one else Thing.two) bK Int :=
  ⟨2 * x.magnitude⟩

def unresolvedBoundary : Provenance.Contract NodeId KindRef where
  name := "isolated opaque result"
  members := [``unresolvedModel]
  ports := [
    ⟨(NodeId.binder "x").within ``unresolvedModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``unresolvedModel, .decl ``bK, .output⟩
  ]
  exits := []

def unresolvedRequirement : Provenance.Requirement where
  name := "Thing one on isolated opaque result"
  statement := "the isolated opaque output is scoped to Thing.one"
  kind := .provable
  governs := ``unresolvedBoundary
  port := some (NodeId.result.within ``unresolvedModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

/--
error: requirement coverage: 1 produced port(s) no requirement governs or whose object scope cannot be checked — requirement-coverage violation
  ⚠ UNCHECKED PropertyKindCalculus.Tests.KindRequirementScope.UnresolvedOnly.unresolvedBoundary ('isolated opaque result') unresolvedModel/result — 'Thing one on isolated opaque result' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one: the result's 'Thing' object cannot be determined statically

What a model's quantities must satisfy is stated as a `Provenance.Requirement` governing the boundary that produces them, not as prose beside the module. Give each port at issue a requirement — provable with its theorem edge or theorem, empirical with its referents and gate, or attested with a reason — or, where nothing is demanded of what the boundary produces, mark its declaration `@[kindRequirementFree "reason"]` so the exemption is data the sweep can read. An object scope must be checkable against the result's object index. Do NOT re-pin a `#kind_requirement_coverage` report whose summary says `violation` — that turns the build green and the census off.
-/
#guard_msgs (whitespace := lax) in
  #kind_requirement_clean PropertyKindCalculus.Tests.KindRequirementScope.UnresolvedOnly

end UnresolvedOnly

def first : Thing := .one

def thingAliasBoundary : Provenance.Contract NodeId KindRef :=
  thingBoundary "Thing-indexed model, aliased object scope"

def thingAliasRequirement : Provenance.Requirement where
  name := "Thing first and two"
  statement := "the generic result is governed for first and Thing.two"
  kind := .provable
  governs := ``thingAliasBoundary
  port := some (NodeId.result.within ``thingModel)
  scope := .objects [``first, ``Thing.two]
  attested := "coverage-domain probe"

structure Tag where
  id : String

def tagS : SortOfSystem := ⟨"coverage probe tag"⟩
instance : Sorted Tag := ⟨fun _ => tagS⟩

def tagA : Tag := ⟨"A"⟩

def tagModel {t : Tag} (x : IndividualQuantity t aK Int) :
    IndividualQuantity t bK Int :=
  ⟨2 * x.magnitude⟩

def tagBoundary : Provenance.Contract NodeId KindRef where
  name := "Tag-indexed model"
  members := [``tagModel]
  ports := [
    ⟨(NodeId.binder "x").within ``tagModel, .decl ``aK, .input⟩,
    ⟨NodeId.result.within ``tagModel, .decl ``bK, .output⟩
  ]
  exits := []

def tagRequirement : Provenance.Requirement where
  name := "Tag A"
  statement := "the generic result is governed for tag A"
  kind := .provable
  governs := ``tagBoundary
  port := some (NodeId.result.within ``tagModel)
  scope := .objects [``tagA]
  attested := "coverage-domain probe"

def tagB : Tag := ⟨"B"⟩

def namedTagBModel : IndividualQuantity tagB bK Int := ⟨0⟩

def namedTagBoundary : Provenance.Contract NodeId KindRef where
  name := "named Tag B result"
  members := [``namedTagBModel]
  ports := [⟨NodeId.result.within ``namedTagBModel, .decl ``bK, .output⟩]
  exits := []

def namedTagRequirement : Provenance.Requirement where
  name := "Tag A on named Tag B"
  statement := "a named Tag B result is not governed by Tag A"
  kind := .provable
  governs := ``namedTagBoundary
  port := some (NodeId.result.within ``namedTagBModel)
  scope := .objects [``tagA]
  attested := "coverage-domain probe"

structure ThingBox where
  object : Thing

structure Holder where
  box : ThingBox

def heldTwo : Holder := ⟨⟨Thing.two⟩⟩

def projectedCompositeModel :
    IndividualQuantity
      (Composite.part (σ := probeS) ((⟨⟨Thing.two⟩⟩ : Holder).box.object))
      bK Int :=
  ⟨0⟩

def projectedCompositeBoundary : Provenance.Contract NodeId KindRef where
  name := "projected composite Thing.two result"
  members := [``projectedCompositeModel]
  ports := [⟨NodeId.result.within ``projectedCompositeModel, .decl ``bK, .output⟩]
  exits := []

def projectedCompositeRequirement : Provenance.Requirement where
  name := "Thing one on projected composite"
  statement := "a projected composite bearer containing Thing.two is not governed by Thing.one"
  kind := .provable
  governs := ``projectedCompositeBoundary
  port := some (NodeId.result.within ``projectedCompositeModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

def wrappedCompositeModel :
    IndividualQuantity (Composite.part (σ := probeS) heldTwo) bK Int :=
  ⟨0⟩

def wrappedCompositeBoundary : Provenance.Contract NodeId KindRef where
  name := "wrapped composite Thing.two result"
  members := [``wrappedCompositeModel]
  ports := [⟨NodeId.result.within ``wrappedCompositeModel, .decl ``bK, .output⟩]
  exits := []

def wrappedCompositeRequirement : Provenance.Requirement where
  name := "Thing one on wrapped composite"
  statement := "a wrapped composite bearer containing Thing.two is not governed by Thing.one"
  kind := .provable
  governs := ``wrappedCompositeBoundary
  port := some (NodeId.result.within ``wrappedCompositeModel)
  scope := .objects [``Thing.one]
  attested := "coverage-domain probe"

def thingSortBoundary : Provenance.Contract NodeId KindRef :=
  thingBoundary "Thing-indexed model, sort-scoped output"

def thingSortRequirement : Provenance.Requirement where
  name := "probe sort on Thing"
  statement := "the generic Thing output is governed by its sort"
  kind := .provable
  governs := ``thingSortBoundary
  port := some (NodeId.result.within ``thingModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

/--
info: kind requirement 'probe sort on Thing' (provable) on 'Thing-indexed model, sort-scoped output'
statement: the generic Thing output is governed by its sort
governs: 'Thing-indexed model, sort-scoped output' at thingModel/result
scope: sort PropertyKindCalculus.Tests.KindRequirement.probeS
attested: coverage-domain probe
-/
#guard_msgs in #kind_requirement thingSortRequirement

def thingWrongSortBoundary : Provenance.Contract NodeId KindRef :=
  thingBoundary "Thing-indexed model, wrong sort scope"

def thingWrongSortRequirement : Provenance.Requirement where
  name := "Tag sort on Thing"
  statement := "a Thing output is not governed by the Tag sort"
  kind := .provable
  governs := ``thingWrongSortBoundary
  port := some (NodeId.result.within ``thingModel)
  scope := .sort ``tagS
  attested := "coverage-domain probe"

inductive Mixed where
  | m1
  | m2

instance : Sorted Mixed := ⟨fun
  | .m1 => probeS
  | .m2 => tagS⟩

def mixedGenericModel {m : Mixed} : IndividualQuantity m bK Int := ⟨0⟩
def mixedOneModel : IndividualQuantity Mixed.m1 bK Int := ⟨0⟩
def mixedTwoModel : IndividualQuantity Mixed.m2 bK Int := ⟨0⟩

structure Target (s : SortOfSystem) where
  tag : Nat

instance {s : SortOfSystem} : Sorted (Target s) := ⟨fun _ => s⟩

def targetGenericModel {s : SortOfSystem} {t : Target s} :
    IndividualQuantity t bK Int := ⟨0⟩

def mixedBoundary (name : String) (member : Lean.Name) :
    Provenance.Contract NodeId KindRef where
  name := name
  members := [member]
  ports := [⟨NodeId.result.within member, .decl ``bK, .output⟩]
  exits := []

def mixedGenericBoundary : Provenance.Contract NodeId KindRef :=
  mixedBoundary "generic Mixed result" ``mixedGenericModel

def mixedGenericCombinedBoundary : Provenance.Contract NodeId KindRef :=
  mixedBoundary "generic Mixed result with object scope" ``mixedGenericModel

def mixedOneBoundary : Provenance.Contract NodeId KindRef :=
  mixedBoundary "Mixed.m1 result" ``mixedOneModel

def mixedTwoBoundary : Provenance.Contract NodeId KindRef :=
  mixedBoundary "Mixed.m2 result" ``mixedTwoModel

@[kindRequirementFree "the fixed m2 object has sort tagS, not probeS"]
def mixedTwoExemptBoundary : Provenance.Contract NodeId KindRef :=
  mixedBoundary "exempt Mixed.m2 result" ``mixedTwoModel

def mixedTwoCombinedBoundary : Provenance.Contract NodeId KindRef :=
  mixedBoundary "Mixed.m2 result with object scope" ``mixedTwoModel

def mixedGenericRequirement : Provenance.Requirement where
  name := "probe sort on generic Mixed"
  statement := "the generic Mixed output has sort probeS"
  kind := .provable
  governs := ``mixedGenericBoundary
  port := some (NodeId.result.within ``mixedGenericModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

def mixedGenericCombinedSortRequirement : Provenance.Requirement where
  name := "probe sort on generic Mixed with m2 object"
  statement := "the generic Mixed output is governed by probeS and its m2 object"
  kind := .provable
  governs := ``mixedGenericCombinedBoundary
  port := some (NodeId.result.within ``mixedGenericModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

def mixedGenericCombinedObjectRequirement : Provenance.Requirement where
  name := "Mixed.m2 object scope on generic output"
  statement := "Mixed.m2 is explicitly governed in the generic output"
  kind := .provable
  governs := ``mixedGenericCombinedBoundary
  port := some (NodeId.result.within ``mixedGenericModel)
  scope := .objects [``Mixed.m2]
  attested := "coverage-domain probe"

def mixedOneRequirement : Provenance.Requirement where
  name := "probe sort on Mixed.m1"
  statement := "Mixed.m1 has sort probeS"
  kind := .provable
  governs := ``mixedOneBoundary
  port := some (NodeId.result.within ``mixedOneModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

def mixedTwoRequirement : Provenance.Requirement where
  name := "probe sort on Mixed.m2"
  statement := "Mixed.m2 is not of sort probeS"
  kind := .provable
  governs := ``mixedTwoBoundary
  port := some (NodeId.result.within ``mixedTwoModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

def mixedTwoExemptRequirement : Provenance.Requirement where
  name := "exempt probe sort on Mixed.m2"
  statement := "the marked Mixed.m2 output is explicitly exempted"
  kind := .provable
  governs := ``mixedTwoExemptBoundary
  port := some (NodeId.result.within ``mixedTwoModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

def mixedTwoCombinedSortRequirement : Provenance.Requirement where
  name := "probe sort on Mixed.m2 with object"
  statement := "Mixed.m2 is covered by its object scope despite the other sort"
  kind := .provable
  governs := ``mixedTwoCombinedBoundary
  port := some (NodeId.result.within ``mixedTwoModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

def mixedTwoCombinedObjectRequirement : Provenance.Requirement where
  name := "Mixed.m2 object scope"
  statement := "Mixed.m2 is explicitly governed as an object"
  kind := .provable
  governs := ``mixedTwoCombinedBoundary
  port := some (NodeId.result.within ``mixedTwoModel)
  scope := .objects [``Mixed.m2]
  attested := "coverage-domain probe"

def targetGenericBoundary : Provenance.Contract NodeId KindRef where
  name := "generic Target result"
  members := [``targetGenericModel]
  ports := [⟨NodeId.result.within ``targetGenericModel, .decl ``bK, .output⟩]
  exits := []

def targetGenericSortRequirement : Provenance.Requirement where
  name := "probe sort on generic Target"
  statement := "the generic Target output is governed by probeS"
  kind := .provable
  governs := ``targetGenericBoundary
  port := some (NodeId.result.within ``targetGenericModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

def anyB (_y : Quantity bK Int) : Bool := true

theorem anyB_model : ∀ x, anyB (model x) = true := fun _ => rfl

def isZero (y : Quantity bK Int) : Bool := y.magnitude == 0

def zeroModel (_ : Quantity aK Int) : Quantity bK Int := ⟨0⟩

def oneModel (_ : Quantity aK Int) : Quantity bK Int := ⟨1⟩

theorem isZero_zeroModel : ∀ x, isZero (zeroModel x) = true := by
  intro x
  simp [isZero, zeroModel]

def decidedProofBoundary : Provenance.Contract NodeId KindRef :=
  { modelBoundary with name := "decider proof result" }

def decidedNoProofBoundary : Provenance.Contract NodeId KindRef :=
  { modelBoundary with name := "decided result without proof" }

@[kindRequirementFree "the probe isolates a decided scope's missing proof"]
def decidedExemptBoundary : Provenance.Contract NodeId KindRef :=
  { modelBoundary with name := "exempt decided result without proof" }

def decidedWrongProofBoundary : Provenance.Contract NodeId KindRef where
  name := "decided result with proof for another member"
  members := [``oneModel]
  ports := [⟨NodeId.result.within ``oneModel, .decl ``bK, .output⟩]
  exits := []

def decidedProofRequirement : Provenance.Requirement where
  name := "decider proof on model output"
  statement := "anyB holds for every model output"
  kind := .provable
  governs := ``decidedProofBoundary
  port := some (NodeId.result.within ``PropertyKindCalculus.Tests.KindRequirement.model)
  scope := .decided ``anyB
  deciderProof := some ``anyB_model
  attested := "decided-scope proof probe"

/--
info: kind requirement 'decider proof on model output' (provable) on 'decider proof result'
statement: anyB holds for every model output
governs: 'decider proof result' at model/result
scope: decided by PropertyKindCalculus.Tests.KindRequirementScope.anyB
decider proof: PropertyKindCalculus.Tests.KindRequirementScope.anyB_model
attested: decided-scope proof probe
-/
#guard_msgs in #kind_requirement decidedProofRequirement

def decidedNoProofRequirement : Provenance.Requirement where
  name := "decided scope without proof"
  statement := "the decider's output subset is unchecked"
  kind := .provable
  governs := ``decidedNoProofBoundary
  port := some (NodeId.result.within ``PropertyKindCalculus.Tests.KindRequirement.model)
  scope := .decided ``anyB
  attested := "decided-scope proof probe"

/--
info: kind requirement 'decided scope without proof' (provable) on 'decided result without proof'
statement: the decider's output subset is unchecked
governs: 'decided result without proof' at model/result
scope: decided by PropertyKindCalculus.Tests.KindRequirementScope.anyB
attested: decided-scope proof probe
-/
#guard_msgs in #kind_requirement decidedNoProofRequirement

def decidedExemptRequirement : Provenance.Requirement :=
  { decidedNoProofRequirement with
    name := "exempted decided scope without proof"
    governs := ``decidedExemptBoundary }

/--
info: kind requirement 'exempted decided scope without proof' (provable) on 'exempt decided result without proof'
statement: the decider's output subset is unchecked
governs: 'exempt decided result without proof' at model/result
scope: decided by PropertyKindCalculus.Tests.KindRequirementScope.anyB
attested: decided-scope proof probe
-/
#guard_msgs in #kind_requirement decidedExemptRequirement

def decidedWrongProofRequirement : Provenance.Requirement where
  name := "decider proof for another member"
  statement := "the proof must be for the member this boundary governs"
  kind := .provable
  governs := ``decidedWrongProofBoundary
  port := some (NodeId.result.within ``oneModel)
  scope := .decided ``isZero
  deciderProof := some ``isZero_zeroModel
  attested := "decided-scope proof probe"

/--
error: 'PropertyKindCalculus.Tests.KindRequirementScope.isZero_zeroModel' does not prove that 'PropertyKindCalculus.Tests.KindRequirementScope.isZero' holds on everything 'PropertyKindCalculus.Tests.KindRequirementScope.oneModel' produces — expected: ∀
  (x : Quantity aK Int), isZero (oneModel x) = true
-/
#guard_msgs (whitespace := lax) in #kind_requirement decidedWrongProofRequirement

/--
info: requirement coverage:
[governed] PropertyKindCalculus.Tests.KindRequirementScope.conditionalResultBoundary ('conditional result') conditionalResultModel/result — by 'Thing one on conditional result'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.decidedProofBoundary ('decider proof result') model/result — by 'decider proof on model output'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.kindIndexedBoundary ('Thing.one result with a kind index') kindIndexedModel/result — by 'Thing one on kind-indexed result'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.mixedGenericBoundary ('generic Mixed result') mixedGenericModel/result for PropertyKindCalculus.Tests.KindRequirementScope.Mixed.m1 — by 'probe sort on generic Mixed'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.mixedGenericCombinedBoundary ('generic Mixed result with object scope') mixedGenericModel/result — by 'Mixed.m2 object scope on generic output', 'probe sort on generic Mixed with m2 object'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.mixedOneBoundary ('Mixed.m1 result') mixedOneModel/result — by 'probe sort on Mixed.m1'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.mixedTwoCombinedBoundary ('Mixed.m2 result with object scope') mixedTwoModel/result — by 'Mixed.m2 object scope'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.tagBoundary ('Tag-indexed model') tagModel/result for PropertyKindCalculus.Tests.KindRequirementScope.tagA — by 'Tag A'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.thingAliasBoundary ('Thing-indexed model, aliased object scope') thingModel/result — by 'Thing first and two'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.thingBothBoundary ('Thing-indexed model, both scoped objects') thingModel/result — by 'Thing one and two'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.thingOneBoundary ('Thing-indexed model, one scoped object') thingModel/result for PropertyKindCalculus.Tests.KindRequirement.Thing.one — by 'Thing one'
[governed] PropertyKindCalculus.Tests.KindRequirementScope.thingSortBoundary ('Thing-indexed model, sort-scoped output') thingModel/result — by 'probe sort on Thing'
⊘ exempted PropertyKindCalculus.Tests.KindRequirementScope.decidedExemptBoundary ('exempt decided result without proof') model/result — the probe isolates a decided scope's missing proof
⊘ exempted PropertyKindCalculus.Tests.KindRequirementScope.mixedTwoExemptBoundary ('exempt Mixed.m2 result') mixedTwoModel/result — the fixed m2 object has sort tagS, not probeS
⊘ exempted PropertyKindCalculus.Tests.KindRequirementScope.opaqueExemptBoundary ('exempt opaque conditional result') opaqueExemptResultModel/result — the opaque output's Thing object cannot be determined statically
⚠ UNCHECKED PropertyKindCalculus.Tests.KindRequirementScope.UnresolvedOnly.unresolvedBoundary ('isolated opaque result') unresolvedModel/result — 'Thing one on isolated opaque result' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one: the result's 'Thing' object cannot be determined statically
⚠ UNCHECKED PropertyKindCalculus.Tests.KindRequirementScope.bareResultBoundary ('unindexed result') bareResultModel/result — 'bare-result object scope' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one: the result carries no 'Thing' index
⚠ UNCHECKED PropertyKindCalculus.Tests.KindRequirementScope.decidedNoProofBoundary ('decided result without proof') model/result — 'decided scope without proof': decided by 'PropertyKindCalculus.Tests.KindRequirementScope.anyB' with no valid decider proof
⚠ UNCHECKED PropertyKindCalculus.Tests.KindRequirementScope.decidedWrongProofBoundary ('decided result with proof for another member') oneModel/result — 'decider proof for another member': decided by 'PropertyKindCalculus.Tests.KindRequirementScope.isZero' with no valid decider proof
⚠ UNCHECKED PropertyKindCalculus.Tests.KindRequirementScope.opaqueResultBoundary ('opaque conditional result') opaqueResultModel/result — 'Thing one on opaque conditional result' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one: the result's 'Thing' object cannot be determined statically
⚠ UNCHECKED PropertyKindCalculus.Tests.KindRequirementScope.targetGenericBoundary ('generic Target result') targetGenericModel/result — 'probe sort on generic Target': the sort of a generic 'Target s' object cannot be determined statically
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.aliasedThingTwoBoundary ('aliased Thing.two result') aliasedThingTwoModel/result for PropertyKindCalculus.Tests.KindRequirement.Thing.two — 'Thing one on aliased Thing.two' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.mixedGenericBoundary ('generic Mixed result') mixedGenericModel/result for PropertyKindCalculus.Tests.KindRequirementScope.Mixed.m2 — 'probe sort on generic Mixed' scoped to sort 'PropertyKindCalculus.Tests.KindRequirement.probeS'; 'PropertyKindCalculus.Tests.KindRequirementScope.Mixed.m2' is of sort 'PropertyKindCalculus.Tests.KindRequirementScope.tagS'
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.mixedTwoBoundary ('Mixed.m2 result') mixedTwoModel/result — 'probe sort on Mixed.m2' scoped to sort 'PropertyKindCalculus.Tests.KindRequirement.probeS', but 'Mixed' objects are of sort 'PropertyKindCalculus.Tests.KindRequirementScope.tagS'
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.namedTagBoundary ('named Tag B result') namedTagBModel/result for PropertyKindCalculus.Tests.KindRequirementScope.tagB — 'Tag A on named Tag B' scoped to PropertyKindCalculus.Tests.KindRequirementScope.tagA
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.projectedCompositeBoundary ('projected composite Thing.two result') projectedCompositeModel/result for PropertyKindCalculus.Tests.KindRequirement.Thing.two — 'Thing one on projected composite' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.tagBoundary ('Tag-indexed model') tagModel/result for every other 'Tag' — 'Tag A' scoped to PropertyKindCalculus.Tests.KindRequirementScope.tagA
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.thingOneBoundary ('Thing-indexed model, one scoped object') thingModel/result for PropertyKindCalculus.Tests.KindRequirement.Thing.two — 'Thing one' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.thingTwoBoundary ('Thing.two-indexed model') thingTwoModel/result for PropertyKindCalculus.Tests.KindRequirement.Thing.two — 'Thing one on Thing two' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.thingWrongSortBoundary ('Thing-indexed model, wrong sort scope') thingModel/result — 'Tag sort on Thing' scoped to sort 'PropertyKindCalculus.Tests.KindRequirementScope.tagS', but 'Thing' objects are of sort 'PropertyKindCalculus.Tests.KindRequirement.probeS'
⚠ UNGOVERNED PropertyKindCalculus.Tests.KindRequirementScope.wrappedCompositeBoundary ('wrapped composite Thing.two result') wrappedCompositeModel/result for PropertyKindCalculus.Tests.KindRequirement.Thing.two — 'Thing one on wrapped composite' scoped to PropertyKindCalculus.Tests.KindRequirement.Thing.one
31 row(s) over 28 model boundary(ies): 12 governed, 3 exempted, 10 UNGOVERNED, 6 UNCHECKED — requirement-coverage violation
requirements: 31 provable, 0 empirical, 31 attested
-/
#guard_msgs (whitespace := lax) in
  #kind_requirement_coverage PropertyKindCalculus.Tests.KindRequirementScope

end PropertyKindCalculus.Tests.KindRequirementScope

namespace PropertyKindCalculus.Tests.KindRequirementDecidedValidation

open PropertyKindCalculus
open PropertyKindCalculus.Tests.KindRequirement
open PropertyKindCalculus.Tests.KindRequirementScope
open PropertyKindCalculus.Provenance (NodeId KindRef)

def decidedInputProofRequirement : Provenance.Requirement where
  name := "decider proof on an input"
  statement := "a decider proof may cover only a result port"
  kind := .provable
  governs := ``modelBoundary
  port := some ((NodeId.binder "x").within ``PropertyKindCalculus.Tests.KindRequirement.model)
  scope := .decided ``anyB
  deciderProof := some ``anyB_model
  attested := "decided-scope proof probe"

/--
error: 'decider proof on an input''s decider proof covers result ports only, but 'model/x' of 'requirement probe model' is not one
-/
#guard_msgs (whitespace := lax) in #kind_requirement decidedInputProofRequirement

def stringDecider (_ : String) : Bool := true

def decidedDeciderDoesNotApply : Provenance.Requirement where
  name := "decider does not apply to result"
  statement := "a decider must accept the governed member's result"
  kind := .provable
  governs := ``modelBoundary
  port := some (NodeId.result.within ``PropertyKindCalculus.Tests.KindRequirement.model)
  scope := .decided ``stringDecider
  deciderProof := some ``anyB_model
  attested := "decided-scope proof probe"

/--
error: 'PropertyKindCalculus.Tests.KindRequirementDecidedValidation.stringDecider' does not apply to what 'PropertyKindCalculus.Tests.KindRequirement.model' produces
-/
#guard_msgs in #kind_requirement decidedDeciderDoesNotApply

def decidedProofWithAllScope : Provenance.Requirement where
  name := "decider proof on an all scope"
  statement := "a decider proof requires a decided scope"
  kind := .provable
  governs := ``modelBoundary
  port := some (NodeId.result.within ``PropertyKindCalculus.Tests.KindRequirement.model)
  scope := .all
  deciderProof := some ``anyB_model
  attested := "decided-scope proof probe"

/--
error: 'decider proof on an all scope' has a decider proof, but its scope is not `.decided`
-/
#guard_msgs in #kind_requirement decidedProofWithAllScope

def decidedMissingProof : Provenance.Requirement where
  name := "missing decider proof declaration"
  statement := "a named decider proof must exist"
  kind := .provable
  governs := ``modelBoundary
  port := some (NodeId.result.within ``PropertyKindCalculus.Tests.KindRequirement.model)
  scope := .decided ``anyB
  deciderProof := some (Lean.Name.mkSimple "missingAnyBModelProof")
  attested := "decided-scope proof probe"

/--
error: the decider proof 'missingAnyBModelProof' is not a declaration
-/
#guard_msgs in #kind_requirement decidedMissingProof

end PropertyKindCalculus.Tests.KindRequirementDecidedValidation

namespace PropertyKindCalculus.Tests.KindRequirementSortValidation

open PropertyKindCalculus
open PropertyKindCalculus.Tests.KindRequirement
open PropertyKindCalculus.Tests.KindRequirementScope
open PropertyKindCalculus.Provenance (NodeId KindRef)

def bareResultSortRequirement : Provenance.Requirement where
  name := "sort scope on unindexed output"
  statement := "the bare result is governed by probeS"
  kind := .provable
  governs := ``bareResultBoundary
  port := some (NodeId.result.within ``bareResultModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

/--
error: 'sort scope on unindexed output' is scoped to sort 'PropertyKindCalculus.Tests.KindRequirement.probeS', but 'bareResultModel/result' of 'unindexed result' carries no object index — a sort scope quantifies over the objects an output belongs to; index the result by its object
-/
#guard_msgs (whitespace := lax) in #kind_requirement bareResultSortRequirement

def thingSortInputRequirement : Provenance.Requirement where
  name := "sort scope on input port"
  statement := "the input port is covered by a sort-scoped requirement"
  kind := .provable
  governs := ``thingOneBoundary
  port := some ((NodeId.binder "x").within ``thingModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

/--
error: 'sort scope on input port' is scoped to objects or a sort, but 'thingModel/x' of 'Thing-indexed model, one scoped object' is an input — an object or sort scope quantifies over the objects an output belongs to; govern a produced port
-/
#guard_msgs (whitespace := lax) in #kind_requirement thingSortInputRequirement

inductive Unsorted where
  | obj

def unsortedModel : IndividualQuantity Unsorted.obj bK Int := ⟨0⟩

def unsortedBoundary : Provenance.Contract NodeId KindRef where
  name := "unsorted object result"
  members := [``unsortedModel]
  ports := [⟨NodeId.result.within ``unsortedModel, .decl ``bK, .output⟩]
  exits := []

def unsortedSortRequirement : Provenance.Requirement where
  name := "sort scope without Sorted"
  statement := "an object without a Sorted instance has no declared sort"
  kind := .provable
  governs := ``unsortedBoundary
  port := some (NodeId.result.within ``unsortedModel)
  scope := .sort ``probeS
  attested := "coverage-domain probe"

/--
error: 'sort scope without Sorted' is scoped to sort 'PropertyKindCalculus.Tests.KindRequirement.probeS', but the objects of 'unsortedModel/result' ('Unsorted') declare no sort — give 'Unsorted' a `Sorted` instance
-/
#guard_msgs (whitespace := lax) in #kind_requirement unsortedSortRequirement

end PropertyKindCalculus.Tests.KindRequirementSortValidation

end Blanket
