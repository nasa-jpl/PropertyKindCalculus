/-
# Validation probes — the theorem edge (`Provenance.Relation`, `#kind_relation`)

`agrees` compares a declaration with the graph its members compute; `discharges` compares
two declarations. Neither can say that one boundary inverts another, and that is a theorem
rather than a port list. `#kind_relation` checks everything around such a proof, and throws
on every failure — so the command is the report and the gate at once, and the probes below
pin its refusals as well as its acceptance.

The refusals pinned here cover every check: a witness that is not a theorem; a witness
whose conclusion is not the shape the claimed kind names — including the per-kind shapes,
an inversion whose equality never composes the two boundaries and a refinement that binds
no hypothesis; a tolerance that is not a declared `Quantity` at an output port's kind; a
named side condition the statement does not mention; a license rung with no repair and no
restatement, and one resting on a definition; and — the check that keeps the edge from
being decoration — a witness that names no member of one boundary or the other. The
survey `#kind_relations` closes the file: every edge above in one pinned report, the
violations rendered as `✗` rows.
-/
import PropertyKindCalculus.KindIncidence

namespace PropertyKindCalculus.Tests.KindRelation

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)

/-- A probe kind — the forward's argument. -/
def aK : KindOfProperty := { id := "relation probe a", scale := .ratio }
/-- A probe kind — the forward's answer. -/
def bK : KindOfProperty := { id := "relation probe b", scale := .ratio }

/-- The forward the right-hand boundary is claimed for. -/
def probeFwd (x : Quantity aK Int) : Quantity bK Int := ⟨x.magnitude + 1⟩

/-- The retrieval the left-hand boundary is claimed for. -/
def probeInv (y : Quantity bK Int) : Quantity aK Int := ⟨y.magnitude - 1⟩

/-- The witness: the retrieval recovers what the forward consumed. -/
theorem probeInv_probeFwd (x : Quantity aK Int) : probeInv (probeFwd x) = x := by
  cases x; simp [probeInv, probeFwd]

/-- A true theorem about neither boundary. -/
theorem probeStranger : (1 : Int) + 1 = 2 := by decide

/-- A true theorem about both boundaries whose conclusion is an order relation. -/
theorem probeBounded (x : Quantity aK Int) :
    (probeFwd x).magnitude - (probeInv (probeFwd x)).magnitude ≤ 2 := by
  cases x; simp [probeFwd, probeInv]; omega

/-- The forward's declared boundary. -/
def fwdBoundary : Provenance.Contract NodeId KindRef where
  name := "relation probe forward"
  members := [``probeFwd]
  ports := [⟨((NodeId.binder "x").within ``probeFwd), .decl ``aK, .input⟩, ⟨(NodeId.result.within ``probeFwd), .decl ``bK, .output⟩]
  exits := []

/-- The retrieval's declared boundary. -/
def invBoundary : Provenance.Contract NodeId KindRef where
  name := "relation probe retrieval"
  members := [``probeInv]
  ports := [⟨((NodeId.binder "y").within ``probeInv), .decl ``bK, .input⟩, ⟨(NodeId.result.within ``probeInv), .decl ``aK, .output⟩]
  exits := []

/-- The edge: the retrieval inverts the forward, and here is the proof. -/
def retrievalInvertsForward : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .inverts
  witness := ``probeInv_probeFwd
  claim := "the retrieval recovers the argument the forward consumed"

/--
info: kind relation: 'relation probe retrieval' inverts 'relation probe forward'
witness: PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd
claims: the retrieval recovers the argument the forward consumed
names on the left: PropertyKindCalculus.Tests.KindRelation.probeInv
names on the right: PropertyKindCalculus.Tests.KindRelation.probeFwd
axioms: propext
-/
#guard_msgs in #kind_relation retrievalInvertsForward

/-! ## The refusals -/

/-- A definition asserts nothing, so it cannot carry a relation. -/
def witnessIsADefinition : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .inverts
  witness := ``probeInv

/--
error: the witness 'PropertyKindCalculus.Tests.KindRelation.probeInv' is not a theorem — a relation between two boundaries is carried by a proof, and a definition asserts nothing
-/
#guard_msgs in #kind_relation witnessIsADefinition

/-- A theorem that names neither boundary is a true statement about something else. -/
def witnessIsAStranger : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .equals
  witness := ``probeStranger

/--
error: 'PropertyKindCalculus.Tests.KindRelation.probeStranger' names no member of 'relation probe retrieval' — a theorem that does not mention a boundary is not about it
-/
#guard_msgs in #kind_relation witnessIsAStranger

/-- The claimed kind names a shape, and the conclusion has to have it. -/
def boundClaimedAsEquality : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .equals
  witness := ``probeBounded

/--
error: 'PropertyKindCalculus.Tests.KindRelation.probeBounded' is claimed to state an equality, but its conclusion is headed by 'LE.le', not 'Eq'
-/
#guard_msgs in #kind_relation boundClaimedAsEquality

/-- The same witness, claimed as what it is. -/
def boundClaimedAsBound : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .boundedBy
  witness := ``probeBounded
  claim := "the round trip moves the carrier by at most 2"

/--
info: kind relation: 'relation probe retrieval' bounded by 'relation probe forward'
witness: PropertyKindCalculus.Tests.KindRelation.probeBounded
claims: the round trip moves the carrier by at most 2
names on the left: PropertyKindCalculus.Tests.KindRelation.probeInv
names on the right: PropertyKindCalculus.Tests.KindRelation.probeFwd
axioms: propext, Quot.sound
-/
#guard_msgs in #kind_relation boundClaimedAsBound

/-! ## The refinement shape — the same value under a stated hypothesis -/

/-- The domain the clamped retrieval agrees on, named so the edge can list it. -/
def probeDomain (y : Quantity bK Int) : Prop := 1 ≤ y.magnitude

/-- A second retrieval, clamped at zero — it answers as `probeInv` does only on
`probeDomain`. -/
def probeInvClamped (y : Quantity bK Int) : Quantity aK Int := ⟨max (y.magnitude - 1) 0⟩

/-- The witness: the clamped retrieval answers as the retrieval does on the named
domain. -/
theorem probeInvClamped_probeInv (y : Quantity bK Int) (h : probeDomain y) :
    (probeInvClamped y).magnitude = (probeInv y).magnitude := by
  cases y with
  | mk m => simp [probeInvClamped, probeInv, probeDomain] at h ⊢; omega

/-- The clamped retrieval's declared boundary. -/
def clampedBoundary : Provenance.Contract NodeId KindRef where
  name := "relation probe clamped retrieval"
  members := [``probeInvClamped]
  ports := [⟨((NodeId.binder "y").within ``probeInvClamped), .decl ``bK, .input⟩,
            ⟨(NodeId.result.within ``probeInvClamped), .decl ``aK, .output⟩]
  exits := []

/-- The edge: the clamped retrieval refines the retrieval, under the named domain — the
side condition is listed at the edge, and the check demands the statement mention it. -/
def clampedRefinesRetrieval : Provenance.Relation where
  left := ``clampedBoundary
  right := ``invBoundary
  kind := .refines
  witness := ``probeInvClamped_probeInv
  claim := "the clamped retrieval answers as the retrieval does wherever the input \
    magnitude is at least one"
  hypotheses := [``probeDomain]

/--
info: kind relation: 'relation probe clamped retrieval' refines 'relation probe retrieval'
witness: PropertyKindCalculus.Tests.KindRelation.probeInvClamped_probeInv
claims: the clamped retrieval answers as the retrieval does wherever the input magnitude is at least one
hypotheses: PropertyKindCalculus.Tests.KindRelation.probeDomain
names on the left: PropertyKindCalculus.Tests.KindRelation.probeInvClamped
names on the right: PropertyKindCalculus.Tests.KindRelation.probeInv
axioms: propext, Quot.sound
-/
#guard_msgs in #kind_relation clampedRefinesRetrieval

/-- The same claim with a witness that binds no hypothesis: a refinement with nothing
stated is an equality claim, and is refused as one. -/
def refinesWithoutHypothesis : Provenance.Relation where
  left := ``clampedBoundary
  right := ``invBoundary
  kind := .refines
  witness := ``probeInv_probeFwd

/--
error: 'PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd' is claimed to hold under a stated hypothesis, but its statement binds none — a refinement with no hypothesis is an equality claim
-/
#guard_msgs in #kind_relation refinesWithoutHypothesis

/-! ## The inversion shape — the round trip must be in the statement -/

/-- A true equality mentioning both boundaries whose sides never compose them: each side
names one boundary alone, so no side is a round trip. -/
theorem probeSidesApart (x : Quantity aK Int) (y : Quantity bK Int) :
    (probeFwd x).magnitude - (probeFwd x).magnitude
      = (probeInv y).magnitude - (probeInv y).magnitude := by simp

/-- Claimed as an inversion, the split statement is refused: mentioning both boundaries
is not the same as composing them. -/
def invertsWithoutRoundTrip : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .inverts
  witness := ``probeSidesApart

/--
error: 'PropertyKindCalculus.Tests.KindRelation.probeSidesApart' is claimed to state an inversion, but neither side of its equality composes a member of 'relation probe retrieval' with a member of 'relation probe forward' — the round trip is not in the statement
-/
#guard_msgs in #kind_relation invertsWithoutRoundTrip

/-! ## The tolerance — a bound is governed by a kinded quantity -/

/-- The declared tolerance: a quantity at the retrieval's output kind. -/
def probeTol : Quantity aK Int := ⟨2⟩

/-- A quantity at the input side's kind — no produced port carries it. -/
def probeTolWrongKind : Quantity bK Int := ⟨2⟩

/-- The bound edge, its tolerance named: the declaration is checked to be a `Quantity`
at the kind of an output port of the left boundary. -/
def boundWithTolerance : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .boundedBy
  witness := ``probeBounded
  claim := "the round trip moves the carrier by at most the declared tolerance"
  tolerance := ``probeTol

/--
info: kind relation: 'relation probe retrieval' bounded by 'relation probe forward'
witness: PropertyKindCalculus.Tests.KindRelation.probeBounded
claims: the round trip moves the carrier by at most the declared tolerance
tolerance: PropertyKindCalculus.Tests.KindRelation.probeTol : aK
names on the left: PropertyKindCalculus.Tests.KindRelation.probeInv
names on the right: PropertyKindCalculus.Tests.KindRelation.probeFwd
axioms: propext, Quot.sound
-/
#guard_msgs in #kind_relation boundWithTolerance

/-- The same edge with a tolerance at the wrong kind: `bK` is what the retrieval
consumes, not what it produces, so no output port is governed by it. -/
def toleranceAtTheWrongKind : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .boundedBy
  witness := ``probeBounded
  tolerance := ``probeTolWrongKind

/--
error: the tolerance 'PropertyKindCalculus.Tests.KindRelation.probeTolWrongKind' is a quantity at kind 'bK', which is not the kind of any output port of 'relation probe retrieval' — a bound governs what the boundary produces
-/
#guard_msgs in #kind_relation toleranceAtTheWrongKind

/-- The same edge with a tolerance that is not a quantity at all. -/
def toleranceIsNotAQuantity : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .boundedBy
  witness := ``probeBounded
  tolerance := ``probeDomain

/--
error: the tolerance 'PropertyKindCalculus.Tests.KindRelation.probeDomain' is not a 'Quantity' — a tolerance is a kinded quantity, not a bare number
-/
#guard_msgs in #kind_relation toleranceIsNotAQuantity

/-! ## The named side conditions — listed means stated -/

/-- The inversion with a hypothesis list naming a declaration the statement never
mentions: a side condition the statement does not state is not one the claim holds
under. -/
def hypothesisNotInStatement : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .inverts
  witness := ``probeInv_probeFwd
  hypotheses := [``probeTol]

/--
error: 'PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd' does not mention the hypothesis 'PropertyKindCalculus.Tests.KindRelation.probeTol' — a side condition the statement does not state is not one the claim holds under
-/
#guard_msgs in #kind_relation hypothesisNotInStatement

/-! ## The license clause — a rung is answered for by name -/

/-- The inversion extended to a second rung, restated by name: the evidence is checked
to be a sorry-free theorem. -/
def licensedInversion : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .inverts
  witness := ``probeInv_probeFwd
  claim := "the retrieval recovers the argument the forward consumed"
  licenses := [⟨"Int", .restated ``probeInv_probeFwd⟩]

/--
info: kind relation: 'relation probe retrieval' inverts 'relation probe forward'
witness: PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd
claims: the retrieval recovers the argument the forward consumed
license: Int — restated by 'PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd'
names on the left: PropertyKindCalculus.Tests.KindRelation.probeInv
names on the right: PropertyKindCalculus.Tests.KindRelation.probeFwd
axioms: propext
-/
#guard_msgs in #kind_relation licensedInversion

/-- A rung claimed with no repair and no restatement: transfer is not assumed. -/
def licenseClaimsWithoutEvidence : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .inverts
  witness := ``probeInv_probeFwd
  licenses := [⟨"FP32", .exact .anonymous⟩]

/--
error: the license at rung 'FP32' claims the relation with no repair and no restatement — name the repair theorem that carries it across, or the witness that restates it at that rung
-/
#guard_msgs in #kind_relation licenseClaimsWithoutEvidence

/-- A rung resting on a definition: a transfer is carried by a proof. -/
def licenseRestsOnADefinition : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .inverts
  witness := ``probeInv_probeFwd
  licenses := [⟨"FP32", .nonneg ``probeInv⟩]

/--
error: the license at rung 'FP32' names 'PropertyKindCalculus.Tests.KindRelation.probeInv', which is not a theorem — a transfer is carried by a proof
-/
#guard_msgs in #kind_relation licenseRestsOnADefinition

/-! ## The survey — every edge in scope, one line each, violations in the report -/

/--
info: kind relations — 15 theorem edge(s), 10 violated
  PropertyKindCalculus.Tests.KindRelation.boundClaimedAsBound: 'relation probe retrieval' bounded by 'relation probe forward' — PropertyKindCalculus.Tests.KindRelation.probeBounded
  ✗ PropertyKindCalculus.Tests.KindRelation.boundClaimedAsEquality: 'PropertyKindCalculus.Tests.KindRelation.probeBounded' is claimed to state an equality, but its conclusion is headed by 'LE.le', not 'Eq'
  PropertyKindCalculus.Tests.KindRelation.boundWithTolerance: 'relation probe retrieval' bounded by 'relation probe forward' — PropertyKindCalculus.Tests.KindRelation.probeBounded [tolerance: PropertyKindCalculus.Tests.KindRelation.probeTol]
  PropertyKindCalculus.Tests.KindRelation.clampedRefinesRetrieval: 'relation probe clamped retrieval' refines 'relation probe retrieval' — PropertyKindCalculus.Tests.KindRelation.probeInvClamped_probeInv
  ✗ PropertyKindCalculus.Tests.KindRelation.hypothesisNotInStatement: 'PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd' does not mention the hypothesis 'PropertyKindCalculus.Tests.KindRelation.probeTol' — a side condition the statement does not state is not one the claim holds under
  ✗ PropertyKindCalculus.Tests.KindRelation.invertsWithoutRoundTrip: 'PropertyKindCalculus.Tests.KindRelation.probeSidesApart' is claimed to state an inversion, but neither side of its equality composes a member of 'relation probe retrieval' with a member of 'relation probe forward' — the round trip is not in the statement
  ✗ PropertyKindCalculus.Tests.KindRelation.licenseClaimsWithoutEvidence: the license at rung 'FP32' claims the relation with no repair and no restatement — name the repair theorem that carries it across, or the witness that restates it at that rung
  ✗ PropertyKindCalculus.Tests.KindRelation.licenseRestsOnADefinition: the license at rung 'FP32' names 'PropertyKindCalculus.Tests.KindRelation.probeInv', which is not a theorem — a transfer is carried by a proof
  PropertyKindCalculus.Tests.KindRelation.licensedInversion: 'relation probe retrieval' inverts 'relation probe forward' — PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd [rungs: Int]
  ✗ PropertyKindCalculus.Tests.KindRelation.refinesWithoutHypothesis: 'PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd' is claimed to hold under a stated hypothesis, but its statement binds none — a refinement with no hypothesis is an equality claim
  PropertyKindCalculus.Tests.KindRelation.retrievalInvertsForward: 'relation probe retrieval' inverts 'relation probe forward' — PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd
  ✗ PropertyKindCalculus.Tests.KindRelation.toleranceAtTheWrongKind: the tolerance 'PropertyKindCalculus.Tests.KindRelation.probeTolWrongKind' is a quantity at kind 'bK', which is not the kind of any output port of 'relation probe retrieval' — a bound governs what the boundary produces
  ✗ PropertyKindCalculus.Tests.KindRelation.toleranceIsNotAQuantity: the tolerance 'PropertyKindCalculus.Tests.KindRelation.probeDomain' is not a 'Quantity' — a tolerance is a kinded quantity, not a bare number
  ✗ PropertyKindCalculus.Tests.KindRelation.witnessIsADefinition: the witness 'PropertyKindCalculus.Tests.KindRelation.probeInv' is not a theorem — a relation between two boundaries is carried by a proof, and a definition asserts nothing
  ✗ PropertyKindCalculus.Tests.KindRelation.witnessIsAStranger: 'PropertyKindCalculus.Tests.KindRelation.probeStranger' names no member of 'relation probe retrieval' — a theorem that does not mention a boundary is not about it
-/
#guard_msgs (whitespace := lax) in
#kind_relations PropertyKindCalculus.Tests.KindRelation

end PropertyKindCalculus.Tests.KindRelation
