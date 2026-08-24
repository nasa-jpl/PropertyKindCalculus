/-
# Validation probes — the theorem edge (`Provenance.Relation`, `#kind_relation`)

`agrees` compares a declaration with the graph its members compute; `discharges` compares
two declarations. Neither can say that one boundary inverts another, and that is a theorem
rather than a port list. `#kind_relation` checks everything around such a proof, and throws
on every failure — so the command is the report and the gate at once, and the probes below
pin its refusals as well as its acceptance.

Three refusals are pinned: a witness that is not a theorem, a witness whose conclusion is
not the shape the claimed kind names, and — the check that keeps the edge from being
decoration — a witness that names no member of one boundary or the other.
-/
import PropertyKindCalculus.KindIncidence

namespace PropertyKindCalculus.Tests.KindRelation

open PropertyKindCalculus

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
def fwdBoundary : Provenance.Contract String String where
  name := "relation probe forward"
  members := ["PropertyKindCalculus.Tests.KindRelation.probeFwd"]
  ports := [⟨"probeFwd/x", "aK", .input⟩, ⟨"probeFwd/result", "bK", .output⟩]
  exits := []

/-- The retrieval's declared boundary. -/
def invBoundary : Provenance.Contract String String where
  name := "relation probe retrieval"
  members := ["PropertyKindCalculus.Tests.KindRelation.probeInv"]
  ports := [⟨"probeInv/y", "bK", .input⟩, ⟨"probeInv/result", "aK", .output⟩]
  exits := []

/-- The edge: the retrieval inverts the forward, and here is the proof. -/
def retrievalInvertsForward : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.KindRelation.invBoundary"
  right := "PropertyKindCalculus.Tests.KindRelation.fwdBoundary"
  kind := .inverts
  witness := "PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd"
  says := "the retrieval recovers the argument the forward consumed"

/--
info: kind relation: 'relation probe retrieval' inverts 'relation probe forward'
witness: PropertyKindCalculus.Tests.KindRelation.probeInv_probeFwd
says: the retrieval recovers the argument the forward consumed
names on the left: PropertyKindCalculus.Tests.KindRelation.probeInv
names on the right: PropertyKindCalculus.Tests.KindRelation.probeFwd
axioms: propext
-/
#guard_msgs in #kind_relation retrievalInvertsForward

/-! ## The refusals -/

/-- A definition asserts nothing, so it cannot carry a relation. -/
def witnessIsADefinition : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.KindRelation.invBoundary"
  right := "PropertyKindCalculus.Tests.KindRelation.fwdBoundary"
  kind := .inverts
  witness := "PropertyKindCalculus.Tests.KindRelation.probeInv"

/--
error: the witness 'PropertyKindCalculus.Tests.KindRelation.probeInv' is not a theorem — a relation between two boundaries is carried by a proof, and a definition asserts nothing
-/
#guard_msgs in #kind_relation witnessIsADefinition

/-- A theorem that names neither boundary is a true statement about something else. -/
def witnessIsAStranger : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.KindRelation.invBoundary"
  right := "PropertyKindCalculus.Tests.KindRelation.fwdBoundary"
  kind := .equals
  witness := "PropertyKindCalculus.Tests.KindRelation.probeStranger"

/--
error: 'PropertyKindCalculus.Tests.KindRelation.probeStranger' names no member of 'relation probe retrieval' — a theorem that does not mention a boundary is not about it
-/
#guard_msgs in #kind_relation witnessIsAStranger

/-- The claimed kind names a shape, and the conclusion has to have it. -/
def boundClaimedAsEquality : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.KindRelation.invBoundary"
  right := "PropertyKindCalculus.Tests.KindRelation.fwdBoundary"
  kind := .equals
  witness := "PropertyKindCalculus.Tests.KindRelation.probeBounded"

/--
error: 'PropertyKindCalculus.Tests.KindRelation.probeBounded' is claimed to state an equality, but its conclusion is headed by 'LE.le', not 'Eq'
-/
#guard_msgs in #kind_relation boundClaimedAsEquality

/-- The same witness, claimed as what it is. -/
def boundClaimedAsBound : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.KindRelation.invBoundary"
  right := "PropertyKindCalculus.Tests.KindRelation.fwdBoundary"
  kind := .boundedBy
  witness := "PropertyKindCalculus.Tests.KindRelation.probeBounded"
  says := "the round trip moves the carrier by at most 2"

/--
info: kind relation: 'relation probe retrieval' bounded by 'relation probe forward'
witness: PropertyKindCalculus.Tests.KindRelation.probeBounded
says: the round trip moves the carrier by at most 2
names on the left: PropertyKindCalculus.Tests.KindRelation.probeInv
names on the right: PropertyKindCalculus.Tests.KindRelation.probeFwd
axioms: propext, Quot.sound
-/
#guard_msgs in #kind_relation boundClaimedAsBound

end PropertyKindCalculus.Tests.KindRelation
