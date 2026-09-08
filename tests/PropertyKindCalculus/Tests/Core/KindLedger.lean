/-
# Validation probes — `KindLedger` (the unkinded inventory of a declared scope)

The ledger is the unkinded reading gathered over an assembly and made into a worklist.
Four claims are checked here.

**It dedupes by member.** A helper called twice is two levels, so a single naked binder
would be counted twice — and dissecting a call would then *raise* the recorded debt while
strictly improving the reading. The probe calls one helper twice and pins one row.

**Its count is a predicate stated with its number**, and the empty case says what the
number means rather than printing `0`.

**Its gate is separate from its pin.** `#kind_unkinded` can express a violation, so it
cannot also be the check that none exists; `#kind_unkinded_clean` errors on a non-empty
ledger and is pinned on the scope that has reached zero.

**A subterm it cannot read leaves a row opaque, not the ledger empty.** A value may put a
`match` under a lambda of its own, where the discriminant is a loose bound variable and
`inferType` throws rather than answers. The reading is opaque there, and every row around
it still reports.

The JSON emitter is a pure function of the same rows, so it is decidable by evaluation.
-/
import PropertyKindCalculus.KindLedger

namespace PropertyKindCalculus.Tests.KindLedger

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)
open PropertyKindCalculus.KindLedger

/-- Does `sub` occur in `s`? Evaluation-only probe helper. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- A probe kind — the scaled operand. -/
def aK : KindOfProperty := { id := "kind-ledger probe a", scale := .ratio }
/-- A probe kind — the scaling factor. -/
def bK : KindOfProperty := { id := "kind-ledger probe b", scale := .ratio }
/-- A probe kind — the product. -/
def dK : KindOfProperty := { id := "kind-ledger probe d", scale := .ratio }

/-- A registered attestor, so the probe's mint is a declared source rather than a raw
one and the naked argument's flow into it is harvested. -/
@[kindAttest]
def probeAttest (k : KindOfProperty) (_reason : String) (m : Float) : Quantity k Float :=
  ⟨m⟩

/-- A helper with one naked binder: `n` carries no kind, and it mints the factor. -/
def scaledBy (n : Nat) (x : Quantity aK Float) : Quantity dK Float :=
  Quantity.mul (ProductKind.ofRatio aK bK dK) x (probeAttest bK "probe" n.toFloat)

/-- Two calls to it — two levels, one member. -/
def usesTwice (p q : Quantity aK Float) : Quantity dK Float :=
  Quantity.add (DifferenceKind.ofScale) (scaledBy 1 p) (scaledBy 2 q)

/-- The scope, declared as a contract so the ledger is read over a *boundary* rather than
over an ad-hoc list. -/
def probeScope : Provenance.Contract NodeId KindRef where
  name := "kind-ledger probe scope"
  members := [``usesTwice, ``scaledBy]
  ports := []
  exits := []

-- The assembly the ledger is read off: `scaledBy` appears at two call sites, so there
-- are two instance levels of the one member — and TWO red rows.
/--

info: kind assembly of 3 steps:
level usesTwice: walked
level scaledBy: walked
level scaledBy#2: walked
input usesTwice/p : aK
input usesTwice/q : aK
output usesTwice/result : dK
derived usesTwice/_1 : dK
derived usesTwice/_2 : dK
derived scaledBy/x : aK
derived scaledBy/result : dK
attested "probe" scaledBy/_1 : bK
derived scaledBy#2/x : aK
derived scaledBy#2/result : dK
attested "probe" scaledBy#2/_1 : bK
dK ± dK → dK ⟨usesTwice/_1, usesTwice/_2⟩ ⇒ usesTwice/result
[step scaledBy] aK → dK ⟨usesTwice/p⟩ ⇒ usesTwice/_1
[step scaledBy#2] aK → dK ⟨usesTwice/q⟩ ⇒ usesTwice/_2
aK · bK → dK ⟨scaledBy/x, scaledBy/_1⟩ ⇒ scaledBy/result
aK · bK → dK ⟨scaledBy#2/x, scaledBy#2/_1⟩ ⇒ scaledBy#2/result
aK → aK ⟨usesTwice/p⟩ ⇒ scaledBy/x
aK → aK ⟨usesTwice/q⟩ ⇒ scaledBy#2/x
unkinded input scaledBy/n : Nat
unkinded input scaledBy#2/n : Nat
unkinded flow: scaledBy/n ⇒ scaledBy/_1
unkinded flow: scaledBy#2/n ⇒ scaledBy#2/_1
cites: usesTwice → scaledBy
well-formed: true
-/
#guard_msgs in #kind_assembly probeScope

-- Two instances, two red rows in the graph — and ONE row in the ledger, because the
-- debt belongs to the declaration and a call site is not a second naked binder.
/--
info: unkinded ledger of 'kind-ledger probe scope':
unkinded: 1 position(s), 1 flow(s)
unkinded input scaledBy/n : Nat
unkinded flow: scaledBy/n ⇒ scaledBy/_1
-/
#guard_msgs in #kind_unkinded probeScope

/-- The same helper with the count kinded — the shape the fix takes. -/
def scaledByQ (n : Quantity bK Float) (x : Quantity aK Float) : Quantity dK Float :=
  Quantity.mul (ProductKind.ofRatio aK bK dK) x n

/-- A scope with nothing naked in it. -/
def cleanScope : Provenance.Contract NodeId KindRef where
  name := "kind-ledger clean scope"
  members := [``scaledByQ]
  ports := [⟨(NodeId.binder "n").within ``scaledByQ, .decl ``bK, .input⟩,
            ⟨(NodeId.binder "x").within ``scaledByQ, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``scaledByQ, .decl ``dK, .output⟩]
  exits := []

-- The empty ledger says what the number means.
/--
info: unkinded ledger of 'kind-ledger clean scope':
unkinded: none — every position carries a kind
-/
#guard_msgs in #kind_unkinded cleanScope

-- And the gate — separate from the pin, because a pin that can express a violation is
-- not a check that there is none.
/-- info: unkinded-clean: every position of 'kind-ledger clean scope' carries a kind -/
#guard_msgs in #kind_unkinded_clean cleanScope

/-! ## A selection under a binder the walk carries

The ledger walks a declaration's value, and a value can put a `match` under a lambda of its
own — an attested reading that is a *function*, selecting on that function's argument. The
discriminant there is a loose bound variable, and asking for its type is not a wrong answer
but a thrown one: `inferType` rejects a loose bound variable, and the exception takes the
whole ledger with it, one unreadable subterm anywhere in a scope erasing every row in it.
The reading a bound discriminant must get is the one every open reading gets — opaque —
and the rows around it must survive. Both pins below fail if the walk reads it. -/

/-- An attested reading that is a function, selecting on its own argument: the `match`
sits under a binder the walk carries, so its discriminant is still bound when the walk
arrives. -/
def selectUnderBinder (p q : Float) : Quantity aK (Bool → Float) :=
  .attest "a reading selected per argument" (fun b => match b with | true => p | false => q)

/-- The scope: nothing is ported, so both naked magnitudes are rows — the point being
that they are *reported*, not lost to an exception raised inside the selection. -/
def selectScope : Provenance.Contract NodeId KindRef where
  name := "kind-ledger selection scope"
  members := [``selectUnderBinder]
  ports := []
  exits := []

/--
info: unkinded ledger of 'kind-ledger selection scope':
unkinded: 2 position(s), 2 flow(s)
unkinded input selectUnderBinder/p : Float
unkinded input selectUnderBinder/q : Float
unkinded flow: selectUnderBinder/p ⇒ selectUnderBinder/_1
unkinded flow: selectUnderBinder/q ⇒ selectUnderBinder/_1
-/
#guard_msgs in #kind_unkinded selectScope

-- The graph the ledger is gathered from reads the same way: one attested mint at `aK`,
-- with both magnitudes flowing into it naked. The selection contributes no edge — an
-- open discriminant is opaque, which is a reading, not a failure.
/--
info: kind assembly of 1 steps:
level selectUnderBinder: walked
output selectUnderBinder/result : aK
attested "a reading selected per argument" selectUnderBinder/_1 : aK
aK → aK ⟨selectUnderBinder/_1⟩ ⇒ selectUnderBinder/result
unkinded input selectUnderBinder/p : Float
unkinded input selectUnderBinder/q : Float
unkinded flow: selectUnderBinder/p ⇒ selectUnderBinder/_1
unkinded flow: selectUnderBinder/q ⇒ selectUnderBinder/_1
well-formed: true
-/
#guard_msgs in #kind_assembly selectScope

/-! ## The JSON emission

A pure function of the same rows, so the figure, the pin and the file are three renderings
of one value rather than three claims that have to be kept in agreement. -/

/-- The interface tallies the emitter is checked on — the denominator beside the rows. -/
def probeMembers : Array MemberRow :=
  #[⟨"scaledBy#1", "scaledBy", "walked", ⟨1, 0, 1, 2, 1⟩⟩]

/-- The rows the emitter is checked on. -/
def probeRows : Array Row :=
  #[⟨"s", "scaledBy", "n", .position .input "Nat"⟩,
    ⟨"s", "scaledBy", "n", .flow "_1"⟩]

/-- The counts are in the document, not only in the rows. -/
example : hasSub (toJson "s" probeMembers probeRows) "\"positions\": 1" := by native_decide
example : hasSub (toJson "s" probeMembers probeRows) "\"flows\": 1" := by native_decide

/-- A position row carries its direction and the type the signature states. -/
example :
    hasSub (toJson "s" probeMembers probeRows)
      "{\"member\": \"scaledBy\", \"node\": \"n\", \"silence\": \"position\", \"dir\": \"input\", \"type\": \"Nat\"}" := by
  native_decide

/-- A flow row carries its target instead. -/
example :
    hasSub (toJson "s" probeMembers probeRows)
      "{\"member\": \"scaledBy\", \"node\": \"n\", \"silence\": \"flow\", \"target\": \"_1\"}" := by
  native_decide

/-- The empty ledger emits an empty array, not a missing key: a reviewer's tooling reads
one shape whether or not there is debt. -/
example : hasSub (toJson "s" probeMembers #[]) "\"rows\": []" := by native_decide

/-- The denominator: a scope with no rows still reports the interface it was read over,
one entry per *level* — a call site has an interface even when it contributes no debt. -/
example :
    hasSub (toJson "s" probeMembers #[])
      "{\"level\": \"scaledBy#1\", \"member\": \"scaledBy\", \"mode\": \"walked\", \"in\": 1, \"config\": 0, \"out\": 1, \"interior\": 2, \"unkinded\": 1}" := by
  native_decide

/-- An assembly with no levels emits an empty array there too, for the same reason. -/
example : hasSub (toJson "s" #[] #[]) "\"members\": []" := by native_decide

end PropertyKindCalculus.Tests.KindLedger
