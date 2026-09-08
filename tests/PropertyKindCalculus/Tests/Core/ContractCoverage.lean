/-
`Tests.Core.ContractCoverage` — the indexed probe for the three censuses over declared
boundaries (`PropertyKindCalculus.ContractCoverage`): `#kind_relation_coverage` (M12),
`#kind_mereology_coverage` (M15), `#kind_inversion_coverage` (M21's domain half), and their
gates.

One probe world, every verdict class of every census exercised, the full reports pinned:

  * a forward and a retrieval, joined by an `inverts` edge — the retrieval guarded by a
    `conditional` port with a named decider, both boundaries' produced ports classed;
  * an inverted boundary with an `output` port and nothing else declared: witnessed (M12),
    `UNDECLARED` (M15), `UNGUARDED` (M21);
  * an orphan no edge names: `UNWITNESSED`, and outside M21's population;
  * `@[kindRelationFree]` and `@[kindInversionTotal]` exemptions with their reasons, and a
    boundary carrying both marks *stale* — an edge and a conditional port have since arrived,
    and the declarations win over the marks;
  * a `@[kindCounterexample]` contract (listed as exempted, a subject of nothing) and a
    `@[kindCounterexample]` edge naming the orphan, which must neither witness nor enroll it;
  * a contract at `Nat` nodes: in the population by type, decided by name for M12,
    `UNREADABLE` for M15, absent from M21 (nothing inverts it).

Then each gate: it throws on the probe world, and passes silently on a sub-namespace where
everything is declared or exempted — an exemption is not a violation and must not fire it.
Finally the attributes' own refusals: a mark on something that is not a `Provenance.Contract`,
and a mark with a blank reason.
-/
import PropertyKindCalculus.ContractCoverage

namespace PropertyKindCalculus.Tests.ContractCoverage

open PropertyKindCalculus

/-! ## The probe world -/

/-- A probe kind — the forward's argument. -/
def aK : KindOfProperty := { id := "contract coverage probe a", scale := .ratio }
/-- A probe kind — the forward's answer. -/
def bK : KindOfProperty := { id := "contract coverage probe b", scale := .ratio }

namespace Good

/-- The forward. -/
def fwd (x : Quantity aK Int) : Quantity bK Int := ⟨x.magnitude + 1⟩

/-- The retrieval inverting it. -/
def inv (y : Quantity bK Int) : Quantity aK Int := ⟨y.magnitude - 1⟩

/-- The witness. -/
theorem inv_fwd (x : Quantity aK Int) : inv (fwd x) = x := by
  cases x; simp [inv, fwd]

/-- The domain predicate the retrieval's conditional port names as its decider. -/
def inDomain (y : Quantity bK Int) : Bool := y.magnitude > 0

/-- The forward's boundary: witnessed by the edge below; its output classed. -/
def fwdBoundary : Provenance.Contract String String where
  name := "coverage probe forward"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.fwd"]
  ports := [⟨"fwd/x", "aK", .input⟩, ⟨"fwd/result", "bK", .output⟩]
  exits := []
  aggregations := [("fwd/result", .intensive)]

/-- The retrieval's boundary: the left side of the inversion edge, guarded by a conditional
port whose decider is named, its port classed. -/
def invBoundary : Provenance.Contract String String where
  name := "coverage probe retrieval"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.inv"]
  ports := [⟨"inv/y", "bK", .input⟩, ⟨"inv/result", "aK", .conditional⟩]
  exits := []
  deciders := [("inv/result", "PropertyKindCalculus.Tests.ContractCoverage.Good.inDomain")]
  aggregations := [("inv/result", .wholeProper)]

/-- The theorem edge between them. -/
def retrievalInvertsForward : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary"
  right := "PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary"
  kind := .inverts
  witness := "PropertyKindCalculus.Tests.ContractCoverage.Good.inv_fwd"

end Good

namespace Bare

/-- Inverted, with an `output` port and nothing else declared. -/
def unguardedInverse : Provenance.Contract String String where
  name := "coverage probe retrieval, unguarded"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.inv"]
  ports := [⟨"inv/y", "bK", .input⟩, ⟨"inv/result", "aK", .output⟩]
  exits := []

/-- The edge that makes it an inverted boundary. -/
def unguardedInverts : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse"
  right := "PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary"
  kind := .inverts
  witness := "PropertyKindCalculus.Tests.ContractCoverage.Good.inv_fwd"

/-- No edge names it; its output is unclassed; nothing inverts it. -/
def orphan : Provenance.Contract String String where
  name := "coverage probe orphan"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.fwd"]
  ports := [⟨"fwd/x", "aK", .input⟩, ⟨"fwd/result", "bK", .output⟩]
  exits := []

end Bare

namespace Exempt

/-- No edge, on purpose. Its port is classed. -/
@[kindRelationFree "a data-movement boundary: its behavior is the identity on kinds, and \
  there is no measurement model to carry"]
def dataMove : Provenance.Contract String String where
  name := "coverage probe data movement"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.fwd"]
  ports := [⟨"fwd/x", "aK", .input⟩, ⟨"fwd/result", "bK", .output⟩]
  exits := []
  aggregations := [("fwd/result", .countKeyed "pixel")]

/-- Inverted, no conditional port, exempted as total. -/
@[kindInversionTotal "total on its input type: every integer is the forward's image of one, \
  so there is no outside to detect"]
def totalInverse : Provenance.Contract String String where
  name := "coverage probe retrieval, total"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.inv"]
  ports := [⟨"inv/y", "bK", .input⟩, ⟨"inv/result", "aK", .output⟩]
  exits := []
  aggregations := [("inv/result", .intensive)]

/-- The edge that makes it an inverted boundary. -/
def totalInverts : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse"
  right := "PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary"
  kind := .inverts
  witness := "PropertyKindCalculus.Tests.ContractCoverage.Good.inv_fwd"

/-- Both marks, stale: an edge now names the boundary and a conditional port guards it, and
both declarations win over the marks. -/
@[kindRelationFree "stale — an edge now names this boundary",
  kindInversionTotal "stale — a conditional port now guards it"]
def staleMarks : Provenance.Contract String String where
  name := "coverage probe, marks gone stale"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.inv"]
  ports := [⟨"inv/y", "bK", .input⟩, ⟨"inv/result", "aK", .conditional⟩]
  exits := []
  aggregations := [("inv/result", .intensive)]

/-- The edge that arrived after the mark. -/
def staleInverts : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks"
  right := "PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary"
  kind := .inverts
  witness := "PropertyKindCalculus.Tests.ContractCoverage.Good.inv_fwd"

/-- A deliberate misdeclaration kept: a subject of nothing, listed as exempted. -/
@[kindCounterexample]
def keptCounterexample : Provenance.Contract String String :=
  { Bare.orphan with name := "coverage probe orphan, kept as a counterexample" }

/-- A deliberately broken edge naming the orphan: it witnesses nothing and enrolls nothing. -/
@[kindCounterexample]
def keptBrokenEdge : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.ContractCoverage.Bare.orphan"
  right := "PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary"
  kind := .inverts
  witness := "PropertyKindCalculus.Tests.ContractCoverage.Good.fwd"

end Exempt

namespace Weird

/-- A contract at `Nat` nodes: in the population by type, unreadable as a
`Contract String String`. -/
def unreadable : Provenance.Contract Nat Nat where
  name := "coverage probe at Nat nodes"
  members := []
  ports := [⟨0, 0, .output⟩]
  exits := []

end Weird

/-! ## The pinned reports -/

/--
info: relation coverage:
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse ('coverage probe retrieval, unguarded') — edges: PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks ('coverage probe, marks gone stale') — edges: PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleInverts
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse ('coverage probe retrieval, total') — edges: PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverts
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary ('coverage probe forward') — edges: PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts, PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleInverts, PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverts, PropertyKindCalculus.Tests.ContractCoverage.Good.retrievalInvertsForward
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary ('coverage probe retrieval') — edges: PropertyKindCalculus.Tests.ContractCoverage.Good.retrievalInvertsForward
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.dataMove ('coverage probe data movement') — a data-movement boundary: its behavior is the identity on kinds, and there is no measurement model to carry
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.keptCounterexample — counterexample
⚠ UNWITNESSED PropertyKindCalculus.Tests.ContractCoverage.Bare.orphan ('coverage probe orphan')
⚠ UNWITNESSED PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable (?)
9 boundary(ies): 5 witnessed, 2 exempted, 2 UNWITNESSED — relation-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_relation_coverage PropertyKindCalculus.Tests.ContractCoverage

/--
info: mereology coverage:
[classed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.dataMove :: fwd/result : bK — count keyed by pixel
[classed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks :: inv/result : aK — intensive
[classed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse :: inv/result : aK — intensive
[classed] PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary :: fwd/result : bK — intensive
[classed] PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary :: inv/result : aK — whole-proper
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.keptCounterexample — counterexample
⚠ UNDECLARED PropertyKindCalculus.Tests.ContractCoverage.Bare.orphan :: fwd/result : bK
⚠ UNDECLARED PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse :: inv/result : aK
⚠ UNREADABLE PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable — not a `Contract String String`
7 produced port(s): 5 classed, 2 UNDECLARED; 1 boundary(ies) exempted; 1 UNREADABLE — mereology-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_mereology_coverage PropertyKindCalculus.Tests.ContractCoverage

/--
info: inversion coverage:
[guarded] PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks ('coverage probe, marks gone stale') — conditional inv/result; inverted by: PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleInverts
[guarded] PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary ('coverage probe retrieval') — conditional inv/result (decider: PropertyKindCalculus.Tests.ContractCoverage.Good.inDomain); inverted by: PropertyKindCalculus.Tests.ContractCoverage.Good.retrievalInvertsForward
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse ('coverage probe retrieval, total') — total on its input type: every integer is the forward's image of one, so there is no outside to detect; inverted by: PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverts
⚠ UNGUARDED PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse ('coverage probe retrieval, unguarded') — inverted by: PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts
4 inverted boundary(ies): 2 guarded, 1 exempted, 1 UNGUARDED — inversion-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_inversion_coverage PropertyKindCalculus.Tests.ContractCoverage

/-! ## The gates — each fires on the probe world, and cannot be re-blessed -/

/--
error: relation coverage: 2 declared boundary(ies) no theorem edge names — relation-coverage violation
  ⚠ UNWITNESSED PropertyKindCalculus.Tests.ContractCoverage.Bare.orphan ('coverage probe orphan')
  ⚠ UNWITNESSED PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable (?)

A module's behavior is a measurement model carried as a theorem edge, not prose beside the module. Give each boundary at issue a `Provenance.Relation` naming it (left or right) with its witness theorem, or — where its behavior is not a measurement model (pure data movement; the reference an edge is about) — mark its declaration `@[kindRelationFree "reason"]` so the exemption is data the sweep can read. Do NOT re-pin a `#kind_relation_coverage` report whose summary says `violation` — that turns the build green and the census off.
-/
#guard_msgs (whitespace := lax) in
#kind_relation_clean PropertyKindCalculus.Tests.ContractCoverage

/--
error: mereology coverage: 3 produced port(s) with no mereology declaration — mereology-coverage violation
  ⚠ UNDECLARED PropertyKindCalculus.Tests.ContractCoverage.Bare.orphan :: fwd/result : bK
  ⚠ UNDECLARED PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse :: inv/result : aK
  ⚠ UNREADABLE PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable — not a `Contract String String`

A license to shard or recarve is derived from the port's declared aggregation class, not from the fact that a sharded run worked. Add an `aggregations` entry for each port at issue — `.intensive` for a value that must never be summed over a carving, `.wholeProper` for one its parts do not determine, `.extensive` (or a qualified class) where it composes. There is no exemption mark: the vocabulary already names every honest negative. Do NOT re-pin a `#kind_mereology_coverage` report whose summary says `violation` — that turns the build green and the census off.
-/
#guard_msgs (whitespace := lax) in
#kind_mereology_clean PropertyKindCalculus.Tests.ContractCoverage

/--
error: inversion coverage: 1 inverted boundary(ies) with no declared out-of-domain behavior — inversion-coverage violation
  ⚠ UNGUARDED PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse ('coverage probe retrieval, unguarded') — inverted by: PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts

An inversion has a domain, and failure outside it is detected at the interface, not carried in a constructor choice no boundary can see. Give each boundary at issue a `conditional` port for the value it produces only inside the domain, and name the predicate that decides it in `deciders`; or — where the inversion is total on its input type — mark its declaration `@[kindInversionTotal "reason"]` so the exemption is data the sweep can read. Do NOT re-pin a `#kind_inversion_coverage` report whose summary says `violation` — that turns the build green and the census off.
-/
#guard_msgs (whitespace := lax) in
#kind_inversion_clean PropertyKindCalculus.Tests.ContractCoverage

/-! A namespace where everything is declared or exempted: every gate passes silently. The
exemption is the point — it is not a violation and must not fire the gate. -/
namespace Clean

/-- Inverted, guarded, classed, witnessed. -/
def retrieval : Provenance.Contract String String where
  name := "coverage probe clean retrieval"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.inv"]
  ports := [⟨"inv/y", "bK", .input⟩, ⟨"inv/result", "aK", .conditional⟩]
  exits := []
  deciders := [("inv/result", "PropertyKindCalculus.Tests.ContractCoverage.Good.inDomain")]
  aggregations := [("inv/result", .intensive)]

/-- Its edge. -/
def retrievalInverts : Provenance.Relation where
  left := "PropertyKindCalculus.Tests.ContractCoverage.Clean.retrieval"
  right := "PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary"
  kind := .inverts
  witness := "PropertyKindCalculus.Tests.ContractCoverage.Good.inv_fwd"

/-- Edge-free on purpose, its port classed, nothing inverting it. -/
@[kindRelationFree "a reference boundary the edges are about, not a computation"]
def spec : Provenance.Contract String String where
  name := "coverage probe clean spec"
  members := ["PropertyKindCalculus.Tests.ContractCoverage.Good.fwd"]
  ports := [⟨"fwd/x", "aK", .input⟩, ⟨"fwd/result", "bK", .output⟩]
  exits := []
  aggregations := [("fwd/result", .intensive)]

end Clean

-- no message: everything under `Clean` is declared or exempted
#guard_msgs in
#kind_relation_clean PropertyKindCalculus.Tests.ContractCoverage.Clean

-- no message: everything under `Clean` is declared or exempted
#guard_msgs in
#kind_mereology_clean PropertyKindCalculus.Tests.ContractCoverage.Clean

-- no message: everything under `Clean` is declared or exempted
#guard_msgs in
#kind_inversion_clean PropertyKindCalculus.Tests.ContractCoverage.Clean

/-! ## The attributes' own refusals -/

/--
error: `@[kindRelationFree]` expects a 'Provenance.Contract' — 'PropertyKindCalculus.Tests.ContractCoverage.aK' is not one. The mark exempts a declared boundary from a census over declared boundaries, so that is where it goes.
-/
#guard_msgs (whitespace := lax) in
attribute [kindRelationFree "misplaced"] aK

/--
error: `@[kindInversionTotal]` on 'PropertyKindCalculus.Tests.ContractCoverage.Bare.orphan' needs a reason: an exemption without one is the docstring problem in a new place
-/
#guard_msgs (whitespace := lax) in
attribute [kindInversionTotal "  "] Bare.orphan

end PropertyKindCalculus.Tests.ContractCoverage
