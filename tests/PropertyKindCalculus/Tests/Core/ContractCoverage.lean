/-
`Tests.Core.ContractCoverage` — the indexed probe for the five censuses over declared
boundaries (`PropertyKindCalculus.ContractCoverage`): `#kind_relation_coverage` (M12),
`#kind_mereology_coverage` (M15), `#kind_inversion_coverage` (M21's domain half),
`#kind_wellposedness_coverage` (M20 and M21's ambiguity half),
`#kind_diagnostic_coverage` (M22), and their gates.

One probe world, every verdict class of every census exercised, the full reports pinned:

  * a forward and a retrieval, joined by an `inverts` edge — the retrieval guarded by a
    `conditional` port with a named decider, both boundaries' produced ports classed, the
    edge `[well-posed]` by a witness on its declared domain (stated in the expanded
    `∃`-plus-uniqueness form: this tier is Mathlib-free, and the `∃!` spelling with its
    shape check is `#kind_relation`'s business, pinned beside the Water Cloud Model edge);
  * a collapsing forward whose edge declares `ambiguity` and nothing else: `[surfaced]`,
    the honest negative that must not fire the gate — while the three field-free `inverts`
    edges read `⚠ UNDECIDED` and do;
  * two `@[kindDiagnostic]`-marked kinds: one carried by a produced port of the retrieval
    (`[exported]`), one that no boundary exports (`⚠ SIDECHANNELED`);
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

module

public import PropertyKindCalculus.ContractCoverage
meta import PropertyKindCalculus.ContractCoverage

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.ContractCoverage

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)

/-! ## The probe world -/

/-- A probe kind — the forward's argument. -/
def aK : KindOfProperty := { id := "contract coverage probe a", scale := .ratio }
/-- A probe kind — the forward's answer. -/
def bK : KindOfProperty := { id := "contract coverage probe b", scale := .ratio }

/-- A quality kind the retrieval exports: marked diagnostic, and carried by a produced
port of `Good.invBoundary` below. -/
@[kindDiagnostic "whether the retrieval's answer was decided inside its domain"]
def qcK : KindOfProperty := { id := "contract coverage probe quality", scale := .ordinal }

/-- A conditioning kind marked diagnostic that no boundary in scope exports — the side
channel the census is for. -/
@[kindDiagnostic "the fit's conditioning pivot"]
def hiddenK : KindOfProperty :=
  { id := "contract coverage probe conditioning", scale := .ratio }

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

/-- The domain the well-posedness below is declared on — `inDomain`'s `Prop` face. -/
def InDomainP (y : Quantity bK Int) : Prop := y.magnitude > 0

/-- Existence and uniqueness of the inversion's answer on `InDomainP`, in the expanded
form this Mathlib-free tier can state (`∃` plus uniqueness). The census reads the
*declaration*; the `∃!` spelling and its shape check are `#kind_relation`'s business,
pinned beside the Water Cloud Model edge (`UncertaintyExamples`). -/
theorem fwd_well_posed (y : Quantity bK Int) (_ : InDomainP y) :
    ∃ x, fwd x = y ∧ ∀ x', fwd x' = y → x' = x := by
  refine ⟨inv y, ?_, fun x' hx' => (inv_fwd x').symm.trans (congrArg inv hx')⟩
  cases y; simp [fwd, inv]

/-- The forward's boundary: witnessed by the edge below; its output classed. -/
def fwdBoundary : Provenance.Contract NodeId KindRef where
  name := "coverage probe forward"
  members := [``Good.fwd]
  ports := [⟨(NodeId.binder "x").within ``Good.fwd, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``Good.fwd, .decl ``bK, .output⟩]
  exits := []
  aggregations := [(NodeId.result.within ``Good.fwd, .intensive)]

/-- The retrieval's boundary: the left side of the inversion edge, guarded by a conditional
port whose decider is named, its ports classed, its quality flag exported as a port
rather than a side channel. -/
def invBoundary : Provenance.Contract NodeId KindRef where
  name := "coverage probe retrieval"
  members := [``Good.inv]
  ports := [⟨(NodeId.binder "y").within ``Good.inv, .decl ``bK, .input⟩,
            ⟨NodeId.result.within ``Good.inv, .decl ``aK, .conditional⟩,
            ⟨(NodeId.binder "quality").within ``Good.inv, .decl ``qcK, .output⟩]
  exits := []
  deciders := [(NodeId.result.within ``Good.inv, ``Good.inDomain)]
  aggregations := [(NodeId.result.within ``Good.inv, .wholeProper),
                   ((NodeId.binder "quality").within ``Good.inv, .intensive)]

/-- The theorem edge between them — answering for its inversion: the well-posedness
witness on its declared domain. -/
def retrievalInvertsForward : Provenance.Relation where
  left := ``Good.invBoundary
  right := ``Good.fwdBoundary
  kind := .inverts
  witness := ``Good.inv_fwd
  wellPosed := ``Good.fwd_well_posed
  domain := ``Good.InDomainP

end Good

namespace Bare

/-- Inverted, with an `output` port and nothing else declared. -/
def unguardedInverse : Provenance.Contract NodeId KindRef where
  name := "coverage probe retrieval, unguarded"
  members := [``Good.inv]
  ports := [⟨(NodeId.binder "y").within ``Good.inv, .decl ``bK, .input⟩,
            ⟨NodeId.result.within ``Good.inv, .decl ``aK, .output⟩]
  exits := []

/-- The edge that makes it an inverted boundary. -/
def unguardedInverts : Provenance.Relation where
  left := ``Bare.unguardedInverse
  right := ``Good.fwdBoundary
  kind := .inverts
  witness := ``Good.inv_fwd

/-- No edge names it; its output is unclassed; nothing inverts it. -/
def orphan : Provenance.Contract NodeId KindRef where
  name := "coverage probe orphan"
  members := [``Good.fwd]
  ports := [⟨(NodeId.binder "x").within ``Good.fwd, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``Good.fwd, .decl ``bK, .output⟩]
  exits := []

end Bare

namespace Exempt

/-- No edge, on purpose. Its port is classed. -/
@[kindRelationFree "a data-movement boundary: its behavior is the identity on kinds, and \
  there is no measurement model to carry"]
def dataMove : Provenance.Contract NodeId KindRef where
  name := "coverage probe data movement"
  members := [``Good.fwd]
  ports := [⟨(NodeId.binder "x").within ``Good.fwd, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``Good.fwd, .decl ``bK, .output⟩]
  exits := []
  aggregations := [(NodeId.result.within ``Good.fwd, .countKeyed `pixel)]

/-- Inverted, no conditional port, exempted as total. -/
@[kindInversionTotal "total on its input type: every integer is the forward's image of one, \
  so there is no outside to detect"]
def totalInverse : Provenance.Contract NodeId KindRef where
  name := "coverage probe retrieval, total"
  members := [``Good.inv]
  ports := [⟨(NodeId.binder "y").within ``Good.inv, .decl ``bK, .input⟩,
            ⟨NodeId.result.within ``Good.inv, .decl ``aK, .output⟩]
  exits := []
  aggregations := [(NodeId.result.within ``Good.inv, .intensive)]

/-- The edge that makes it an inverted boundary. -/
def totalInverts : Provenance.Relation where
  left := ``Exempt.totalInverse
  right := ``Good.fwdBoundary
  kind := .inverts
  witness := ``Good.inv_fwd

/-- Both marks, stale: an edge now names the boundary and a conditional port guards it, and
both declarations win over the marks. -/
@[kindRelationFree "stale — an edge now names this boundary",
  kindInversionTotal "stale — a conditional port now guards it"]
def staleMarks : Provenance.Contract NodeId KindRef where
  name := "coverage probe, marks gone stale"
  members := [``Good.inv]
  ports := [⟨(NodeId.binder "y").within ``Good.inv, .decl ``bK, .input⟩,
            ⟨NodeId.result.within ``Good.inv, .decl ``aK, .conditional⟩]
  exits := []
  aggregations := [(NodeId.result.within ``Good.inv, .intensive)]

/-- The edge that arrived after the mark. -/
def staleInverts : Provenance.Relation where
  left := ``Exempt.staleMarks
  right := ``Good.fwdBoundary
  kind := .inverts
  witness := ``Good.inv_fwd

/-- A deliberate misdeclaration kept: a subject of nothing, listed as exempted. -/
@[kindCounterexample]
def keptCounterexample : Provenance.Contract NodeId KindRef :=
  { Bare.orphan with name := "coverage probe orphan, kept as a counterexample" }

/-- A deliberately broken edge naming the orphan: it witnesses nothing and enrolls nothing. -/
@[kindCounterexample]
def keptBrokenEdge : Provenance.Relation where
  left := ``Bare.orphan
  right := ``Good.fwdBoundary
  kind := .inverts
  witness := ``Good.fwd

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

namespace Amb

/-- A forward that collapses everything: the inversion with more than one root. -/
def collapse (x : Quantity aK Int) : Quantity bK Int := ⟨x.magnitude * 0⟩

/-- The collision, surfaced as a declaration. The negated-`∃!` spelling and its shape
check are `#kind_relation`'s business, pinned beside the Water Cloud Model edge. -/
theorem collapse_collision : collapse ⟨0⟩ = collapse ⟨1⟩ := by simp [collapse]

/-- The ambiguous retrieval's boundary — guarded and classed, so the domain story is in
order; what fails is uniqueness, and the edge below surfaces it. -/
def foldBoundary : Provenance.Contract NodeId KindRef where
  name := "coverage probe retrieval, ambiguous"
  members := [``Good.inv]
  ports := [⟨(NodeId.binder "y").within ``Good.inv, .decl ``bK, .input⟩,
            ⟨NodeId.result.within ``Good.inv, .decl ``aK, .conditional⟩]
  exits := []
  deciders := [(NodeId.result.within ``Good.inv, ``Good.inDomain)]
  aggregations := [(NodeId.result.within ``Good.inv, .wholeProper)]

/-- The edge surfacing the ambiguity instead of claiming well-posedness. -/
def foldInverts : Provenance.Relation where
  left := ``Amb.foldBoundary
  right := ``Good.fwdBoundary
  kind := .inverts
  witness := ``Good.inv_fwd
  ambiguity := ``Amb.collapse_collision

end Amb

/-! ## The pinned reports -/

/--
info: relation coverage:
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Amb.foldBoundary ('coverage probe retrieval, ambiguous') — edges: PropertyKindCalculus.Tests.ContractCoverage.Amb.foldInverts
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse ('coverage probe retrieval, unguarded') — edges: PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks ('coverage probe, marks gone stale') — edges: PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleInverts
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse ('coverage probe retrieval, total') — edges: PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverts
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary ('coverage probe forward') — edges: PropertyKindCalculus.Tests.ContractCoverage.Amb.foldInverts, PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts, PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleInverts, PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverts, PropertyKindCalculus.Tests.ContractCoverage.Good.retrievalInvertsForward
[witnessed] PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary ('coverage probe retrieval') — edges: PropertyKindCalculus.Tests.ContractCoverage.Good.retrievalInvertsForward
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.dataMove ('coverage probe data movement') — a data-movement boundary: its behavior is the identity on kinds, and there is no measurement model to carry
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.keptCounterexample — counterexample
⚠ UNWITNESSED PropertyKindCalculus.Tests.ContractCoverage.Bare.orphan ('coverage probe orphan')
⚠ UNWITNESSED PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable (?)
10 boundary(ies): 6 witnessed, 2 exempted, 2 UNWITNESSED — relation-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_relation_coverage PropertyKindCalculus.Tests.ContractCoverage

/--

info: mereology coverage:
[classed] PropertyKindCalculus.Tests.ContractCoverage.Amb.foldBoundary :: inv/result : aK — whole-proper
[classed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.dataMove :: fwd/result : bK — count keyed by pixel
[classed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks :: inv/result : aK — intensive
[classed] PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse :: inv/result : aK — intensive
[classed] PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary :: fwd/result : bK — intensive
[classed] PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary :: inv/quality : qcK — intensive
[classed] PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary :: inv/result : aK — whole-proper
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.keptCounterexample — counterexample
⚠ UNDECLARED PropertyKindCalculus.Tests.ContractCoverage.Bare.orphan :: fwd/result : bK
⚠ UNDECLARED PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse :: inv/result : aK
⚠ UNREADABLE PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable — not a `Contract NodeId KindRef`
9 produced port(s): 7 classed, 2 UNDECLARED; 1 boundary(ies) exempted; 1 UNREADABLE — mereology-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_mereology_coverage PropertyKindCalculus.Tests.ContractCoverage

/--
info: inversion coverage:
[guarded] PropertyKindCalculus.Tests.ContractCoverage.Amb.foldBoundary ('coverage probe retrieval, ambiguous') — conditional inv/result (decider: PropertyKindCalculus.Tests.ContractCoverage.Good.inDomain); inverted by: PropertyKindCalculus.Tests.ContractCoverage.Amb.foldInverts
[guarded] PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks ('coverage probe, marks gone stale') — conditional inv/result; inverted by: PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleInverts
[guarded] PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary ('coverage probe retrieval') — conditional inv/result (decider: PropertyKindCalculus.Tests.ContractCoverage.Good.inDomain); inverted by: PropertyKindCalculus.Tests.ContractCoverage.Good.retrievalInvertsForward
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse ('coverage probe retrieval, total') — total on its input type: every integer is the forward's image of one, so there is no outside to detect; inverted by: PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverts
⚠ UNGUARDED PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse ('coverage probe retrieval, unguarded') — inverted by: PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts
5 inverted boundary(ies): 3 guarded, 1 exempted, 1 UNGUARDED — inversion-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_inversion_coverage PropertyKindCalculus.Tests.ContractCoverage

/--
info: well-posedness coverage:
[surfaced] PropertyKindCalculus.Tests.ContractCoverage.Amb.foldInverts — ambiguity: PropertyKindCalculus.Tests.ContractCoverage.Amb.collapse_collision
[well-posed] PropertyKindCalculus.Tests.ContractCoverage.Good.retrievalInvertsForward — PropertyKindCalculus.Tests.ContractCoverage.Good.fwd_well_posed on PropertyKindCalculus.Tests.ContractCoverage.Good.InDomainP
⊘ exempted PropertyKindCalculus.Tests.ContractCoverage.Exempt.keptBrokenEdge — counterexample
⚠ UNDECIDED PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts — 'PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse' inverts 'PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary', no well-posedness witness, no surfaced ambiguity
⚠ UNDECIDED PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleInverts — 'PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks' inverts 'PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary', no well-posedness witness, no surfaced ambiguity
⚠ UNDECIDED PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverts — 'PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse' inverts 'PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary', no well-posedness witness, no surfaced ambiguity
6 inverts edge(s): 1 well-posed, 1 ambiguity surfaced, 1 exempted, 3 UNDECIDED — well-posedness-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_wellposedness_coverage PropertyKindCalculus.Tests.ContractCoverage

/--

info: diagnostic coverage:
[exported] PropertyKindCalculus.Tests.ContractCoverage.qcK — PropertyKindCalculus.Tests.ContractCoverage.Good.invBoundary :: inv/quality
⚠ SIDECHANNELED PropertyKindCalculus.Tests.ContractCoverage.hiddenK (the fit's conditioning pivot) — no produced port in scope carries it
⚠ UNREADABLE PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable — not a `Contract NodeId KindRef`
2 diagnostic kind(s): 1 exported, 1 SIDECHANNELED; 1 UNREADABLE — diagnostic-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_diagnostic_coverage PropertyKindCalculus.Tests.ContractCoverage

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
  ⚠ UNREADABLE PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable — not a `Contract NodeId KindRef`
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

/--
error: well-posedness coverage: 3 inverts edge(s) with neither a well-posedness witness nor a surfaced ambiguity — well-posedness-coverage violation
  ⚠ UNDECIDED PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverts — 'PropertyKindCalculus.Tests.ContractCoverage.Bare.unguardedInverse' inverts 'PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary', no well-posedness witness, no surfaced ambiguity
  ⚠ UNDECIDED PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleInverts — 'PropertyKindCalculus.Tests.ContractCoverage.Exempt.staleMarks' inverts 'PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary', no well-posedness witness, no surfaced ambiguity
  ⚠ UNDECIDED PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverts — 'PropertyKindCalculus.Tests.ContractCoverage.Exempt.totalInverse' inverts 'PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary', no well-posedness witness, no surfaced ambiguity

An inversion either has exactly one answer on a declared domain or it does not, and the edge records which. Give each edge at issue a `wellPosed` witness — a sorry-free theorem concluding with `∃!` — together with the `domain` declaration its statement mentions; or name in `ambiguity` the theorem concluding with the negation of an `∃!` that surfaces the collision, so non-uniqueness is data a consumer can read rather than a root the algorithm happened to reach. There is no exemption mark: either answer is a declaration. Do NOT re-pin a `#kind_wellposedness_coverage` report whose summary says `violation` — that turns the build green and the census off.
-/
#guard_msgs (whitespace := lax) in
#kind_wellposedness_clean PropertyKindCalculus.Tests.ContractCoverage

/--

error: diagnostic coverage: 2 diagnostic kind(s) no declared boundary exports — diagnostic-coverage violation
  ⚠ SIDECHANNELED PropertyKindCalculus.Tests.ContractCoverage.hiddenK (the fit's conditioning pivot) — no produced port in scope carries it
  ⚠ UNREADABLE PropertyKindCalculus.Tests.ContractCoverage.Weird.unreadable — not a `Contract NodeId KindRef`
A quality or conditioning output a consumer must read is part of the declared contract, not a side channel a downstream stage may or may not read. Give some boundary in scope a produced port at each kind at issue — `conditional` where the value exists only in some cases, with its decider named — or, where the kind is not in fact a diagnostic a consumer needs, remove its `@[kindDiagnostic]` mark: enrollment is the mark, so the mark is also the exemption. Do NOT re-pin a `#kind_diagnostic_coverage` report whose summary says `violation` — that turns the build green and the census off.
-/
#guard_msgs (whitespace := lax) in
#kind_diagnostic_clean PropertyKindCalculus.Tests.ContractCoverage

/-! A namespace where everything is declared or exempted: every gate passes silently. The
exemption is the point — it is not a violation and must not fire the gate. -/
namespace Clean

/-- The quality kind the clean retrieval exports. -/
@[kindDiagnostic "whether the clean retrieval's answer was decided inside its domain"]
def qualityK : KindOfProperty :=
  { id := "contract coverage probe clean quality", scale := .ordinal }

/-- Inverted, guarded, classed, witnessed, its diagnostic exported. -/
def retrieval : Provenance.Contract NodeId KindRef where
  name := "coverage probe clean retrieval"
  members := [``Good.inv]
  ports := [⟨(NodeId.binder "y").within ``Good.inv, .decl ``bK, .input⟩,
            ⟨NodeId.result.within ``Good.inv, .decl ``aK, .conditional⟩,
            ⟨(NodeId.binder "quality").within ``Good.inv, .decl ``qualityK, .output⟩]
  exits := []
  deciders := [(NodeId.result.within ``Good.inv, ``Good.inDomain)]
  aggregations := [(NodeId.result.within ``Good.inv, .intensive), ((NodeId.binder "quality").within ``Good.inv, .intensive)]

/-- Its edge, answering for its inversion. -/
def retrievalInverts : Provenance.Relation where
  left := ``Clean.retrieval
  right := ``Good.fwdBoundary
  kind := .inverts
  witness := ``Good.inv_fwd
  wellPosed := ``Good.fwd_well_posed
  domain := ``Good.InDomainP

/-- Edge-free on purpose, its port classed, nothing inverting it. -/
@[kindRelationFree "a reference boundary the edges are about, not a computation"]
def spec : Provenance.Contract NodeId KindRef where
  name := "coverage probe clean spec"
  members := [``Good.fwd]
  ports := [⟨(NodeId.binder "x").within ``Good.fwd, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``Good.fwd, .decl ``bK, .output⟩]
  exits := []
  aggregations := [(NodeId.result.within ``Good.fwd, .intensive)]

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

-- no message: the one inverts edge under `Clean` declares its well-posedness
#guard_msgs in
#kind_wellposedness_clean PropertyKindCalculus.Tests.ContractCoverage.Clean

-- no message: the one diagnostic kind under `Clean` is exported as a port
#guard_msgs in
#kind_diagnostic_clean PropertyKindCalculus.Tests.ContractCoverage.Clean

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

/--
error: `@[kindDiagnostic]` expects a 'KindOfProperty' — 'PropertyKindCalculus.Tests.ContractCoverage.Good.fwdBoundary' is not one. The mark declares a *kind* to be a quality or conditioning output, and the census then asks the boundaries for a port at that kind.
-/
#guard_msgs (whitespace := lax) in
attribute [kindDiagnostic "misplaced"] Good.fwdBoundary

/--
error: `@[kindDiagnostic]` on 'PropertyKindCalculus.Tests.ContractCoverage.aK' needs to say what the kind diagnoses: a diagnostic no one can interpret is the side channel again
-/
#guard_msgs (whitespace := lax) in
attribute [kindDiagnostic "  "] aK

end PropertyKindCalculus.Tests.ContractCoverage

end Blanket
