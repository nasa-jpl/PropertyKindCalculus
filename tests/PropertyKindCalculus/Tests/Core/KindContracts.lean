/-
# Validation probes — the by-type sweeps (`#kind_contracts`, `#kind_contracts_decide`)

`#kind_contract c` checks the boundary an author hands it; these sweeps check the
boundaries nobody handed to anything. Membership is by type — every `Provenance.Contract`
under the given namespaces is a subject — so declaring a boundary is enrolling it, and the
one failure mode the per-name commands leave open (a contract declared and never checked,
indistinguishable from a checked one) is closed. Opting *out* is the explicit act:
`@[kindCounterexample]` marks a deliberate falsification probe, the sweeps list it as an
exempted `⊘` row, and the attribute itself refuses any declaration that is not a
`Provenance.Contract` or `Provenance.Relation`. The probes below pin all of it: the mixed
report (a clean pair, a `✗` violation, a `⊘` exemption, every count in the header), the
empty scope pinning `0` rather than passing invisibly, the kernel-receipt tier and its
idempotence across repeated sweeps, its refusal on a violated scope, the misuse refusal
of the attribute, and `#kind_relations` honoring the same exemption.
-/

module

public import PropertyKindCalculus.KindIncidence
meta import PropertyKindCalculus.KindIncidence
-- Private scope only, and no paired `public import`: core seals `Lean.Name.beq`, so a kernel
-- `decide` over a provenance graph whose kinds are `Name`s gets stuck without this.
import all Init.Prelude
import all PropertyKindCalculus.Provenance

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.KindContracts

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)

/-- A probe kind — the forward's argument. -/
def aK : KindOfProperty := { id := "contract sweep probe a", scale := .ratio }
/-- A probe kind — the forward's answer. -/
def bK : KindOfProperty := { id := "contract sweep probe b", scale := .ratio }

namespace Good

/-- The forward whose boundary is declared correctly. -/
def fwd (x : Quantity aK Int) : Quantity bK Int := ⟨x.magnitude + 1⟩

/-- The retrieval inverting it. -/
def inv (y : Quantity bK Int) : Quantity aK Int := ⟨y.magnitude - 1⟩

/-- The witness: the retrieval recovers what the forward consumed. -/
theorem inv_fwd (x : Quantity aK Int) : inv (fwd x) = x := by
  cases x; simp [inv, fwd]

/-- The forward's declared boundary — a subject the sweep accepts. -/
def fwdBoundary : Provenance.Contract NodeId KindRef where
  name := "sweep probe forward"
  members := [``fwd]
  ports := [⟨(NodeId.binder "x").within ``fwd, .decl ``aK, .input⟩,
            ⟨NodeId.result.within ``fwd, .decl ``bK, .output⟩]
  exits := []

/-- The retrieval's declared boundary. -/
def invBoundary : Provenance.Contract NodeId KindRef where
  name := "sweep probe retrieval"
  members := [``inv]
  ports := [⟨(NodeId.binder "y").within ``inv, .decl ``bK, .input⟩,
            ⟨NodeId.result.within ``inv, .decl ``aK, .output⟩]
  exits := []

/-- The theorem edge between them — the subject `#kind_relations` accepts. -/
def retrievalInvertsForward : Provenance.Relation where
  left := ``invBoundary
  right := ``fwdBoundary
  kind := .inverts
  witness := ``inv_fwd
  claim := "the retrieval recovers the argument the forward consumed"

end Good

namespace Bad

/-- The boundary that forgot the forward's input port. Nobody hands this to a command by
name — being a `Provenance.Contract` in scope is what makes it a subject, and that is
the point of the sweep. -/
def forgottenInput : Provenance.Contract NodeId KindRef where
  name := "sweep probe forward, x forgotten"
  members := [``Good.fwd]
  ports := [⟨NodeId.result.within ``Good.fwd, .decl ``bK, .output⟩]
  exits := []

end Bad

namespace Exempt

/-- The same misdeclaration kept deliberately: the mark is what lets a falsification
probe live in a swept scope without failing its gate. -/
@[kindCounterexample]
def keptCounterexample : Provenance.Contract NodeId KindRef :=
  { Bad.forgottenInput with name := "sweep probe forward, kept as a counterexample" }

/-- A deliberately broken edge (the witness is a definition), exempted the same way. -/
@[kindCounterexample]
def keptBrokenEdge : Provenance.Relation :=
  { Good.retrievalInvertsForward with witness := ``Good.fwd }

end Exempt

/-! ## Declaring a boundary is copying what the machine computed

`#kind_boundary_syntax` prints the assembled scope's surviving boundary as the
constructor syntax a `Provenance.Contract` declares — authored by paste, then owned. -/

/--
info: boundary of this scope, as declarable syntax:
  members := [``PropertyKindCalculus.Tests.KindContracts.Good.fwd]
  ports := [
    ⟨((NodeId.binder "x").within ``PropertyKindCalculus.Tests.KindContracts.Good.fwd), .decl ``PropertyKindCalculus.Tests.KindContracts.aK, .input⟩,
    ⟨(NodeId.result.within ``PropertyKindCalculus.Tests.KindContracts.Good.fwd), .decl ``PropertyKindCalculus.Tests.KindContracts.bK, .output⟩]
  exits := []
-/
#guard_msgs in #kind_boundary_syntax [Good.fwd]

/-! ## The report sweep — checked rows, the `✗` violation, the `⊘` exemption, all counted -/

/--
info: kind contracts — 4 contract(s), 1 violated, 1 exempted
  ✗ PropertyKindCalculus.Tests.KindContracts.Bad.forgottenInput: 'sweep probe forward, x forgotten' — undeclared input fwd/x : aK
  PropertyKindCalculus.Tests.KindContracts.Good.fwdBoundary: 'sweep probe forward' — 2 ports, 0 exits, 1 member step(s)
  PropertyKindCalculus.Tests.KindContracts.Good.invBoundary: 'sweep probe retrieval' — 2 ports, 0 exits, 1 member step(s)
  ⊘ PropertyKindCalculus.Tests.KindContracts.Exempt.keptCounterexample: counterexample, exempted
-/
#guard_msgs in #kind_contracts PropertyKindCalculus.Tests.KindContracts

-- The edge sweep honors the same exemption.
/--
info: kind relations — 2 theorem edge(s), 1 exempted
  PropertyKindCalculus.Tests.KindContracts.Good.retrievalInvertsForward: 'sweep probe retrieval' inverts 'sweep probe forward' — PropertyKindCalculus.Tests.KindContracts.Good.inv_fwd
  ⊘ PropertyKindCalculus.Tests.KindContracts.Exempt.keptBrokenEdge: counterexample, exempted
-/
#guard_msgs in #kind_relations PropertyKindCalculus.Tests.KindContracts

-- A scope with no contracts pins `0` rather than passing invisibly.
/-- info: kind contracts — 0 contract(s) -/
#guard_msgs in #kind_contracts PropertyKindCalculus.Tests.KindContracts.Nowhere

/-! ## The kernel-receipt tier — receipts added, idempotent, and a hard gate -/

/--
info: kind contracts — 2 contract(s) kernel-accepted
  PropertyKindCalculus.Tests.KindContracts.Good.fwdBoundary: kernel-accepted (theorem 'PropertyKindCalculus.Tests.KindContracts.Good.fwdBoundary.kindContractOk')
  PropertyKindCalculus.Tests.KindContracts.Good.invBoundary: kernel-accepted (theorem 'PropertyKindCalculus.Tests.KindContracts.Good.invBoundary.kindContractOk')
-/
#guard_msgs in #kind_contracts_decide PropertyKindCalculus.Tests.KindContracts.Good

-- Sweeping again re-proves nothing: a standing receipt is reported, not re-derived.
/--
info: kind contracts — 2 contract(s) kernel-accepted
  PropertyKindCalculus.Tests.KindContracts.Good.fwdBoundary: theorem 'PropertyKindCalculus.Tests.KindContracts.Good.fwdBoundary.kindContractOk' already stands
  PropertyKindCalculus.Tests.KindContracts.Good.invBoundary: theorem 'PropertyKindCalculus.Tests.KindContracts.Good.invBoundary.kindContractOk' already stands
-/
#guard_msgs in #kind_contracts_decide PropertyKindCalculus.Tests.KindContracts.Good

-- On a violated scope the deciding sweep throws — no reading of it states a violation.
/--
error: the boundary declared by 'PropertyKindCalculus.Tests.KindContracts.Bad.forgottenInput' is not the one its members compute:
contract 'sweep probe forward, x forgotten': 1 ports, 0 exits
undeclared input fwd/x : aK
boundary agrees: false
-/
#guard_msgs in #kind_contracts_decide PropertyKindCalculus.Tests.KindContracts.Bad

/-! ## The attribute's own gate — only the two swept types may be exempted -/

/--
error: `@[kindCounterexample]` expects a 'Provenance.Contract' or a 'Provenance.Relation' — 'PropertyKindCalculus.Tests.KindContracts.stray' is neither. The mark exempts a declaration from the by-type provenance sweeps, and only those two types are swept.
-/
#guard_msgs in @[kindCounterexample] def stray : Nat := 0

end PropertyKindCalculus.Tests.KindContracts

end Blanket
