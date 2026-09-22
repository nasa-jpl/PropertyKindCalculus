/-
# What a port name refers to — the reference vocabulary, held to its scopes

Every command that reads or compares a provenance graph instantiates `Provenance ν κ` and
`Provenance.Contract ν κ` at `NodeId`/`KindRef` (`contractValueOf` demands that
instantiation; any other is invisible to the audits). A reference says which *class* of
thing it names and, for the environment-backed classes, carries the `Lean.Name` the
environment resolves — the vocabulary and its resolution scopes are stated at the types
(`Provenance.lean`, "The reference vocabulary"). This file pins that regime's semantics
in the build, one smallest-possible declaration per rule: any change to how the harvest
mints references, refuses a name, or matches a census answers to every probe below.

Three properties carry the file.

* **Distinct references coexist however alike they render.** A binder named `result` is a
  `NodeRef.binder`, not the structural result; a kind-bearing `let` reusing an input
  binder's name is a `letBound`, not that binder. Both render identically and neither
  collides — the rendering is display, the reference is identity.

* **A name that cannot serve as a reference is refused where the signature or body is the
  fix.** An arrow-form binder with only a hygiene name, two kind-bearing binders or two
  kind binders sharing one name, a second kind-bearing binding at a name the flat body
  namespace already holds — `let`s, do-binds, and matcher binders, across match arms —
  and an erased inline compound the graph cannot name: each is refused with the repair in
  the message, instead of minting a graph whose ill-formedness names no cause or whose
  wiring silently merges two things one name denoted.

* **A census matches by referent, never by rendering.** `#kind_diagnostic_coverage`
  compares a port's `KindRef.decl` against the marked kind's environment name with
  `Name` equality, so two marked kinds sharing a last component are two referents: the
  port carrying one of them exports that one, and the other reads `SIDECHANNELED` — a
  rendering cannot credit a mark it does not name.

The flat body namespace is deliberate: a nesting path is rejected as identity because it
is unstable under hoisting (a semantic no-op would re-address every contract naming the
node), identical for same-depth shadowing, and matcher-generated — hence unwritable —
through match arms. `nestedValue` pins the coexistence that makes the flat reading
sufficient; the refusals pin what uniqueness costs to violate, which is a rename.
-/

module

public import PropertyKindCalculus.ContractCoverage
meta import PropertyKindCalculus.ContractCoverage

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.PortNameScopes
open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)

def aK : KindOfProperty := { id := "port-name-scope probe a", scale := .ratio }

def bK : KindOfProperty := { id := "port-name-scope probe b", scale := .ratio }

/-! ## Signature scope -/

/-- A binder legally named `result` is its own reference: `NodeRef.binder "result"` and
the structural result node render alike and are different nodes, so the wire from one to
the other is an ordinary identity wire and the graph is well formed. -/
def resultShadow (result : Quantity aK Float) : Quantity aK Float := result

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.resultShadow':
input result : aK
output result : aK
aK → aK ⟨result⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph resultShadow

/-- An arrow-form type names no binder, so the port would carry a hygiene name nobody
can write: refused, and naming the binder is the fix. -/
def arrowForm : Quantity aK Float → Quantity aK Float := fun x => x

/--
error: a kind-bearing binder of 'PropertyKindCalculus.Tests.PortNameScopes.arrowForm' has no accessible name — name it, so the port it states is a reference someone can write
-/
#guard_msgs in #kind_ports arrowForm

set_option linter.unusedVariables false in
/-- Two explicit binders with one user name — legal Lean — would mint one reference for
two ports: refused. -/
def shadowedBinders (x : Quantity aK Float) (x : Quantity bK Float) : Quantity bK Float :=
  x

/--
error: two kind-bearing binders of 'PropertyKindCalculus.Tests.PortNameScopes.shadowedBinders' are named 'x' — one reference cannot name both; rename one
-/
#guard_msgs in #kind_graph shadowedBinders

/-- The parametric baseline: a kind generic in the signature is a `KindRef.param`,
rendered as its binder name. -/
def generic {k : KindOfProperty} (q : Quantity k Float) : Quantity k Float := q

/--
info: kind ports of 'PropertyKindCalculus.Tests.PortNameScopes.generic':
input q : k
output result : k
-/
#guard_msgs in #kind_ports generic

set_option linter.unusedVariables false in
/-- Shadowed kind parameters: a `KindRef.param` names its binder, and two kind binders
with one name would make one reference two kinds — refused. -/
def twoParams {k : KindOfProperty} (p : Quantity k Float)
    {k : KindOfProperty} (q : Quantity k Float) : Quantity k Float := q

/--
error: two kind binders of 'PropertyKindCalculus.Tests.PortNameScopes.twoParams' are named 'k' — a kind stated by that name would not say which; rename one
-/
#guard_msgs in #kind_ports twoParams

/-! ## Body scope: exit victims -/

/-- The behaving baseline: the erased value is a signature binder, and the exit carries
its reference. -/
def erasesBinder (x : Quantity aK Float) : Float := x.magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.erasesBinder':
input x : aK
unkinded output result : Float
exit x
well-formed: true
-/
#guard_msgs in #kind_graph erasesBinder

/-- The behaving body case: the erased value is a `let` the author named, and the exit
carries that `letBound` reference. -/
def erasesLet (x : Quantity aK Float) : Float :=
  let m := x + x
  m.magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.erasesLet':
input x : aK
unkinded output result : Float
derived m : aK
aK ± aK → aK ⟨x, x⟩ ⇒ m
exit m
well-formed: true
-/
#guard_msgs in #kind_graph erasesLet

/-- An inline compound has no reference for an exit to name: refused, and let-binding
the erased value is the fix. -/
def erasesInline (x : Quantity aK Float) : Float := (x + x).magnitude

/--
error: a value erased in 'PropertyKindCalculus.Tests.PortNameScopes.erasesInline' is a compound the graph cannot name — let-bind the value you erase, so the exit names a node of the boundary
-/
#guard_msgs in #kind_graph erasesInline

/-! ## Body scope: the flat kind-bearing name namespace -/

/-- The behaving baseline: distinct let names, each node the author's own handle. -/
def seqLets (x : Quantity aK Float) : Float :=
  let m := x + x
  let n := m + m
  n.magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.seqLets':
input x : aK
unkinded output result : Float
derived m : aK
derived n : aK
aK ± aK → aK ⟨x, x⟩ ⇒ m
aK ± aK → aK ⟨m, m⟩ ⇒ n
exit n
well-formed: true
-/
#guard_msgs in #kind_graph seqLets

/-- Sequential shadowing — legal Lean — would merge two bindings' nodes into one
reference and corrupt the wiring: refused, and renaming one is the fix. -/
def shadowLets (x : Quantity aK Float) : Float :=
  let m := x + x
  let m := m + m
  m.magnitude

/--
error: two kind-bearing bindings in 'PropertyKindCalculus.Tests.PortNameScopes.shadowLets' are named 'm' — one flat namespace cannot hold both; rename one
-/
#guard_msgs in #kind_graph shadowLets

/-- A kind-bearing `let` reusing an *input binder's* name is not a collision: the
`letBound` and the `binder` are different references in different scopes, both render
`x`, and the graph is well formed — the class, not the spelling, is the identity. -/
def shadowsBinder (x : Quantity aK Float) : Float :=
  let x := x + x
  x.magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.shadowsBinder':
input x : aK
unkinded output result : Float
derived x : aK
aK ± aK → aK ⟨x, x⟩ ⇒ x
exit x
well-formed: true
-/
#guard_msgs in #kind_graph shadowsBinder

/-- Nesting is not identity: a `let` inside a `let`'s value coexists with it in one flat
namespace because the names are distinct — a nesting path would add nothing here and
would change under hoisting everywhere. -/
def nestedValue (x : Quantity aK Float) : Float :=
  let m := (let inner := x + x; inner + inner)
  m.magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.nestedValue':
input x : aK
unkinded output result : Float
derived inner : aK
derived m : aK
aK ± aK → aK ⟨x, x⟩ ⇒ inner
aK ± aK → aK ⟨inner, inner⟩ ⇒ m
exit m
well-formed: true
-/
#guard_msgs in #kind_graph nestedValue

/-- One `let t` per match arm — the arms share the flat namespace, so the reuse is
refused exactly as sequential shadowing is; naming the arms' values apart is the fix. -/
def matchArms (b : Bool) (x : Quantity aK Float) : Float :=
  match b with
  | true => let t := x + x; t.magnitude
  | false => let t := x - x; t.magnitude

/--
error: two kind-bearing bindings in 'PropertyKindCalculus.Tests.PortNameScopes.matchArms' are named 't' — one flat namespace cannot hold both; rename one
-/
#guard_msgs in #kind_graph matchArms

/-! ## Census matching by referent -/

namespace A
@[kindDiagnostic "the first of two marked kinds sharing a short name"]
def qcK : KindOfProperty := { id := "port-name-scope probe quality A", scale := .ordinal }
end A

namespace B
@[kindDiagnostic "the second of two marked kinds sharing a short name"]
def qcK : KindOfProperty := { id := "port-name-scope probe quality B", scale := .ordinal }
end B

/-- One produced port whose declared kind names `A.qcK` by reference. `B.qcK` renders
identically and is a different referent, so it is not credited. The census reads
declared ports only, so the empty member list is immaterial. -/
def box : Provenance.Contract NodeId KindRef where
  name := "referent probe"
  members := []
  ports := [⟨(NodeId.letBound "flag").within `step, .decl ``A.qcK, .output⟩]
  exits := []

/--
info: diagnostic coverage:
[exported] PropertyKindCalculus.Tests.PortNameScopes.A.qcK — PropertyKindCalculus.Tests.PortNameScopes.box :: step/flag
⚠ SIDECHANNELED PropertyKindCalculus.Tests.PortNameScopes.B.qcK (the second of two marked kinds sharing a short name) — no produced port in scope carries it
2 diagnostic kind(s): 1 exported, 1 SIDECHANNELED — diagnostic-coverage violation
-/
#guard_msgs in #kind_diagnostic_coverage PropertyKindCalculus.Tests.PortNameScopes

end PropertyKindCalculus.Tests.PortNameScopes

end -- pkc-blanket-expose
end -- pkc-blanket
