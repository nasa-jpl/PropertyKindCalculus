/-
# What a port name refers to — the resolution scopes of the `String String` vocabulary

Every command that reads or compares a provenance graph instantiates `Provenance ν κ` and
`Provenance.Contract ν κ` at `String String` (`contractValueOf` demands that instantiation;
any other is invisible to the audits). This file states what those strings *denote* — the
scope each class of name resolves in — and pins, one smallest-possible declaration per
failure, the places where the flattening loses the referent. The pins hold the naming
regime's actual semantics in the build: any change to how the harvest mints names, or to
how the audits compare them, answers to every probe below.

## The node grammar (`ν`)

A node identifier is minted by the harvest, never chosen freely. Its grammar, with the
minting site for each production:

```
node  ::= level "/" local          (assembled; bare `local` in a single-step graph)
level ::= shortMemberName ["#" n]  (`stepNameOf`: the declaration's last component —
                                    an address, deliberately not the pretty printer —
                                    with "#n" numbering the instances when one member
                                    is called more than once; last-component collisions
                                    between members are refused at assembly)
local ::= binderName path          (an explicit binder — `stepGraphOf` telescopes the
                                    declaration's *type*, never the value's lambdas)
        | "result" ["." i] path    (the result, or component i of a product result)
        | fullConstantName path    (a configuration constant the body reads — the full
                                    environment name, so identity is reader-independent)
        | letName                  (a kind-bearing `let` of the body — the bare user
                                    name, at any nesting depth)
        | "_" n                    (`WalkSt.nextFresh`: a synthesized interior node,
                                    numbered in traversal order — graph-internal)
path  ::= ("." fieldName)*         (carrier field paths through container structures)
```

## The kind grammar (`κ`)

```
kind ::= prettyPrintedConstant     (`renderKindArg`: `Meta.ppExpr`, relative to the
                                    elaborating context's namespace and `open`s)
       | binderName                (a parametric kind — the type-telescope binder name)
       | kind (" → " kind)+       (`signatureKind?`: a module-valued port)
       | kind (", " kind)+        (a multi-kind carrier)
```

## The scope table

Where each name class resolves — the rule every reader of these strings depends on:

| name class      | resolves in                                                       |
|-----------------|-------------------------------------------------------------------|
| binder node     | the member's signature telescope, explicit binders                |
| parametric kind | the member's signature telescope, kind-typed binders              |
| let node        | the body's kind-bearing `let`s — one flat namespace, no path      |
| result node     | structural: the result position, or a product-component index     |
| config node     | the environment, by full constant name                            |
| level           | the environment, by last component                                |

Two asymmetries follow from the flattening. First, the string does not say which class it
is in, so no reader can check that a name resolves in its scope — a config node's full
constant name is indistinguishable from a binder plus a long field path, and a kind that is
a binder name is indistinguishable from a kind that is a constant. Second, of the
`Contract` fields that reference declarations, the port *kind* is the only one never
resolved against the environment: `deciders`, `aggregations`, `suppliers`, and the relation
clauses all pass through `env.find?`, while a kind meets only another string —
byte-for-byte in `Contract.standsFor` (which is why `#kind_contracts` replays each contract
under its defining module's namespace), and by the `endsWith "." ++ ·` suffix tolerance
in every census that must bridge a short-rendered port kind to a full environment name.

## The probes

Grouped by scope. Each is the smallest declaration exhibiting one loss, with the
misbehavior pinned exactly as the commands report it.

* **Signature scope.** `resultShadow` — a binder legally named `result` collides with the
  reserved result node: two ports, one identity, and the graph is ill-formed with no cause
  named. `arrowForm` — an arrow-form type has no source binder name, so the port's
  identity is the toolchain's internal hygiene name: unaddressable by any author.
  `shadowedBinders` — Lean permits two explicit binders with one user name; both ports
  read `x`, and the graph is ill-formed with no cause named. `generic` and `twoParams` —
  a parametric kind renders as its binder name; under shadowing the earlier parameter
  renders with a hygiene dagger (`k✝`), a spelling no declared contract can write.

* **Body scope: exits.** An exit names the node whose value leaves the calculus at a
  carrier projection, and the victim is named by the body walk (`refName` over the walk's
  binder context). `erasesBinder` and `erasesLet` behave: the victim is a signature binder
  or a `let` the author named. `erasesInline` — a projection applied to an inline compound
  records the *instance function's* name (`instHAdd.hAdd`) as the exit: a garbage
  identity that is not a node of the graph, while the value itself sits on a synthesized
  `_1`. `erasesTwoInline` — exits deduplicate by name, so two distinct inline erasures
  collapse onto one nonexistent node.

* **Body scope: the let namespace is flat, and nesting is not identity.** `walk`'s
  `.letE` case names the node by bare user name at any depth; the binder context resolves
  *references* and contributes nothing to identity. `nestedValue` pins that this is
  correct for distinct names: `inner` and `m` coexist however deeply nested, so a nesting
  path adds nothing where names are unique. The failures are all *reuse*: `shadowLets` —
  sequential shadowing corrupts the wiring itself (`⟨m, m⟩ ⇒ m` merges the second
  binding's operands with its result); `matchArms` — one `let t` per match arm collapses
  the two arms' values onto one node and their two exits onto one. A nesting path would
  repair neither: a path changes under hoisting (a semantic no-op would re-address every
  contract naming the exit), is identical for same-depth shadowing, and is
  matcher-generated — hence unwritable — through match arms. What a faithful flat reading
  requires is name *uniqueness* among the body's kind-bearing `let`s; these pins exhibit
  what its absence costs.

* **Census matching.** `#kind_diagnostic_coverage` matches a mark's full environment name
  against a port's short-rendered kind by suffix, so two marked kinds sharing a short name
  both read `[exported]` from a single port — one port discharges two distinct
  diagnostics, and the gate reads clean.
-/
import PropertyKindCalculus.ContractCoverage

namespace PropertyKindCalculus.Tests.PortNameScopes
open PropertyKindCalculus

def aK : KindOfProperty := { id := "port-name-scope probe a", scale := .ratio }

def bK : KindOfProperty := { id := "port-name-scope probe b", scale := .ratio }

/-! ## Signature scope -/

/-- A binder legally named `result` takes the reserved result node's identity: one name,
two interface positions, and the ill-formedness names no cause. -/
def resultShadow (result : Quantity aK Float) : Quantity aK Float := result

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.resultShadow':
input result : aK
output result : aK
aK → aK ⟨result⟩ ⇒ result
well-formed: false
-/
#guard_msgs in #kind_graph resultShadow

/-- An arrow-form type names no binder, so the port's identity is the internal hygiene
name the elaborator minted for the arrow's domain — unaddressable by any author, and
owned by the toolchain rather than the source. -/
def arrowForm : Quantity aK Float → Quantity aK Float := fun x => x

/--
info: kind ports of 'PropertyKindCalculus.Tests.PortNameScopes.arrowForm':
input a._@._internal._hyg.0 : aK
output result : aK
-/
#guard_msgs in #kind_ports arrowForm

set_option linter.unusedVariables false in
/-- Two explicit binders with one user name — legal Lean — mint two ports with one
identity. -/
def shadowedBinders (x : Quantity aK Float) (x : Quantity bK Float) : Quantity bK Float :=
  x

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.shadowedBinders':
input x : aK
input x : bK
output result : bK
bK → bK ⟨x⟩ ⇒ result
well-formed: false
-/
#guard_msgs in #kind_graph shadowedBinders

/-- The parametric baseline: a kind generic in the signature renders as its type-telescope
binder name. -/
def generic {k : KindOfProperty} (q : Quantity k Float) : Quantity k Float := q

/--
info: kind ports of 'PropertyKindCalculus.Tests.PortNameScopes.generic':
input q : k
output result : k
-/
#guard_msgs in #kind_ports generic

set_option linter.unusedVariables false in
/-- Shadowed kind parameters: the earlier one renders with a hygiene dagger — a kind no
declared contract can spell. -/
def twoParams {k : KindOfProperty} (p : Quantity k Float)
    {k : KindOfProperty} (q : Quantity k Float) : Quantity k Float := q

/--
info: kind ports of 'PropertyKindCalculus.Tests.PortNameScopes.twoParams':
input p : k✝
input q : k
output result : k
-/
#guard_msgs in #kind_ports twoParams

/-! ## Body scope: exit victims -/

/-- The behaving baseline: the erased value is a signature binder, and the exit carries
its name. -/
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
carries that name. -/
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

/-- An inline compound has no name, so the exit records the arithmetic *instance
function* — a garbage identity that is not a node of the graph — while the value itself
sits on the synthesized `_1`. -/
def erasesInline (x : Quantity aK Float) : Float := (x + x).magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.erasesInline':
input x : aK
unkinded output result : Float
derived _1 : aK
aK ± aK → aK ⟨x, x⟩ ⇒ _1
exit instHAdd.hAdd
well-formed: false
-/
#guard_msgs in #kind_graph erasesInline

/-- Exits deduplicate by name, so two distinct inline erasures collapse onto one
nonexistent node. -/
def erasesTwoInline (x : Quantity aK Float) (y : Quantity aK Float) : Float :=
  (x + x).magnitude + (y + y).magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.erasesTwoInline':
input x : aK
input y : aK
unkinded output result : Float
derived _1 : aK
derived _2 : aK
aK ± aK → aK ⟨x, x⟩ ⇒ _1
aK ± aK → aK ⟨y, y⟩ ⇒ _2
exit instHAdd.hAdd
well-formed: false
-/
#guard_msgs in #kind_graph erasesTwoInline

/-! ## Body scope: the flat let namespace -/

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

/-- Sequential shadowing — legal Lean — corrupts the wiring itself: the second binding's
operands merge with its result into `⟨m, m⟩ ⇒ m`. -/
def shadowLets (x : Quantity aK Float) : Float :=
  let m := x + x
  let m := m + m
  m.magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.shadowLets':
input x : aK
unkinded output result : Float
derived m : aK
derived m : aK
aK ± aK → aK ⟨x, x⟩ ⇒ m
aK ± aK → aK ⟨m, m⟩ ⇒ m
exit m
well-formed: false
-/
#guard_msgs in #kind_graph shadowLets

/-- Nesting is not identity: a `let` inside a `let`'s value coexists with it in one flat
namespace, correctly, because the names are distinct — a nesting path would add nothing
here and would change under hoisting everywhere. -/
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

/-- One `let t` per match arm — idiomatic Lean — collapses the two arms' values onto one
node and their two erasures onto one exit. -/
def matchArms (b : Bool) (x : Quantity aK Float) : Float :=
  match b with
  | true => let t := x + x; t.magnitude
  | false => let t := x - x; t.magnitude

/--
info: kind graph of 'PropertyKindCalculus.Tests.PortNameScopes.matchArms':
input x : aK
unkinded input b : Bool
unkinded output result : Float
derived t : aK
derived t : aK
aK ± aK → aK ⟨x, x⟩ ⇒ t
aK ± aK → aK ⟨x, x⟩ ⇒ t
exit t
well-formed: false
-/
#guard_msgs in #kind_graph matchArms

/-! ## Census matching by suffix -/

namespace A
@[kindDiagnostic "the first of two marked kinds sharing a short name"]
def qcK : KindOfProperty := { id := "port-name-scope probe quality A", scale := .ordinal }
end A

namespace B
@[kindDiagnostic "the second of two marked kinds sharing a short name"]
def qcK : KindOfProperty := { id := "port-name-scope probe quality B", scale := .ordinal }
end B

/-- One produced port whose declared kind is the bare short name both marks share. The
census reads declared ports only, so the empty member list is immaterial. -/
def box : Provenance.Contract String String where
  name := "suffix probe"
  members := []
  ports := [⟨"step/flag", "qcK", .output⟩]
  exits := []

/--
info: diagnostic coverage:
[exported] PropertyKindCalculus.Tests.PortNameScopes.A.qcK — PropertyKindCalculus.Tests.PortNameScopes.box :: step/flag
[exported] PropertyKindCalculus.Tests.PortNameScopes.B.qcK — PropertyKindCalculus.Tests.PortNameScopes.box :: step/flag
2 diagnostic kind(s): 2 exported — clean
-/
#guard_msgs in #kind_diagnostic_coverage PropertyKindCalculus.Tests.PortNameScopes

end PropertyKindCalculus.Tests.PortNameScopes
