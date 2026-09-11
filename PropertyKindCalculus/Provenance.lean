/-
# Provenance — the metrological provenance hypergraph as data

The calculus's audit surfaces each report one relation of a single underlying object.
`#kind_boundary_audit` reports where values acquire kinds, with the evidence tier that
sanctions each site (`BoundaryAudit`); `#kind_edges` enumerates the authored kind-algebra
edges, each occurrence attributed to its use site (`KindEdges`); and a model's coverage
probe pins the closure its pipeline exercises. This module defines the object those
relations constitute — the **metrological provenance hypergraph**, the formal counterpart
of Dybkær's dissection of a complete property statement into system, component,
kind-of-property, procedure, and result. Its nodes are kinded values; its hyperedges are
witness-family occurrences — a `ProductKind k₁ k₂ k` occurrence relates two operands and
a result, hence *hyper*graph, and relates them in *order*: a quotient's numerator and
denominator are different ports of the edge, and the same node may occur twice
(`kx / kx`), so incidence is an ordered list, never a set. Sources carry the boundary
audit's evidence tiers; exits mark the erasure boundary, where kinded provenance hands
off to the bare carrier and the byte gate, not the type system, carries the claim onward.

The structure is *data* — prelude-only, carrier- and application-generic, parametric in
the node-identifier type `ν` and the kind type `κ` — so a graph can be authored by hand
in a probe, constructed by an elaborator harvest, or replayed from a report. Its fields
are lists and its checker is structural recursion over them, so well-formedness is
decided by *evaluation* in a probe (`#guard`) and by *kernel reduction* in a proof
(`decide`) — the kernel checks the wiring — and the applications' theorems get list
induction as their proof skeleton. A harvest that needs per-node attribution puts it
*inside* its choice of `ν` (a node id may be a declaration–binder pair); the occurrence's
use site is a field because use-site attribution is constitutive of the occurrence
relation itself — two uses of one witness are two occurrences, wherever the elaborator
lifted or shared the proof term.

## Well-formedness is structural; edges stay authored claims

`wellFormed` checks the wiring: every node declared exactly once; every occurrence typed
(operands and result carry the kinds their node declarations state, at the family's
operand count); results land only on derivation targets — a `derived` node or a port the
step produces, never on a source, whose whole point is that it is *not* derived; and every derived
node, output port, and exit is reached from the sources (input and configuration ports,
gated ingests, attested mints) through the occurrences — reached through the *closure*,
so a cycle of occurrences feeding each other licenses nothing. That last condition is the
boundary audit's "raw mints = 0" made compositional: a node that is neither a source nor
reachable through authored occurrences is exactly an anonymous mint, and the predicate
refuses the graph that contains one.

## What well-formedness does not claim — the graph's scope

`wellFormed` judges the wiring of the graph it is given, and it is **monotone under
disjoint union**: unique-declaration survives on node-disjoint operands, typing and
results-are-derivations are per-occurrence, and the closure of a union contains each
part's closure. Two well-formed graphs sharing no node therefore union to a well-formed
graph however unrelated they are, and a harvest that assembles a *set* of declarations
gets no verdict on the set — adding a member belonging to no pipeline leaves the verdict
`true`, and the assembled ports are a by-product of the membership choice rather than a
claim that choice can be checked against. Scope is a **boundary** property, not a wiring
property: a member set is justified exactly when the boundary it computes is the boundary
someone declared. `reachableFrom` is the query that states connectivity — it is asked of a
chosen start set and never assumed of the whole — and the probes carry the witness, an
unrelated pair whose union passes while neither part reaches the other.

## The declared boundary — `Contract`

`Contract` is that declaration: a name, the members it is claimed for, the ports the
author claims those members expose with the role each plays, and the exits.
`Contract.agrees` compares it with the computed boundary in both directions — nothing
computed left undeclared, nothing declared left unexhibited — and the two difference
lists are the report, because a boundary that cannot disagree checks nothing. This is the
judgment `wellFormed` structurally cannot make, and it closes scope without a scope
checker: add a member and the inputs nothing feeds surface as `undeclared` ports, drop
one and its caller's operand stops wiring, so the port that covered it turns up
`unrealized`. What the contract does *not* re-adjudicate is the wiring itself:
`wellFormed` and `agrees` are two verdicts on one object, the first that the graph holds
together and the second that it is the graph someone meant.

The members belong *in* the declaration, because the sentence being checked is about
them: a member set is justified exactly when the boundary it computes is the boundary
declared for it. Carrying the two apart would leave the scope a per-call-site choice
again — the contract would be checked against whichever members the caller happened to
name — so every consumer, the probe and the figure alike, reads the scope off the one
declaration that answers for it.

Roles carry **binding time**, which is why there are several. A `config` is a constant *this
tier binds* — a cited coefficient, a threshold — harvested from the declaration that binds
it. A `param` is a source this tier does **not** bind: an algorithm states its table extent
and its incidence angle as parameters, and the application below it binds them to
configuration constants of its own. A signature harvest cannot read binding time — it sees
an argument, not when the argument is filled — so `param` is a claim the contract makes
about a computed `input`, and `PortDir.refines` is exactly that one refinement. The tiers
are then contracts over the same vocabulary: an algorithm's parameters unbound, an
application's bound, a deployment's inputs and outputs bound to artifacts.

`conditional` is the one role that answers a different question — not when the value is
bound but whether it is produced at all. An algorithm with a validity domain returns a
quantity in some cases and nothing in others, and the case is the interface's business:
declaring the port conditional is how the domain gets stated where a consumer reads it,
instead of being carried in a constructor choice no boundary can see. A contract may not
trade the two: claiming an unconditional output where the result has cases, or the
reverse, disagrees in both directions, because whether an interface always produces a
value is the plainest thing it has to say. The role records that cases exist; the
contract's `deciders` field may additionally name, per conditional port, the declaration
that decides them — the predicate becomes data of the boundary, checked to exist and to
govern a conditional port, rather than prose beside it.

A produced port may additionally declare its **aggregation class** (`aggregations`):
what distributing the computation over a carving of a batch axis — tiles, blocks,
shards — does to the value, in the §13.5 vocabulary the mereology layer proves laws
over (`AggregationClass` below). Every distribution decision rests on an extensivity
claim; the clause is where that claim is declared so the license to shard can be
derived from it (`Recarving.distribution_license`) instead of assumed. Like an
`Assembles` entry, the class is the author's curated claim — the checks are hygiene
(a class governs a produced port; each name the class carries exists, and a
tolerance is a kinded quantity), and the mereology layer's theorems are what the
claim buys or costs.

A **functional argument ports at its kind signature** — a *module-valued port*. A
kind-typed arrow (`Quantity k₁ α → … → Quantity k α`, however an abbreviation spells
it) is already an anonymous contract — input kinds, an output kind — so the harvest
reads the binder as a port whose kind is that signature, rendered with `→` between
the components. This is the one port class whose payload is a contract rather than a
kind, and it is what closes the paradigm under abstraction: modules may be parameters
of modules. The contract's `suppliers` field then declares the binding — for a
signature port this tier answers, the *name* of the module bound to it — checked
against the supplier's own declared type, so which module a deployment bound is
interface data rather than a call-site habit, and two suppliers of one signature can
be related by a `Relation` edge instead of folklore.

`Contract.discharges` is that ladder, and it is a relation between two *declarations*
rather than between a declaration and a graph — no harvest, so a deployment can state
what it did with an algorithm's parameters with the algorithm's contract merely imported.
It asks three things: that the deploying contract contains every member of the deployed
one, that every inherited parameter is either bound within the wider scope or restated as
a parameter of it, and that no exit is lost on the way up. The middle one is the content:
binding a parameter is an act — a constant declared, a wire run — and relabelling it
per-datum data is not that act, so a parameter is not discharged by being forgotten.

Neither relation can say that one boundary *inverts* another, that two agree wherever a
hypothesis holds, or that one departs from another by no more than a stated quantity.
Those are theorems, not port lists, and `Relation` is the edge that carries one: the two
boundaries, what is claimed of them, and the name of the proof. Nothing about it is
decidable — the witness already is a kernel-checked proposition — so what `#kind_relation`
checks is everything around the proof, including the one thing that keeps the edge from
being decoration: that the statement mentions members of both boundaries.

What well-formedness deliberately does not check is the *truth* of any edge. Per the
trust model (`QuantityClassification`, "The trust model — witnesses are authored, not
checked"), whether `k` really is the product kind of `k₁` and `k₂` is the author's
metrological claim, judged by enumerating the authored witnesses; the graph records which
claims were used where, and inherits its soundness story from that enumeration rather
than re-adjudicating it.

## The identity wire — `copy`

One edge family is not a witness family: `copy`, the identity wire. It exists because an
interface can restate a node the wiring already has — a pass-through step's output *is*
its input, and a multi-output step's components are the interior nodes its body names —
and the graph still owes an occurrence that reaches the output port, or the port is
indistinguishable from an anonymous mint. A `copy` relates one operand to its result and
claims nothing metrological: the value is the same value under a second name. Because
that claim is structural rather than authored, it is the one family whose semantic
content `wellFormed` itself checks — a copy must preserve the kind — where every witness
family's equation remains the authored claim the trust model reviews by enumeration.
Enumeration surfaces list authored licenses, so they never show a `copy`; it belongs to
the wiring, and to the graph renderings of it.

## The procedure edge — `step`, and assembly

A multi-step pipeline is itself one graph, and at the assembly level a whole step is a
hyperedge: `step name arity` relates a step's kinded inputs to one of its outputs — the
formal counterpart of Dybkær's *procedure* element. Its equation is licensed not by a
witness family but by the step itself: by the step's own well-formed graph where its
body exhibits the wiring, and by the boundary audit's per-declaration accountability
where the interior is opaque to the walk. Like every family except `copy`, the
procedure edge's equation is a recorded claim, not something `wellFormed`
re-adjudicates; a step edge is wiring vocabulary for assemblies, so enumeration
surfaces exclude it the way they exclude `copy`. `mapNodes` and `union` are the
assembly combinators: level graphs are renamed into disjoint node spaces and unioned,
call sites wire caller operands to callee ports by `copy`, and well-formedness is then
checked *on the assembled object* — no preservation theorem is owed, because the
doctrine is to decide the object, never to trust the construction.
-/

namespace PropertyKindCalculus

/-- The role a port plays in a step's interface, and with it the time the port's value is
bound: an `input` the step consumes, varying per datum; a `config` it reads — a declared
constant mint this tier binds, a cited coefficient table, a bound, a threshold; a `param`
this tier leaves for the tier below to bind, fixed for a deployment but not here; an
`output` it produces; or a `conditional` output it produces *in some cases of its result
and not others*, which is how an algorithm with a validity domain states that domain at
its interface instead of burying it in a constructor choice. The two output roles are
derivation targets; every other role is a source of the graph. -/
inductive Provenance.PortDir where
  | input
  | config
  | param
  | output
  | conditional
deriving DecidableEq, Repr, Inhabited

/-- Is this role a derivation target — an output, conditional or not? -/
def Provenance.PortDir.produced : Provenance.PortDir → Bool
  | .output | .conditional => true
  | _ => false

/-- How a port role prints in a rendered report: `input` / `config` / `param` /
`output` / `conditional`. -/
def Provenance.PortDir.label : Provenance.PortDir → String
  | .input => "input"
  | .config => "config"
  | .param => "param"
  | .output => "output"
  | .conditional => "conditional"

/-- Does a *declared* role stand for a *computed* one? Every role stands for itself, and
`param` additionally stands for a computed `input`: a signature harvest sees an argument,
never the tier that fills it, so binding time is a claim the contract makes and not a fact
the walk can read. Nothing else refines — a `config` is harvested from the declaration
that binds it, so claiming one where the walk found none is a disagreement, not a
refinement. -/
def Provenance.PortDir.refines : Provenance.PortDir → Provenance.PortDir → Bool
  | .param, .input => true
  | a, b => a == b

/-- The evidence tier of a node-introduction event — the boundary audit's tiers, carried
into the graph. `derived` is the interior case: the kind is reached through an authored
occurrence, and well-formedness demands the occurrence exist. `gated` is a source with
runtime evidence: a checked ingest admitted the value, and the gate declaration is the
evidence. `attested` is a declared source with no machine-checkable evidence: the
harvested reason string is the node's label, carried so every report rendered from the
graph shows the one-line justification at the node that rests on it. -/
inductive Provenance.IntroTier where
  | derived
  | gated
  | attested (reason : String)
deriving DecidableEq, Repr, Inhabited

/-- Is this tier a source of the graph — a node known before any occurrence fires? -/
def Provenance.IntroTier.isSource : Provenance.IntroTier → Bool
  | .derived => false
  | .gated => true
  | .attested _ => true

/-- How an introduction tier prints in a rendered report: `derived` / `gated` /
`attested "reason"` — the attested case shows its one-line justification, per the
header's doctrine that every rendering carries it at the node that rests on it. -/
def Provenance.IntroTier.label : Provenance.IntroTier → String
  | .derived => "derived"
  | .gated => "gated"
  | .attested r => s!"attested \"{r}\""

/-- The last component of a declaration name — the rendering grammar's short form for
members and kind declarations. Purely a display form: identity is the full name. -/
def Provenance.lastComponent : Lean.Name → String
  | .str _ s => s
  | n => toString n

/-- The hyperedge labels: the witness families of the core calculus — `ProductKind`,
`QuotientKind`, `ReciprocalKind`, `TranscendentalKind`, `PowerKind` (carrying its
rational exponent — an exponent is data of the edge, not an operand node),
`ReferenceKind` (the re-expression, whose two reference quantities are configuration of
the edge rather than operands of it — the value converted is the one operand),
`DifferenceKind` (the same-kind sum or difference; one family for both, because one
witness licenses both and the shared kind index is the whole of its claim), and the
operator-table registrations `KindMul`/`KindDiv` — plus `copy`, the identity wire
(header, "The identity wire"): harvested wiring, never an authored license — and
`step`, the procedure edge (header, "The procedure edge"): a whole step applied as a
hyperedge at the assembly level, carrying the step's rendered name and its operand
count, its equation licensed by the step's own graph and audit tier rather than by a
witness — and `select`, the **nominal selection**: a designation of a nominal kind
choosing among alternatives that all carry the result's kind. Its first operand is the
selector, at its own nominal kind; the rest are the branches, each at the result kind,
so the edge states that the choice is *between* values of one kind and that the label is
what makes it. A selection licenses no kind equation — every branch already carries the
kind the result does — which is exactly its content: the only thing a nominal value may
do is be compared for equality, and a `match` is that comparison. -/
inductive Provenance.EdgeFamily where
  | product
  | quotient
  | reciprocal
  | transcendental
  | power (exp : Rat)
  | reference
  | additive
  | tableMul
  | tableDiv
  | copy
  | step (member : Lean.Name) (inst? : Option Nat) (arity : Nat)
  | select (cases : Nat)
deriving DecidableEq, Repr, Inhabited

/-- The number of operand nodes an occurrence of this family relates (its result is not
counted; a `power` edge's exponent is carried by the label, not an operand). A `step`
edge's count is the step's kinded input count, carried by the label — a procedure
relates however many inputs its interface states. -/
def Provenance.EdgeFamily.operandCount : Provenance.EdgeFamily → Nat
  | .product | .quotient | .tableMul | .tableDiv | .additive => 2
  | .reciprocal | .transcendental | .power _ | .reference | .copy => 1
  | .step _ _ a => a
  | .select n => n + 1

/-- Render a `power` exponent in the enumeration commands' grammar: the spelling the
pretty printer gives the authored literal — `1 / 2`, `-1`, `3` — so an edge renders one
way whether it was read off a witness type or carried as edge data. -/
def Provenance.EdgeFamily.renderExp (p : Rat) : String :=
  if p.den == 1 then toString p.num else s!"{p.num} / {p.den}"

/-- Render an edge in the kind-equation grammar the enumeration commands print
(`a · b → c`, `a / b → c`, `1 / a → b`, `transcendental : a → b`, `a ^ p → b`,
`[table] …`; a `copy` is `a → b`; a `step` is `[step name] a · b → c`, its inputs
joined however many the interface states), from already-rendered operand and result
names. -/
def Provenance.EdgeFamily.render (f : Provenance.EdgeFamily)
    (operands : List String) (result : String) : String :=
  let o (i : Nat) : String := operands.getD i "_"
  match f with
  | .product => s!"{o 0} · {o 1} → {result}"
  | .quotient => s!"{o 0} / {o 1} → {result}"
  | .reciprocal => s!"1 / {o 0} → {result}"
  | .transcendental => s!"transcendental : {o 0} → {result}"
  | .power p => s!"{o 0} ^ {Provenance.EdgeFamily.renderExp p} → {result}"
  | .reference => s!"reference : {o 0} → {result}"
  | .additive => s!"{o 0} ± {o 1} → {result}"
  | .tableMul => s!"[table] {o 0} · {o 1} → {result}"
  | .tableDiv => s!"[table] {o 0} / {o 1} → {result}"
  | .copy => s!"{o 0} → {result}"
  | .step m i _ =>
    let nm := match i with
      | some k => if k == 1 then Provenance.lastComponent m
                  else s!"{Provenance.lastComponent m}#{k}"
      | none => Provenance.lastComponent m
    if operands.isEmpty then s!"[step {nm}] → {result}"
    else s!"[step {nm}] {String.intercalate " · " operands} → {result}"
  | .select _ =>
    match operands with
    | [] => s!"select → {result}"
    | sel :: branches =>
      s!"select {sel} : {String.intercalate " | " branches} → {result}"

/-! ## The reference vocabulary — what a node identifier and a kind identifier denote

A `Provenance` value's two type parameters are its identity vocabulary, and the harvest
instantiates them with the two types below. Each constructor names the *class* of thing a
reference denotes and, for the environment-backed classes, carries the `Lean.Name` the
environment resolves — so two references are equal exactly when they denote the same thing,
never because two different things render alike, and a rendering is something a reference
*has*, not something it *is*.

Resolution scopes: a `NodeRef.binder` and a `KindRef.param` resolve in the member's
signature telescope; a `NodeRef.letBound` in the member body's kind-bearing names — `let`
binders and single-alternative matcher binders, one flat namespace with no nesting path,
because a path is unstable under hoisting, identical for same-depth shadowing, and
matcher-generated through match arms. A `NodeRef.const` and a `KindRef.decl` resolve in the
environment; a `NodeRef.result` is structural. The harvest refuses a member whose
kind-bearing names are inaccessible or ambiguous in their scope, so every reference that
reaches a graph names its referent uniquely; a contract mentioning a `fresh` or
`unresolved` node, or a `rendered` kind, is refused — those classes are graph-interior.
Under this doctrine, renaming a binder or a `let` that a contract names is an interface
change. -/

/-- **A kind reference** — what a port or introduction states its kind *is*. -/
inductive Provenance.KindRef where
  /-- A kind declaration, by the name the environment resolves. -/
  | decl (n : Lean.Name)
  /-- A generic kind binder of the member's own signature, by binder name. -/
  | param (binder : String)
  /-- A kind signature — the module-valued port form of a functional argument: the
  domains' kinds in order, then the result kind, last. -/
  | sig (components : List Provenance.KindRef)
  /-- A carrier stating several kinds at once — one component per kind parameter, in
  parameter order. -/
  | tuple (components : List Provenance.KindRef)
  /-- A configuration constant that states no kind: the port exists — the address is
  interface — but no kind claim travels with it. -/
  | unkinded
  /-- A kind expression outside this vocabulary, kept as its rendering. Comparison is
  byte-exact and a contract stating one is refused: the class exists so a graph can
  *report* such a kind, not so a boundary can claim one. -/
  | rendered (s : String)
deriving Repr, Inhabited

/-- Structural equality on kind references; the `BEq` instance below. `decl` compares by
`Lean.Name` equality — never by rendering, which is what retires suffix-tolerant matching
and namespace-relative comparison wholesale. -/
def Provenance.KindRef.beq : Provenance.KindRef → Provenance.KindRef → Bool
  | .decl a, .decl b => a == b
  | .param a, .param b => a == b
  | .sig as, .sig bs => go as bs
  | .tuple as, .tuple bs => go as bs
  | .unkinded, .unkinded => true
  | .rendered a, .rendered b => a == b
  | _, _ => false
where
  /-- Component lists, pointwise. -/
  go : List Provenance.KindRef → List Provenance.KindRef → Bool
    | [], [] => true
    | a :: as, b :: bs => a.beq b && go as bs
    | _, _ => false

instance : BEq Provenance.KindRef := ⟨Provenance.KindRef.beq⟩

/-- **A node root** — the class of thing a node identifier's unqualified part denotes. -/
inductive Provenance.NodeRef where
  /-- A kind-typed binder of the member's signature telescope, by accessible user name. -/
  | binder (name : String)
  /-- A body-named node: a kind-bearing `let` binder or a single-alternative matcher
  binder, by accessible user name — one flat namespace per member body. -/
  | letBound (name : String)
  /-- The member's result: the whole result, or the 1-based component of a product
  result. -/
  | result (component : Option Nat)
  /-- A constant address: a configuration port, or a constant-named operand. -/
  | const (n : Lean.Name)
  /-- A synthesized interior node, by mint order. Graph-interior: a contract naming one
  is refused, because a gensym's number is the walk's business and nobody's interface. -/
  | fresh (n : Nat)
  /-- An operand the walk could not resolve into this vocabulary (a literal, a masked
  application), kept as its rendering — visible so an ill-formed graph can say which
  operand offends, and refused in any contract. -/
  | unresolved (rendered : String)
deriving DecidableEq, Repr, Inhabited, BEq

/-- **A level** — the assembly scope a node belongs to. -/
inductive Provenance.Level where
  /-- One call-site instance of a member: the member's declaration name and the 1-based
  instance ordinal. The ordinal is always present — identity does not change when a
  member gains or loses call sites — and the *rendering* collapses it while the member
  has a single instance. -/
  | inst (member : Lean.Name) (ordinal : Nat)
  /-- The member itself, across all its instances: the scope of a configuration port,
  which is an address one deployment binds once however many instances read it. -/
  | member (member : Lean.Name)
deriving DecidableEq, Repr, Inhabited, BEq

/-- **A node identifier**: the level it belongs to (`none` in a single-step graph), the
root reference, and the field-projection path under that root, segments unjoined. -/
structure Provenance.NodeId where
  /-- The assembly scope, or `none` in a single-step graph. -/
  level : Option Provenance.Level := none
  /-- The root reference. -/
  root : Provenance.NodeRef
  /-- The field-projection path under the root, one segment per projection. -/
  path : List String := []
deriving DecidableEq, Repr, Inhabited, BEq

/-- Substitute kind references — the assembly's monomorphization: an exact match in the
assignment is replaced; a `sig` or `tuple` that matches nothing whole is substituted
componentwise, which a rendering-keyed replacement never could; everything else
stands. -/
def Provenance.KindRef.subst (m : List (Provenance.KindRef × Provenance.KindRef)) :
    Provenance.KindRef → Provenance.KindRef
  | .sig cs => match m.find? (·.1 == .sig cs) with
    | some (_, r) => r
    | none => .sig (go cs)
  | .tuple cs => match m.find? (·.1 == .tuple cs) with
    | some (_, r) => r
    | none => .tuple (go cs)
  | k => match m.find? (·.1 == k) with
    | some (_, r) => r
    | none => k
where
  /-- Components in order. -/
  go : List Provenance.KindRef → List Provenance.KindRef
    | [] => []
    | c :: cs => subst m c :: go cs

/-- Render a kind reference in the established grammar: a `decl` by last component, a
`sig` joined with `" → "`, a `tuple` with `", "`, an unkinded config slot as `"_"`. -/
def Provenance.KindRef.render : Provenance.KindRef → String
  | .decl n => Provenance.lastComponent n
  | .param b => b
  | .sig cs => String.intercalate " → " (go cs)
  | .tuple cs => String.intercalate ", " (go cs)
  | .unkinded => "_"
  | .rendered s => s
where
  /-- Components in order. -/
  go : List Provenance.KindRef → List String
    | [] => []
    | c :: cs => c.render :: go cs

/-- Render a node root: names as themselves, `result` / `result.N`, a constant in full —
a config address must not move with a reader's open namespaces — and `_N` for a gensym. -/
def Provenance.NodeRef.render : Provenance.NodeRef → String
  | .binder n | .letBound n => n
  | .result none => "result"
  | .result (some i) => s!"result.{i}"
  | .const n => toString n
  | .fresh n => s!"_{n}"
  | .unresolved r => r

/-- Render a level name: the member's last component, with `#ordinal` from the second
instance up — a member's only instance needs no telling apart, and the reference is the
same either way because the ordinal lives in the identity, not in the name. -/
def Provenance.Level.render : Provenance.Level → String
  | .inst m 1 => Provenance.lastComponent m
  | .inst m k => s!"{Provenance.lastComponent m}#{k}"
  | .member m => Provenance.lastComponent m

/-- Render a node identifier — `level/root.path`. -/
def Provenance.NodeId.render (id : Provenance.NodeId) : String :=
  let base := match id.level with
    | some l => s!"{l.render}/{id.root.render}"
    | none => id.root.render
  id.path.foldl (fun acc seg => s!"{acc}.{seg}") base

/-- A signature-binder node, level-free — the smart constructor authoring uses. -/
def Provenance.NodeId.binder (name : String) : Provenance.NodeId := { root := .binder name }

/-- A body-named node, level-free. -/
def Provenance.NodeId.letBound (name : String) : Provenance.NodeId :=
  { root := .letBound name }

/-- The whole-result node, level-free. -/
def Provenance.NodeId.result : Provenance.NodeId := { root := .result none }

/-- A product-result component node (1-based), level-free. -/
def Provenance.NodeId.resultAt (component : Nat) : Provenance.NodeId :=
  { root := .result (some component) }

/-- A constant-address node, level-free. -/
def Provenance.NodeId.config (n : Lean.Name) : Provenance.NodeId := { root := .const n }

/-- The same node inside one call-site instance of a member. -/
def Provenance.NodeId.within (id : Provenance.NodeId) (member : Lean.Name)
    (ordinal : Nat := 1) : Provenance.NodeId :=
  { id with level := some (.inst member ordinal) }

/-- The same node in a member's shared (all-instance) scope — a configuration port. -/
def Provenance.NodeId.shared (id : Provenance.NodeId) (member : Lean.Name) :
    Provenance.NodeId :=
  { id with level := some (.member member) }

/-- The same node one field projection deeper. -/
def Provenance.NodeId.field (id : Provenance.NodeId) (segment : String) :
    Provenance.NodeId :=
  { id with path := id.path ++ [segment] }

/-- A kind-typed port: one node of a step's interface, with the kind its signature
states and the role it plays. Input and configuration ports are sources; an output port
is a derivation target an occurrence must reach. -/
structure Provenance.Port (ν κ : Type) where
  /-- The port's node identifier. -/
  node : ν
  /-- The kind the signature states for this port. -/
  kind : κ
  /-- The port's role: input, configuration, or output. -/
  dir : Provenance.PortDir
deriving Repr, Inhabited, BEq

/-- A node-introduction event for an interior or source node that is not a port: the
node, the kind it is introduced at, and the evidence tier that introduces it. -/
structure Provenance.Intro (ν κ : Type) where
  /-- The introduced node's identifier. -/
  node : ν
  /-- The kind the node is introduced at. -/
  kind : κ
  /-- The evidence tier: derived interior node, gated ingest, or attested mint. -/
  tier : Provenance.IntroTier
deriving Repr, Inhabited, BEq

/-- One hyperedge occurrence: a use of an edge family at a site — a witness family
discharged, or the identity `copy` wired — relating its ordered operand nodes (each with
the kind the edge names for that position) to its result node. Order matters and
repetition counts — a quotient's numerator and denominator are distinct positions even
when one node fills both — which is why incidence is a list of pairs and not a set. -/
structure Provenance.Occurrence (ν κ : Type) where
  /-- The witness family this occurrence uses. -/
  family : Provenance.EdgeFamily
  /-- The ordered operands: each incident node with the kind the witness names for its
  position. -/
  operands : List (ν × κ)
  /-- The result node the occurrence derives. -/
  result : ν
  /-- The kind the witness names for the result. -/
  resultKind : κ
  /-- The use site the occurrence is attributed to (rendered; a declaration name). Two
  uses of one witness are two occurrences. -/
  site : String
  /-- The operation discharging this occurrence, where the walk saw one: the callee of
  the consuming application that stated the edge, or the scalar head of a same-kind
  carrier sum (`HAdd.hAdd` / `HSub.hSub`). `.anonymous` where the edge has no single
  operation — a wire, a signature box. This is what a value-equation rendering needs
  and the family deliberately abstracts: `additive` covers sum and difference alike,
  and `transcendental` does not say which function. -/
  op : Lean.Name := .anonymous
deriving Repr, Inhabited, BEq

/-- **The metrological provenance hypergraph**, as data: kind-typed ports, node
introductions carrying the audit's evidence tiers, witness-family occurrences with
ordered incidence, and marked exits at the erasure boundary. Parametric in the node
identifier type `ν` and the kind type `κ`; `wellFormed` below is the structural
well-formedness judgment. -/
structure Provenance (ν κ : Type) where
  /-- The interface: kind-typed ports. -/
  ports : List (Provenance.Port ν κ)
  /-- The node-introduction events for non-port nodes, each with its evidence tier. -/
  intros : List (Provenance.Intro ν κ)
  /-- The hyperedge occurrences. -/
  occurrences : List (Provenance.Occurrence ν κ)
  /-- The marked exits: nodes whose values leave the calculus for the bare carrier. -/
  exits : List ν
deriving Repr, Inhabited, BEq

/-- **The aggregation class of a produced port** — how the value behaves when the
module's computation is distributed over a carving of a batch axis and the pieces are
recombined. The vocabulary is Dybkær §13.5's, extended by the classes the mereology
layer has since earned, and each constructor points at the law that cashes it rather
than restating it:

  * `extensive` — §13.5.1: the total over the parts is the value of the whole
    (`Extensive`, `extensive_additive`), so the port's total survives any re-carving
    of the batch axis (`Recarving.leafSum_invariant`; the boundary-level form is
    `Recarving.distribution_license`);
  * `quasiExtensive tolerance` — §13.5.2: additive to within a *named* per-join
    tolerance, a declaration whose type is a `Quantity` at this port's kind — without
    the name, "approximately" is not a claim (`Uncertainty.QuasiExtensive`; what a
    whole carving costs is `joins · t`, and what a re-carving costs is both carvings'
    joins);
  * `conditionallyExtensive condition` — §13.5.3: additive only under a named
    condition the deployment must establish (volume off the mixing case;
    `mixing_subadditive` is what claiming §13.5.1 anyway reports);
  * `intensive` — §13.5.4: invariant with extent, of constant composition
    (`Intensive`, `intensive_uniform`) — a port a shard may *read off any part* and
    must never sum;
  * `wholeProper` — the parts do not determine the value at all (`WholeProper`):
    no distribution over a carving is licensed, and `assemble_ne_measured` is the
    number a library that shards it anyway reports;
  * `countKeyed sortal` — a count of a specified elementary entity, named by its
    sortal predicate (`countMeasurement`). Extensive over a *fixed* carving and not a
    property of the whole (`coalesce_count_ne`), so it travels with its carving — per
    pixel, per shard — and does not survive a re-carving;
  * `extensiveAbout transport` — additive only about a shared parameter (an axis, a
    frame, a datum: `ExtensiveAbout`), with the named transport law pricing what
    reading parts about different parameters costs (`Transports`,
    `extensiveAbout_mixed`);
  * `interfaceLicensed law` — additivity purchased by a named cancellation law over
    pair-indexed interior actions (`InterfaceLedger.netMeasurement_extensive`); a
    shard boundary is a cut, and `mutualTotal` is exactly what crossing it costs when
    the law is dropped (`netTotal_union`). -/
inductive Provenance.AggregationClass where
  /-- §13.5.1: unconditionally additive over the parts. -/
  | extensive
  /-- §13.5.2: additive to within the named per-join tolerance — a declaration whose
  type is a `Quantity` at the governed port's kind. -/
  | quasiExtensive (tolerance : Lean.Name)
  /-- §13.5.3: additive only under the named condition. -/
  | conditionallyExtensive (condition : Lean.Name)
  /-- §13.5.4: invariant with extent, of constant composition. -/
  | intensive
  /-- The parts do not determine the value: no aggregation is licensed. -/
  | wholeProper
  /-- A count keyed to the named sortal predicate — extensive over a fixed carving,
  not a property of the whole. -/
  | countKeyed (sortal : Lean.Name)
  /-- Additive about a shared parameter, with the named transport law pricing a
  parameter change. -/
  | extensiveAbout (transport : Lean.Name)
  /-- Additivity purchased by the named cancellation law over interior interfaces. -/
  | interfaceLicensed (law : Lean.Name)
deriving DecidableEq, Repr, Inhabited, BEq

/-- The declaration an aggregation class names as the content of its claim — the
tolerance, condition, sortal, transport, or cancellation law; `none` for the three
classes whose whole content is the §13.5 law itself. -/
def Provenance.AggregationClass.evidence : Provenance.AggregationClass → Option Lean.Name
  | .extensive | .intensive | .wholeProper => none
  | .quasiExtensive t => some t
  | .conditionallyExtensive c => some c
  | .countKeyed s => some s
  | .extensiveAbout tr => some tr
  | .interfaceLicensed l => some l

/-- How an aggregation class prints in a rendered report. -/
def Provenance.AggregationClass.label : Provenance.AggregationClass → String
  | .extensive => "extensive"
  | .quasiExtensive t => s!"quasi-extensive within {t}"
  | .conditionallyExtensive c => s!"conditionally extensive on {c}"
  | .intensive => "intensive"
  | .wholeProper => "whole-proper"
  | .countKeyed s => s!"count keyed by {s}"
  | .extensiveAbout tr => s!"extensive about {tr}"
  | .interfaceLicensed l => s!"interface-licensed by {l}"

/-- **A declared boundary** (header, "The declared boundary"): the interface an author
claims for a scope — a rendered name, the members claimed for, the ports with the role
and binding time each carries, and the exits where values leave the calculus. It is the
statement a membership choice can be wrong about: `Contract.agrees` holds exactly when
the boundary those members compute is the boundary declared here, so a member added or
dropped changes a difference list rather than passing silently. Same port vocabulary as
the graph's own interface, because it is a claim about that interface and not a second
notation for it. -/
structure Provenance.Contract (ν κ : Type) where
  /-- The rendered name of what the boundary belongs to — an algorithm, an application. -/
  name : String
  /-- The scope: the declarations whose harvested graphs the boundary is claimed for,
  by the names the environment resolves. Not compared by `agrees`, which sees only the
  graph they produced — they are what *selects* that graph, and stating them here is what
  makes the selection a declaration rather than a habit of each call site. -/
  members : List Lean.Name
  /-- The declared interface, with each port's role and binding time. -/
  ports : List (Provenance.Port ν κ)
  /-- The declared exits: where the contract says values leave the calculus. -/
  exits : List ν
  /-- The deciders of the conditional ports: for a `conditional` port, the name of the
  declaration that decides its cases — the `KindAdmissible` instance, domain predicate,
  or validity check a consumer consults. The role states that cases exist; the decider
  states *which*, by name, where a consumer reads it. One entry per decided port,
  checked by `#kind_contract` to name a conditional port and an existing declaration; a
  conditional port with no entry remains a declared case whose predicate is stated
  elsewhere. -/
  deciders : List (ν × Lean.Name) := []
  /-- The aggregation classes of the produced ports: for an `output` or `conditional`
  port, how its value behaves when the computation is distributed over a carving of a
  batch axis — the declared mereology of the boundary (`AggregationClass`). One entry
  per classed port, checked by `#kind_contract` to govern a produced port and, where
  the class names a tolerance, condition, sortal, transport, or law, to name an
  existing declaration (a tolerance additionally a `Quantity` at the port's kind). A
  produced port with no entry makes no distribution claim — and the license to shard
  it is then nobody's to derive. -/
  aggregations : List (ν × Provenance.AggregationClass) := []
  /-- The suppliers of the module-valued ports: for a port whose kind is a *signature*
  (the `→`-joined port form of a functional argument), the name of the module this
  tier binds to it. One entry per supplied port, checked by `#kind_contract` to govern
  a signature port and to name an existing declaration whose own kind signature is the
  declared one — so *which* module a deployment bound is declared and checked, not
  implicit in a call site. A signature port with no entry remains a parameter: which
  module answers it is then the tier below's to declare. -/
  suppliers : List (ν × Lean.Name) := []
deriving Repr, Inhabited, BEq

namespace Provenance

variable {ν κ : Type} [BEq ν] [BEq κ]

/-- The kind a node is declared at — by a port, or else by an introduction event.
`none` for an undeclared node. -/
def kindOf? (g : Provenance ν κ) (n : ν) : Option κ :=
  match g.ports.find? (·.node == n) with
  | some p => some p.kind
  | none => (g.intros.find? (·.node == n)).map (·.kind)

/-- The sources: the nodes known before any occurrence fires — every port the step does
not produce (inputs, configuration reads, and the parameters a tier leaves unbound),
gated ingests, and attested mints. -/
def sources (g : Provenance ν κ) : List ν :=
  (g.ports.filter (fun p => !p.dir.produced)).map (·.node)
    ++ (g.intros.filter (·.tier.isSource)).map (·.node)

/-- One monotone sweep of the closure: each occurrence whose operands are all known
adds its result, in occurrence order. -/
def sweep (occs : List (Occurrence ν κ)) (ks : List ν) : List ν :=
  occs.foldl (init := ks) fun ks o =>
    if o.operands.all (fun oc => ks.contains oc.1) && !ks.contains o.result then
      ks ++ [o.result]
    else ks

/-- `fuel` sweeps of the closure, starting from `ks`, stopping at the fixpoint. A sweep
only ever appends, so a sweep that adds nothing has reached one, and — `sweep` being a
function of `ks` alone — every later sweep would add nothing either. Running the fuel out
regardless would cost one pass per occurrence where the graph's depth is what the closure
actually needs, and this checker is reduced by the *kernel*: an assembly whose members
carry several call sites multiplies its occurrences, and the sweep is the cubic term. -/
def sweeps (occs : List (Occurrence ν κ)) : Nat → List ν → List ν
  | 0, ks => ks
  | fuel + 1, ks =>
    let ks' := sweep occs ks
    if ks'.length == ks.length then ks else sweeps occs fuel ks'

/-- The nodes *derivable* from a chosen starting set through the occurrences: the least
fixpoint of "an occurrence whose operands are ALL known makes its result known", in
discovery order. One sweep per occurrence saturates, since each productive sweep adds at
least one result. Forward derivability on the hypergraph, asked of whatever start set the
question is about rather than assumed of the whole graph. The conjunctive rule is what
`wellFormed`'s central condition needs — a node is accounted for only once everything it
is built from is — and it is deliberately *not* the influence relation a sensitivity query
asks for: whether *some* operand carries a value onward is a disjunctive closure over the
same incidence, a different query on the same data. -/
def reachableFrom (g : Provenance ν κ) (start : List ν) : List ν :=
  sweeps g.occurrences g.occurrences.length start

/-- The nodes reached from the sources through the occurrences — `reachableFrom` at the
start set `wellFormed`'s central condition asks about. -/
def known (g : Provenance ν κ) : List ν := g.reachableFrom g.sources

/-- Every node is declared exactly once, ports and introductions jointly: a node with
two declarations would have two kinds or two tiers, and every lookup would silently
choose one. -/
def uniquelyDeclared (g : Provenance ν κ) : Bool :=
  let ids := g.ports.map (·.node) ++ g.intros.map (·.node)
  ids.all fun n => (ids.filter (· == n)).length == 1

/-- Every occurrence is typed: its operand count is its family's, and each operand and
the result carry exactly the kind the corresponding node's declaration states — so an
occurrence cannot re-kind a node, and cannot touch an undeclared one. A `copy` must
additionally preserve the kind: the identity wire's claim is structural, so it is the
one family whose equation well-formedness itself checks (header, "The identity
wire"). -/
def occurrencesTyped (g : Provenance ν κ) : Bool :=
  g.occurrences.all fun o =>
    o.operands.length == o.family.operandCount
      && o.operands.all (fun oc => g.kindOf? oc.1 == some oc.2)
      && g.kindOf? o.result == some o.resultKind
      && (!(o.family matches .copy) || o.operands.all (fun oc => oc.2 == o.resultKind))

/-- Every occurrence's result is a derivation target: a `derived` introduction or an
output port. Never a source — a gated or attested node's whole point is that its kind
is *not* derived — and never an input or configuration port. -/
def resultsAreDerivations (g : Provenance ν κ) : Bool :=
  g.occurrences.all fun o =>
    g.intros.any (fun i => i.node == o.result && i.tier == .derived)
      || g.ports.any (fun p => p.node == o.result && p.dir.produced)

/-- The central condition — the boundary audit's "raw mints = 0", compositional: every
`derived` introduction, every output port, and every exit is in `known`, i.e. reached
from the sources through the occurrence closure. A derived node no occurrence chain
produces is an anonymous mint; an occurrence cycle feeding itself licenses nothing,
because the closure starts from the sources. -/
def sourcesReach (g : Provenance ν κ) : Bool :=
  let ks := g.known
  g.intros.all (fun i => !(i.tier == .derived) || ks.contains i.node)
    && g.ports.all (fun p => !p.dir.produced || ks.contains p.node)
    && g.exits.all ks.contains

/-- Structural well-formedness of the provenance hypergraph: unique declarations, typed
occurrences, results on derivation targets only, and sources reaching every derived
node, output, and exit. Decided by evaluation in a probe and by kernel reduction in a
proof; the truth of each edge remains the authored claim the trust model reviews by
enumeration. -/
def wellFormed (g : Provenance ν κ) : Bool :=
  g.uniquelyDeclared && g.occurrencesTyped && g.resultsAreDerivations && g.sourcesReach

/-- `Prop`-level well-formedness, for statements and `decide`. -/
def WellFormed (g : Provenance ν κ) : Prop := g.wellFormed = true

instance (g : Provenance ν κ) : Decidable g.WellFormed :=
  inferInstanceAs (Decidable (g.wellFormed = true))

/-! ## The declared boundary — scope as a comparison (header, "The declared boundary") -/

/-- Does a declared port stand for a computed one: the same node at the same kind, under
a role that refines the computed role (`PortDir.refines` — only `param` for `input`). -/
def Contract.standsFor (q p : Port ν κ) : Bool :=
  q.node == p.node && q.kind == p.kind && q.dir.refines p.dir

/-- The computed boundary ports the contract does not declare. This is where a widened
scope surfaces: a member whose inputs nothing in the assembly feeds contributes ports
nobody claimed, and a member whose kinds the wiring instantiates differently contributes
a port at a kind nobody claimed. -/
def Contract.undeclared (c : Contract ν κ) (g : Provenance ν κ) : List (Port ν κ) :=
  g.ports.filter fun p => !(c.ports.any (Contract.standsFor · p))

/-- The declared ports the computed boundary does not exhibit. This is where a narrowed
scope surfaces: drop the member that fed an operand and the wire disappears with it, so
the port the contract promised is no longer there to be found. -/
def Contract.unrealized (c : Contract ν κ) (g : Provenance ν κ) : List (Port ν κ) :=
  c.ports.filter fun q => !(g.ports.any fun p => Contract.standsFor q p)

/-- The computed exits the contract does not declare — a value leaving the calculus where
the boundary says none does. -/
def Contract.undeclaredExits (c : Contract ν κ) (g : Provenance ν κ) : List ν :=
  g.exits.filter fun n => !(c.exits.contains n)

/-- The declared exits the graph does not exhibit. -/
def Contract.unrealizedExits (c : Contract ν κ) (g : Provenance ν κ) : List ν :=
  c.exits.filter fun n => !(g.exits.contains n)

/-- The contract declares each node once — the hygiene `uniquelyDeclared` demands of the
graph, asked of the claim, so two declarations cannot jointly cover one computed port
while one of them stands for nothing. -/
def Contract.declaresUniquely (c : Contract ν κ) : Bool :=
  let ids := c.ports.map (·.node)
  ids.all fun n => (ids.filter (· == n)).length == 1

/-- The parameters the contract leaves unbound: the source ports whose values a tier
below binds. Every one of them is an obligation on that tier, which either binds it to a
configuration constant or restates it as a parameter of its own. -/
def Contract.params (c : Contract ν κ) : List ν :=
  (c.ports.filter (·.dir == .param)).map (·.node)

/-- **The declared boundary is the computed one**: every computed port declared, every
declared port exhibited, the same for exits, over a contract that declares each node
once. The scope judgment `wellFormed` structurally cannot make (header, "What
well-formedness does not claim"), decided by evaluation in a probe and by kernel
reduction in a proof exactly as the wiring verdict is. It re-adjudicates no wiring: the
two verdicts stand on one object, the first saying the graph holds together and this one
saying it is the graph someone meant. -/
def Contract.agrees (c : Contract ν κ) (g : Provenance ν κ) : Bool :=
  c.declaresUniquely
    && (c.undeclared g).isEmpty && (c.unrealized g).isEmpty
    && (c.undeclaredExits g).isEmpty && (c.unrealizedExits g).isEmpty

/-- `Prop`-level agreement, for statements and `decide`. -/
def Contract.Agrees (c : Contract ν κ) (g : Provenance ν κ) : Prop := c.agrees g = true

instance (c : Contract ν κ) (g : Provenance ν κ) : Decidable (c.Agrees g) :=
  inferInstanceAs (Decidable (c.agrees g = true))

/-! ### The tier relation — a parameter is not discharged by being forgotten

`agrees` needs the graph; this does not. A deployment states what it did with an
algorithm's parameters by comparing two *declarations*, so the ladder can be stated
across a repository boundary — with the algorithm's contract imported and its members
never re-walked. -/

/-- The members of the deployed contract `d` that the deploying contract `c` does not
contain. Non-empty means `c` is not a deployment of `d` at all: it left part of the
algorithm out, and whatever it discharges it is not discharging this. -/
def Contract.unscoped (c d : Contract ν κ) : List Lean.Name :=
  d.members.filter fun m => !(c.members.contains m)

/-- The parameters of `d` that `c` **binds**: they are gone from `c`'s boundary, which
means a member of `c` feeds them — the wire that discharges an obligation is the wire
that makes the port interior. -/
def Contract.bound (c d : Contract ν κ) : List ν :=
  d.params.filter fun n => !(c.ports.any fun p => p.node == n)

/-- The parameters of `d` that `c` inherits and does not answer for: still at `c`'s
boundary, and no longer called parameters there. Binding one is an act — a constant, a
wire — and relabelling it per-datum data is not that act, so the obligation would leave
the ladder without anyone taking it. -/
def Contract.undischarged (c d : Contract ν κ) : List ν :=
  d.params.filter fun n =>
    (c.ports.any fun p => p.node == n) && !(c.params.contains n)

/-- The exits of `d` that `c` does not exhibit: a value that left the calculus one tier
down cannot stop having left it one tier up. -/
def Contract.droppedExits (c d : Contract ν κ) : List ν :=
  d.exits.filter fun n => !(c.exits.contains n)

/-- **`c` is a deployment of `d`, and it has answered for what `d` handed down**: it
contains every member of `d`, every parameter of `d` is either bound within `c` or
restated as a parameter of `c`, and every exit of `d` is still an exit of `c`. The
tier ladder as one decidable relation between declarations — where `agrees` says a
contract is the boundary its own members compute, this says the tiers stack. -/
def Contract.discharges (c d : Contract ν κ) : Bool :=
  (c.unscoped d).isEmpty && (c.undischarged d).isEmpty && (c.droppedExits d).isEmpty

/-- `Prop`-level discharge, for statements and `decide`. -/
def Contract.Discharges (c d : Contract ν κ) : Prop := c.discharges d = true

instance (c d : Contract ν κ) : Decidable (c.Discharges d) :=
  inferInstanceAs (Decidable (c.discharges d = true))

/-! ### The theorem edge — what a tier cannot say

`agrees` compares a declaration with the graph its members compute; `discharges` compares
two declarations. Neither can say that one boundary *inverts* another, that two agree
wherever a hypothesis holds, or that one departs from another by no more than a stated
quantity. Those are theorems, and a theorem is not a port list — it is the one thing in
this development that is proved rather than computed, and the tier ladder was silent about
it. `Relation` is the edge that carries one: which two boundaries it is about, what it
claims of them, and the name of the proof.

Nothing about a `Relation` is decidable, which is why it is not a third `Bool` beside the
two above. What *is* checkable is everything around the proof, and `#kind_relation` checks
it: that the witness is a theorem rather than a definition or an axiom, that its axiom
profile carries no `sorryAx`, that the shape of its conclusion is the shape the claimed
kind names — an `Eq` for `equals`, an order relation for `boundedBy`, for `inverts` an
`Eq` one of whose sides composes members of both boundaries, and for `refines` an `Eq`
under at least one stated hypothesis — and — the check that keeps the edge from being
decoration — that the statement **mentions members of both boundaries**. A theorem naming
neither is a true statement about something else, and citing it here would relate nothing.
The optional clauses are checked the same way: a named `tolerance` must be a `Quantity` at
the kind of an output port of the boundary it governs, a named hypothesis must be a
declaration the witness statement mentions, and every `licenses` rung must name a
sorry-free theorem as its repair or restatement — a rung claimed with neither is refused,
because a side condition does not transfer by being assumed to (`RelationLicense`). An
`inverts` edge may further answer for its inversion: `wellPosed` names the sorry-free
theorem concluding with `∃!` that proves the answer exists and is unique on the `domain`
declared beside it (a well-posedness with no declared domain is refused), and `ambiguity`
names the sorry-free theorem concluding with the negation of an `∃!` that surfaces where
uniqueness fails — the two honest answers to the same question, and the census over
`inverts` edges (`#kind_wellposedness_coverage`) asks each edge for one of them. -/

/-- How a relation edge stands at one carrier rung, given that laws transfer across the
carrier ladder and side conditions do not (`Aggregation`, "side conditions do not
transfer"): a side condition checked at the spec carrier constrains the exact value, at an
executable carrier the rounded one, and neither implies the other. So a relation claimed
at more than the rung its witness is stated at owes, per additional rung, either the name
of the repair theorem that carries it across — `exact` where rounding is the identity on
the values in play (counts, indicator weights; the `licenses_agree_of_exact` shape) or
`nonneg` where nonnegative on-grid weights rule the cancellation out (the
`licenses_agree_of_nonneg` shape) — or `restated`: an independent witness proved at that
rung, transferring nothing. -/
inductive TransferStatus where
  /-- Transferred because rounding is the identity on the values in play; the field names
  the repair theorem. -/
  | exact (repair : Lean.Name)
  /-- Transferred because nonnegative on-grid weights exclude the cancellation; the field
  names the repair theorem. -/
  | nonneg (repair : Lean.Name)
  /-- Not transferred: independently stated at this rung; the field names the per-rung
  witness. -/
  | restated (witness : Lean.Name)
deriving Repr, Inhabited

/-- The theorem or repair a transfer status rests on. -/
def TransferStatus.evidence : TransferStatus → Lean.Name
  | .exact r | .nonneg r | .restated r => r

/-- How a transfer status prints in a rendered report. -/
def TransferStatus.label : TransferStatus → String
  | .exact r => s!"exact via '{r}'"
  | .nonneg r => s!"nonneg via '{r}'"
  | .restated w => s!"restated by '{w}'"

/-- One rung of a relation's license clause: the carrier rung the claim is extended to,
spelled as the ladder names it (`ℝ`, `FP32`, `Float`, …), and how the claim holds there.
A relation with an empty license list is stated at its witness's own rung and claims
nothing beyond it; each entry here is one further rung, answered for by name. -/
structure RelationLicense where
  /-- The carrier rung, as the ladder names it. -/
  rung : String
  /-- How the claim holds at this rung: transferred by a named repair, or restated by a
  named per-rung witness. -/
  transfer : TransferStatus
deriving Repr, Inhabited

/-- How a license rung prints in a rendered report. -/
def RelationLicense.label (l : RelationLicense) : String :=
  s!"{l.rung} — {l.transfer.label}"

/-- What a theorem claims about two declared boundaries. -/
inductive RelationKind where
  /-- The left boundary recovers what the right one consumed — an inversion, at the
  equation the witness states and on the domain it states it. The witness concludes with
  an `Eq` one of whose sides composes members of both boundaries — the round trip. -/
  | inverts
  /-- The left boundary answers as the right one does wherever a stated hypothesis holds:
  the same value on a smaller domain. The witness concludes with an `Eq` and binds at
  least one hypothesis — the domain it holds on. -/
  | refines
  /-- The two boundaries return the same value. The witness concludes with an `Eq`. -/
  | equals
  /-- The left boundary's departure from the right is bounded by a stated quantity. The
  witness concludes with an order relation. -/
  | boundedBy
deriving DecidableEq, Repr, Inhabited

/-- How a relation prints in a rendered report. -/
def RelationKind.label : RelationKind → String
  | .inverts => "inverts"
  | .refines => "refines"
  | .equals => "equals"
  | .boundedBy => "bounded by"

/-- **A theorem edge between two declared boundaries** (header, "The theorem edge"): the
two contracts, spelled as the environment names them, what the theorem claims of them, the
theorem itself, and the claim in the author's own words — the hypothesis a `refines` holds
under, the quantity a `boundedBy` is bounded by. (The field is `claim` and not `says`
because `says` is a Mathlib tactic keyword, and a field name that cannot be written in a
`where` block downstream is not a field name.) The prose is not checked and is not meant
to be: what is checked is that the named theorem exists, is proved, and is about these two
boundaries. -/
structure Relation where
  /-- The declaration name of the contract on the left of the claim. -/
  left : Lean.Name
  /-- The declaration name of the contract on the right. -/
  right : Lean.Name
  /-- What is claimed. -/
  kind : RelationKind
  /-- The declaration name of the theorem that proves it. -/
  witness : Lean.Name
  /-- The claim in the author's words — the hypothesis, the bound, the domain. -/
  claim : String := ""
  /-- For a `boundedBy` edge: the declaration naming the bounding quantity — a `Quantity`
  at the kind of an output port of the left boundary, because a tolerance is a kinded
  quantity governing what the boundary produces, not a float in prose. Anonymous where
  the claim carries its bound inside the witness statement. -/
  tolerance : Lean.Name := .anonymous
  /-- The named side conditions the claim holds under: declarations the witness statement
  mentions, so the domain a consumer must establish is listed at the edge rather than
  excavated from the proof. Empty where the claim is unconditional. -/
  hypotheses : List Lean.Name := []
  /-- The license clause: one entry per carrier rung the claim is extended to beyond the
  rung its witness is stated at, each answered for by a named repair or a named per-rung
  restatement (`RelationLicense`). Empty where the claim stops at its witness's rung. -/
  licenses : List RelationLicense := []
  /-- For an `inverts` edge: the declaration name of the theorem that proves the
  inversion's answer exists and is unique — a sorry-free theorem concluding with `∃!` —
  on the domain named beside it. Anonymous where well-posedness is not (or not yet)
  claimed; an edge whose inversion is *not* single-valued surfaces that in `ambiguity`
  instead. -/
  wellPosed : Lean.Name := .anonymous
  /-- The declaration naming the domain the well-posedness holds on — the box or
  predicate the `wellPosed` statement mentions. Existence and uniqueness are proved *on a
  declared domain*, so a `wellPosed` with no `domain` is refused. -/
  domain : Lean.Name := .anonymous
  /-- For an `inverts` edge: the declaration name of the theorem that surfaces the
  inversion's ambiguity — a sorry-free theorem concluding with the negation of an `∃!`,
  the uniqueness that fails (typically: without the domain's certificate). Ambiguity is
  surfaced as a declaration a consumer can read, not resolved to whichever root the
  algorithm reached first. -/
  ambiguity : Lean.Name := .anonymous
deriving Repr, Inhabited

/-! ## The assembly combinators — namespaced union (header, "The procedure edge") -/

/-- Rename every node through `f` — ports, introductions, occurrence incidence and
results, exits. An assembly renames each level graph into its own namespace before
taking the union, so two steps' interior `_1`s can never collide. -/
def mapNodes {ν' : Type} (f : ν → ν') (g : Provenance ν κ) : Provenance ν' κ where
  ports := g.ports.map fun p => ⟨f p.node, p.kind, p.dir⟩
  intros := g.intros.map fun i => ⟨f i.node, i.kind, i.tier⟩
  occurrences := g.occurrences.map fun o =>
    ⟨o.family, o.operands.map (fun oc => (f oc.1, oc.2)), f o.result, o.resultKind, o.site,
     o.op⟩
  exits := g.exits.map f

/-- Rename every kind through `f` — the assembly's monomorphization: a kind-generic
callee's level graph states its kinds by binder name, and the call site that wires it
supplies the instantiated kinds, so the box is renamed through the call's kind
assignment before the union. -/
def mapKinds {κ' : Type} (f : κ → κ') (g : Provenance ν κ) : Provenance ν κ' where
  ports := g.ports.map fun p => ⟨p.node, f p.kind, p.dir⟩
  intros := g.intros.map fun i => ⟨i.node, f i.kind, i.tier⟩
  occurrences := g.occurrences.map fun o =>
    ⟨o.family, o.operands.map (fun oc => (oc.1, f oc.2)), o.result, f o.resultKind, o.site,
     o.op⟩
  exits := g.exits

/-- Field-wise union. On namespaced (node-disjoint) operands this is the assembly's
disjoint sum; the cross-wires that connect the levels are ordinary `copy` occurrences
added on top, and well-formedness is then checked on the assembled object itself. -/
def union (g h : Provenance ν κ) : Provenance ν κ where
  ports := g.ports ++ h.ports
  intros := g.intros ++ h.intros
  occurrences := g.occurrences ++ h.occurrences
  exits := g.exits ++ h.exits

end Provenance

end PropertyKindCalculus
