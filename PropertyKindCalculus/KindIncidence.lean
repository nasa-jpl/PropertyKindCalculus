/-
# `#kind_graph` — the step harvest: one constructed object, rendered per reading

A step is a declaration, and this module reads it into the metrological provenance
hypergraph as *data*: `stepGraphOf` constructs the `Provenance` value — ports off the
kind-typed signature, occurrences and interior nodes off the elaborated value, exits at
the erasure boundary — and every report is a rendering *of* that one producer, so the
pins sit on one reading and well-formedness is checked on the object rather than read
off a report by a person:

    #kind_ports myStep         -- the interface: input / config / output ports
    #kind_occurrences myStep   -- the authored licenses discharged inline, with incidence
    #kind_graph myStep         -- the whole object, with its well-formedness verdict
    #kind_graph_decide myStep  -- the kernel checks the wiring (an added `decide` theorem)
    #kind_assembly [a, b, …]        -- the multi-step graph of a pipeline, one object
    #kind_assembly_decide [a, b, …] -- the kernel checks the assembled wiring
    #kind_contract c                -- the declared boundary against the computed one
    #kind_contract_decide c         -- the kernel checks the declared boundary
    #kind_contracts ns…             -- every contract in scope, swept by type, one report
    #kind_contracts_decide ns…      -- the sweep as a hard gate, kernel receipts added
    #kind_discharges c d            -- what a deploying contract did with what it inherited
    #kind_discharges_decide c d     -- the kernel checks that the tiers stack

Wherever a scope has a contract, the two assembly commands take its name in place of the
bracket list — `#kind_assembly c` — so the member list is spelled once, in the
declaration that answers for it, and every reading of that scope is a reading of the
same members.

**Ports** are read off what the signature *states*: the telescope's carrier-typed
binders are input ports (in signature order), the result type's carrier-typed right-spine
product components are output ports (positions kept — `result.1`, `result.3` across an
un-kinded component, so a gap stays visible), and the `@[kindConst]` constants the value
reads are configuration ports, deduplicated — a port is an interface node, so a constant
read twice is one port while the occurrence reading keeps both incidence positions, and
the two readings name the node identically. The kind position inside a carrier
application is found generically — the argument whose instantiated binder type is
`KindOfProperty` — so a downstream `@[kindCarrier]` registration ports correctly wherever
its kind parameter sits. Roles are `Provenance.PortDir`: the harvest speaks the graph
structure's vocabulary directly.

A **container** position — a single-constructor structure that is not itself a carrier,
whose fields reach carriers — states its kinds through those fields, and ports as one
node per carrier **field path** (`carrierPaths`): a `Quantity`-endpoint interval states
its kind twice, at `span.lo.q` and `span.hi.q`, and a bundle of quantities states one
port per constituent. The path is the node name, so a port reads exactly as the body
spells the projection and the two readings meet at the same node; a field path reaching a
target is an identity wire, like a binder. This is what lets an interface bundle its
arguments — a direction-locked interval instead of a pair of scalars a call site could
swap — without the graph losing sight of what crosses it: the reading follows the type,
and a bundled signature states MORE than the loose one, not less. The same expansion is
what an *operand* gets: a container handed whole to an edge-bearing or sub-step
application contributes one incidence position per field path, named as the wrapper spells
it, so putting a quantity into a role — a portion, a total, an axis extent — costs the
graph no operand. A `@[kindConst]` constant of container type expands the same way, into
one config port per field path: a configured quantity does not stop being one for
travelling in a role, and the deployment constant that fills a roled binder must reach the
same node the callee's port names. And a *produced* container expands at its binding: a
`let` whose type is a container, or a nested call whose value one consumes, lands on one
node per field path rather than on a single opaque node, so a step that computes a bundled
value and hands it on is wired rather than read as having computed nothing. And a
container *assembled* — a single-constructor application, the anonymous `Prod.mk`
included — splits at its constructor, each field landing on the slot its own path names,
so a step that returns its components bundled wires exactly as the one that returns them
loose. Interface, operand, configuration constant, binding, assembly: the expansion is the
same at every position a bundle can occupy, which is the property that makes bundling free
— a container costs the reading nothing wherever it appears, so an author never has to
choose between a role and a graph. A sum type has no field path (which constructor a value took is not a signature
fact), and a carrier is a leaf, never a container — its own field is the erasure boundary.

**Occurrences** sit on the consuming application: any constant-headed application with a
binder whose instantiated type is a witness-family `Prop` — the smart constructors, and
equally a downstream helper that threads a witness parameter. Reading the edge off the
instantiated *binder type*, not the witness argument's own spelling, keeps the reading
channel-agnostic (inline constructor, lifted or shared `._proof_N` reference, `let`-bound
witness — one line). The operator-table families are read the same way plus **one level
of instance unfolding**: a `[table]` product's use site (`x * y`) carries its license in
an instance argument, so the walk looks through a constant-headed instance argument's
own telescope for the `KindMul`/`KindDiv` position — the registered instance is the
authored license, and a threaded instance *binder* is an assumption, exactly parallel to
a hypothesis witness. An occurrence whose license is a hypothesis or instance binder is
marked **assumed**: it wires the step's own graph (the derivation is real, licensed by
the interface's assumption), but the enumeration rendering excludes it — the authored
occurrence sits at the caller that discharges the license, which is also where
carrier-generic code becomes concrete. A consuming signature that exposes fewer carrier
operands than the family relates is a **sub-step boundary**: the occurrence is marked
*partial*, the graph excludes it from the wiring, and the step's verdict honestly refuses
— one step's graph states what its own body exhibits; composition across steps is the
assembly's, not the harvest's.

**Wiring** makes the interface reachable. Occurrence results land on the node the
structure assigns — the `let` binder they define, the output port they produce, or a
synthesized interior node (`_1`, `_2`, … in walk order) when the producer sits in an
argument position. A producer that *names* a node instead of deriving one — a
pass-through binder, a configuration constant, a tuple component — reaches its port
through the identity wire (`Provenance`, "The identity wire — `copy`"). An attestor
application (`Quantity.attest` and every `@[kindAttest]` registration) introduces an
`attested` source carrying its harvested reason; a `@[kindIngest]`-headed application
introduces a `gated` source; a `@[kindConst]` declaration's own value is wired through an
`attested "[kindConst]"` source; a `@[kindEmission]` declaration's carrier-constructor
mints — the sanctioned grid↔kernel shell — enter through `attested "[kindEmission]"`
sources: the audit's tiers, carried into the graph. A carrier projection marks its
operand as an **exit**: the erasure boundary, beyond which the byte gate carries the
claim. The do-elaboration's administrative heads (`Id.run`, `pure`, `bind`, `letFun`,
`ite`/`dite`, and a single-alternative matcher — tuple destructuring) are transparent
to the walk, so a straight-line monadic body wires exactly like its pure spelling; a
loop stays opaque. A multi-alternative matcher stays opaque too *unless its
discriminant is a nominal designation* (`BoundaryAudit`, "The nominal designation
registry"), in which case it is a **selection**: every alternative produces onto its own
node at the result's kind, and one `select` edge relates the label and those nodes to
the result. That is the one control flow the calculus can read, and it can read it for
the reason the nominal scale exists — a `match` on a label set is an equality
comparison, the only operation such a value licenses, and every branch of it already
carries the kind the result does. What no reading
recognizes — a raw `⟨…⟩` mint, an opaque sub-step call outside an assembly, a loop
body's result, a point-free body — produces nothing, and the verdict says so: an
unreached derivation target is exactly an anonymous mint. A container *value* is
attributed where the structure assigns its slots — a call destructured into a container
binder derives each of that binder's field paths, and a container assembled by its own
constructor splits per field (`ctorFieldSlots`), packaging being transparent to
dataflow. An assembling *call* is not: a smart constructor is a step like any other,
opaque outside an assembly, and its result's ports stay unreached until the assembly
reads it.

**Unkinded positions** are read alongside the ports: an explicit binder or result
component whose type carries no kind information at all — no registered carrier and no
kind vocabulary anywhere in it, after reducible unfolding, beneath a single-constructor
head's fields, or in a type argument — is naked data crossing the interface, which does not
conform to the calculus's methodology. The kinded readings gap-keep such a position;
the harvest additionally *names* it (`unkinded input nR : Nat`), so a report marks it
red instead of silently narrowing to the kinded slice. The value walk pairs the
inventory with the **unkinded flows**: an unkinded argument occurring in a minting
application (attested, gated, emission) flows into that mint's node — unkinded
information minting kinded information — and one occurring in a kinded output's
defining expression *outside* every mint steers that output through logic the kinded
algebra never sees; both render as `unkinded flow: nR ⇒ _1` and draw red in the
figure. A kind-bearing type with no carrier field path — a sum over quantities, a
function returning them — is neither ported nor red: it carries kinds, and what crosses
the interface is not a quantity; propositions and sorts are interface logic, not data,
and are not read.

**Assembly** reads a pipeline as ONE graph (section, "The assembly"): the members
become each other's sub-steps, a call becomes a `step` procedure edge, walked call
sites dissect into the callee's box, and the verdict — with its kernel theorem — is
computed on the assembled multi-step object. What the assembly's ports state after
dissection is its **boundary**: the inputs no member feeds and the outputs no member
takes, since demotion runs at both ends of a wired call. A boundary is a claim about
scope, so it is compared against a declared one — `Provenance.Contract` — and not merely
reported: the wiring verdict is monotone under adding an unrelated member, and the
boundary is what changes when the membership does.

**A node identifier and a kind identifier are typed references** (`Provenance.lean`, "The
reference vocabulary"): a `NodeId` says which class of thing it names — a signature
binder, a body-named `let` or matcher binder, a result component, a constant address, a
gensym — and a `KindRef` names a kind declaration by the name the environment resolves, a
signature binder's kind parameter by its binder name, or a signature/tuple of those.
Identity is absolute and structural — a boundary someone declares means one thing wherever
it is checked, in no reader's namespace — and the familiar spellings (`step/span.lo.q`,
`aK → bK`) are *renderings* of those references, produced for reports and never compared.
The harvest refuses a member whose kind-bearing names are inaccessible or duplicated in
their scope, so every reference that reaches a graph names its referent uniquely.

The byte-identical renderings are the spot check, not the license: `#kind_ports` and
`#kind_occurrences` print exactly the lines they printed as free-standing harvests, now
as projections of the constructed object.

This module, not `KindEdges`, holds the readings because ports and operand positions are
identified by the boundary audit's **carrier registry** (`kindCarrierNames`) and the
tiers by its boundary and attestor registries, and importing the audit puts its
meta-heavy bodies into `producerModules`' walk set — a cost every `#kind_edges` consumer
would pay. Per-declaration reading walks one signature and one value, so it is cheap
here; files that pin both readings keep them in separate modules.
-/
import PropertyKindCalculus.KindEdges
import PropertyKindCalculus.IndividualQuantity
import PropertyKindCalculus.BoundaryAudit
import PropertyKindCalculus.Provenance
import PropertyKindCalculus.AuditReceipt

namespace PropertyKindCalculus.KindIncidence

open Lean
open PropertyKindCalculus.Provenance (Port Intro Occurrence EdgeFamily IntroTier PortDir
  KindRef NodeRef NodeId lastComponent)

/-- The carrier heads an operand position is recognized by: the audit's registry
(`Quantity`, `CertifiedQuantity`, `NominalValue`, plus every downstream `@[kindCarrier]`
registration), and `IndividualQuantity` — not a boundary-audit carrier (registering it
would put its constructor and projection on the mint/erase report), but its
kind-licensed operations consume the same witnesses. A carrier-*generic* telescope
(operands at a variable type) contributes its occurrences at the monomorphic call
sites, the same places its witnesses are discharged. -/
def operandCarriers (env : Environment) : Array Name :=
  BoundaryAudit.kindCarrierNames env ++ #[``PropertyKindCalculus.IndividualQuantity]

/-- The declared constant mints — every `@[kindConst]`-tagged declaration in scope. -/
def configConstants (env : Environment) : NameSet :=
  (BoundaryAudit.boundaryTags env).foldl (init := .empty) fun s t =>
    if t.tier == .kindConst then s.insert t.decl else s

/-- The checked-ingest mints — every `@[kindIngest]`-tagged declaration in scope. -/
def ingestConstants (env : Environment) : NameSet :=
  (BoundaryAudit.boundaryTags env).foldl (init := .empty) fun s t =>
    if t.tier == .kindIngest then s.insert t.decl else s

/-- The binder context of a value walk, innermost first: each entry a binder's user name
and, for a `let`, its value — the name renders `.bvar` operands, the value resolves a
`let`-bound witness to its authored head. A `let` value is an expression of the *outer*
context, so resolution drops the entries above it. -/
abbrev BinderCtx := List (Name × Option Expr)

/-- Is a witness (or instance) argument *authored* — headed by a constant (a
smart-constructor application, a lifted or shared auxiliary reference, a named-theorem
or registered-instance reference), possibly through a `let` binding? A free or
lambda-bound variable is a hypothesis: assumed, not authored — its occurrence is marked
`assumed`, and the authored occurrence sits at the discharging caller. -/
partial def witnessAuthored (ctx : BinderCtx) (w : Expr) : Bool :=
  match w with
  | .app f _ => witnessAuthored ctx f
  | .mdata _ b => witnessAuthored ctx b
  | .const .. => true
  | .bvar i =>
    match ctx[i]? with
    | some (_, some v) => witnessAuthored (ctx.drop (i + 1)) v
    | _ => false
  | .letE nm _ v b _ => witnessAuthored ((nm, some v) :: ctx) b
  | _ => false

/-- Render an operand as a *name* — a binder name for a variable, a **field path** for a
container projection (`span.lo.q`: the node its port carries), the head constant for any
other application (`let` bodies descended), the literal for a literal: the granularity
the incidence relation records.

A *carrier's* own projection is not a path: taking a magnitude is the erasure boundary,
reported against the operand it erases, so a registered carrier's field keeps the plain
naming its exit line has always had. -/
partial def refName (ctx : BinderCtx) (e : Expr) : MetaM String := do
  match e with
  | .app f _ =>
    if let .const c _ := e.getAppFn then
      if let some path ← containerField? c then
        let args := e.getAppArgs
        if let some s := args[path.1]? then
          return s!"{← refName ctx s}.{path.2}"
    refName ctx f
  | .mdata _ b => refName ctx b
  -- a constant names itself in full: the same node a config port declares, and a node
  -- identity that the reader's open namespaces must not move
  | .const c _ => return toString c
  | .fvar id => return toString (← id.getDecl).userName
  | .bvar i =>
    match ctx[i]? with
    | some (nm, _) => return toString nm
    | none => return "_"
  | .letE nm _ v b _ => refName ((nm, some v) :: ctx) b
  | .proj sn i b =>
    let env ← getEnv
    if !(operandCarriers env).contains sn then
      if let some f := (getStructureFields env sn)[i]? then
        return s!"{← refName ctx b}.{f}"
    return s!"{← refName ctx b}.{i}"
  | .lit (.natVal v) => return toString v
  | .lit (.strVal s) => return s!"\"{s}\""
  | _ => return "_"
where
  /-- Is `c` a *container* structure's projection function — the structure argument's
  position and the field's name — or `none` for a non-projection and for every
  registered carrier's own field? -/
  containerField? (c : Name) : MetaM (Option (Nat × String)) := do
    let env ← getEnv
    let some pi := env.getProjectionFnInfo? c | return none
    if (operandCarriers env).contains c.getPrefix then return none
    return some (pi.numParams, c.getString!)

/-- The kind reference a kind argument of an instantiated binder type denotes: a kind
declaration by its environment name, a signature kind binder by its binder name (a
telescope free variable, or a loose bound variable under an inner binder), and anything
outside the vocabulary as its rendering — `KindRef.rendered`, compared byte-exact and
refused in contracts. -/
def kindRefOf (ctx : BinderCtx) (e : Expr) : MetaM KindRef := do
  let e := e.consumeMData.consumeTypeAnnotations
  match e with
  | .const c _ => return .decl c
  | .fvar id => return .param (toString (← id.getDecl).userName)
  | .bvar i =>
    match ctx[i]? with
    | some (nm, _) => return .param (toString nm)
    | none => return .rendered "_"
  | _ =>
    if e.hasLooseBVars then return .rendered (← refName ctx e)
    else return .rendered (toString (← Meta.ppExpr e))

/-- The node identifier an operand expression denotes — the reference-typed reading of
`refName`, minting the class each shape belongs to: a telescope free variable is a
signature binder, a bound variable a body-named node (a `let`, a do-bind, a matcher
binder), a container projection a field path on its base, a constant its own address, a
literal or any other application an `unresolved` degradation the graph can report and no
contract may cite. -/
partial def nodeIdOf (ctx : BinderCtx) (e : Expr) : MetaM NodeId := do
  match e with
  | .app f _ =>
    if let .const c _ := e.getAppFn then
      if let some path ← containerField? c then
        let args := e.getAppArgs
        if let some s := args[path.1]? then
          return (← nodeIdOf ctx s).field path.2
    nodeIdOf ctx f
  | .mdata _ b => nodeIdOf ctx b
  | .const c _ => return NodeId.config c
  | .fvar id => return NodeId.binder (toString (← id.getDecl).userName)
  | .bvar i =>
    match ctx[i]? with
    | some (nm, _) => return NodeId.letBound (toString nm)
    | none => return { root := .unresolved "_" }
  | .letE nm _ v b _ => nodeIdOf ((nm, some v) :: ctx) b
  | .proj sn i b =>
    let env ← getEnv
    if !(operandCarriers env).contains sn then
      if let some f := (getStructureFields env sn)[i]? then
        return (← nodeIdOf ctx b).field (toString f)
    return (← nodeIdOf ctx b).field (toString i)
  | .lit (.natVal v) => return { root := .unresolved (toString v) }
  | .lit (.strVal s) => return { root := .unresolved s!"\"{s}\"" }
  | _ => return { root := .unresolved "_" }
where
  /-- `refName.containerField?`, restated: is `c` a *container* structure's projection
  function — the structure argument's position and the field's name? -/
  containerField? (c : Name) : MetaM (Option (Nat × String)) := do
    let env ← getEnv
    let some pi := env.getProjectionFnInfo? c | return none
    if (operandCarriers env).contains c.getPrefix then return none
    return some (pi.numParams, c.getString!)

/-- Render a node identifier — `NodeId.render`, locally named. -/
def renderNode (n : NodeId) : String := n.render

/-- The nominal kind a `@[kindNominal]`-registered designation set designates, or `none`.
A bespoke finite label set states its kind by *being that type* (`BoundaryAudit`, "The
nominal designation registry"), so the head constant is the whole reading — there is no
kind argument to find, and none to get wrong. -/
def nominalKind? (env : Environment) (ty : Expr) : Option Name :=
  match ty.consumeTypeAnnotations.getAppFn with
  | .const c _ => BoundaryAudit.nominalKindOf? env c
  | _ => none

/-- The kind a carrier-headed type states, or `none` if `ty` is not headed by a
registered carrier: the argument(s) whose instantiated binder type is `KindOfProperty`,
rendered. Positional generic — `Quantity k R` and `IndividualQuantity o k R` both
resolve to `k`.

A registered nominal designation set answers here too, at the kind it designates: a
`Polarization` binder is an interface node of the radar-polarization kind exactly as a
`Quantity relPermKind α` binder is one of the permittivity kind. The kind renders from
its constant, so a designation port and a quantity port spell their kinds the same way
and against the same open namespaces. -/
def carrierKind? (env : Environment) (carriers : Array Name) (ctx : BinderCtx)
    (ty : Expr) : MetaM (Option KindRef) := do
  let ty := ty.consumeTypeAnnotations
  let .const c _ := ty.getAppFn | return none
  if let some kn := BoundaryAudit.nominalKindOf? env c then
    return some (.decl kn)
  unless carriers.contains c do return none
  let some ci := env.find? c | return none
  let args := ty.getAppArgs
  let some btys := KindEdges.instantiatedBinderTypes ci.type args | return none
  let kindIdxs := (Array.range args.size).filter fun i =>
    btys[i]!.isConstOf ``KindOfProperty
  if kindIdxs.isEmpty then return none
  let ks ← kindIdxs.mapM fun i => kindRefOf ctx args[i]!
  match ks.toList with
  | [k] => return some k
  | ks => return some (.tuple ks)

/-- The kind signature a function-over-quantities type states, or `none`: a
non-dependent arrow chain whose every domain and result are carrier-kinded reads as
`k₁ → … → k` — an anonymous contract of input kinds and an output kind, the port form
of a functional argument (a **module-valued port**; `Provenance.Contract`, the
`suppliers` clause). The test reduces at reducible transparency first, so a signature
that names an abbreviation says what the abbreviation says — `AttenQ α` is
`Quantity paramB α → Quantity vegetationIndex α → Quantity vegetationAttenuation α`
however the binder spells it. A dependent arrow, or a domain the kind vocabulary does
not cover, is no signature — the position then falls to the kind-bearing verdict, as
any non-portable position does. -/
partial def signatureKind? (env : Environment) (carriers : Array Name)
    (ctx : BinderCtx) (ty : Expr) (acc : Array KindRef := #[]) : MetaM (Option KindRef) := do
  let ty ← Meta.whnfR ty.consumeTypeAnnotations
  match ty with
  | .forallE _ dom body _ =>
    if body.hasLooseBVars then return none
    let some k ← carrierKind? env carriers ctx dom | return none
    signatureKind? env carriers ctx body (acc.push k)
  | _ =>
    if acc.isEmpty then return none
    let some k ← carrierKind? env carriers ctx ty | return none
    return some (.sig (acc.push k).toList)

/-- The kind signature a *supplier* declaration states: its leading implicit and
instance binders — the carrier and its instances — filled with metavariables, the
remaining explicit spine read exactly as the harvest reads a functional binder
(`signatureKind?`). `none` where that spine is not a function over carrier-kinded
values. -/
partial def supplierSignature? (env : Environment) (carriers : Array Name)
    (ty : Expr) : MetaM (Option KindRef) := do
  let ty ← Meta.whnfR ty
  match ty with
  | .forallE _ dom body bi =>
    if bi.isExplicit then
      signatureKind? env carriers [] ty
    else
      supplierSignature? env carriers (body.instantiate1 (← Meta.mkFreshExprMVar dom))
  | _ => return none

/-- **The carrier field paths of a container type** — the ports a record-carried
quantity contributes. A type that is not itself carrier-headed but is a
single-constructor structure states its kinds through its fields: an `IccQ k R` states
`k` twice, at `.lo.q` and `.hi.q`; a pair of quantities states one kind per component.
Each carrier-headed field (recursively, through nested single-constructor structures,
fuel-bounded) yields one `(path, kind)` — the path appended to the binder or result
name, so the port node reads exactly as the body spells the projection
(`refName`, "a field path for a container projection") and the two readings meet at the
same node.

A sum type has no field path — its payload is not there in every case — and gets
`conditionalPaths` instead; a carrier is a leaf, never a container: its own field is the
erasure boundary. -/
partial def carrierPaths (env : Environment) (carriers : Array Name) (ctx : BinderCtx)
    (ty : Expr) (fuel : Nat := 3) : MetaM (Array (List String × KindRef)) := do
  let ty := ty.consumeTypeAnnotations
  if ty.hasLooseBVars then return #[]
  if (← carrierKind? env carriers ctx ty).isSome then return #[]
  match fuel, ty.getAppFn with
  | fuel + 1, .const c _ =>
    unless isStructure env c do return #[]
    let some (.inductInfo ii) := env.find? c | return #[]
    unless ii.ctors.length == 1 do return #[]
    let x ← Meta.mkFreshExprMVar ty
    let mut out : Array (List String × KindRef) := #[]
    for f in getStructureFields env c do
      let some fty ← (try pure (some (← Meta.inferType (← Meta.mkProjection x f)))
                      catch _ => pure none) | continue
      match ← carrierKind? env carriers ctx fty with
      | some k => out := out.push ([toString f], k)
      | none =>
        for (p, k) in ← carrierPaths env carriers ctx fty fuel do
          out := out.push (toString f :: p, k)
    return out
  | _, _ => return #[]

/-- **The conditional paths of a sum type** — the ports a result produced only in some
cases contributes. A multi-constructor inductive states its kinds through the payloads of
its cases, and each carrier-bearing payload yields one `(path, kind)` addressed by the
*case*: `Option (Quantity k R)` states `k` once, at `.some`, and a case carrying several
quantities states one path per field beneath its own (`.ok.lo.q`), the same rule
`carrierPaths` follows one level up — no path component where there is nothing to
disambiguate.

The case is in the address because the case is the claim: a value at `result.some` is the
one the interface produces when it produces one, and the port that carries it is
`conditional`, so a validity domain is stated at the boundary instead of living in a
constructor nobody downstream can see. A case with no quantity in it — `none`, an error
string — contributes nothing, which is exactly right: there is no measurement there. -/
def conditionalPaths (env : Environment) (carriers : Array Name) (ctx : BinderCtx)
    (ty : Expr) : MetaM (Array (List String × KindRef)) := do
  let ty := ty.consumeTypeAnnotations
  if ty.hasLooseBVars then return #[]
  if (← carrierKind? env carriers ctx ty).isSome then return #[]
  let .const c us := ty.getAppFn | return #[]
  let some (.inductInfo ii) := env.find? c | return #[]
  if ii.ctors.length ≤ 1 then return #[]
  let params := ty.getAppArgs.extract 0 ii.numParams
  if params.size != ii.numParams then return #[]
  let mut out : Array (List String × KindRef) := #[]
  for ctor in ii.ctors do
    let case := ctor.getString!
    -- the constructor's fields at *this* instance: a case's payload is a quantity
    -- only once the inductive's parameters are the ones the result states
    let ctorTy ← Meta.instantiateForall (← Meta.inferType (mkConst ctor us)) params
    let payload ← Meta.forallTelescope ctorTy fun fvars _ => do
      let mut slots : Array (List String × KindRef) := #[]
      for fv in fvars do
        let fty ← Meta.inferType fv
        let nm := toString (← fv.fvarId!.getUserName)
        match ← carrierKind? env carriers ctx fty with
        | some k => slots := slots.push ([nm], k)
        | none =>
          for (p, k) in ← carrierPaths env carriers ctx fty do
            slots := slots.push (nm :: p, k)
      return slots
    match payload with
    | #[(_, k)] => out := out.push ([case], k)
    | ps => for (p, k) in ps do out := out.push (case :: p, k)
  return out

/-- Does a type carry kind information at all — a registered carrier or the kind
vocabulary itself, mentioned anywhere in the expression, or (fuel-bounded) in the
fields of the single-constructor inductive at its head, or in one of its own type
arguments? The negative answer classifies a signature position as *unkinded* (module
header, "Unkinded positions"): naked data, red in every report. The positive answer
without a carrier field path (`carrierPaths`) or a kind signature (`signatureKind?` —
a function over quantities ports at its arrow of kinds, the module-valued port) is a
kind-bearing position that ports nothing — a sum over quantities, a dependent or
partially-kinded function: not naked data, and not an interface node either.

Three ways a type says it, because an abbreviation and a plural are not naked data:

  * the test reduces at **reducible** transparency first, so a signature that names an
    abbreviation says what the abbreviation says — `AttenQ α`, spelled
    `Quantity paramB α → Quantity vegetationIndex α → Quantity vegetationAttenuation α`,
    is a function over quantities however the binder spells it;
  * a single-constructor head states its kinds through its fields, one level at a time;
  * **a container of kinded values is kinded** — a type argument is searched like the
    type itself, so `List (ObsWQ α)` carries what an `ObsWQ α` carries. It ports
    nothing (a list has no fixed arity, so there is no field path to name), which is
    exactly the "carries kinds, is not an interface node" verdict — the plural of a
    kinded thing is not naked data, and calling it naked over-reports the debt. -/
partial def kindBearing (carriers : Array Name) (ty : Expr) (fuel : Nat := 3) :
    MetaM Bool := do
  let ty ← Meta.whnfR ty.consumeTypeAnnotations
  let mentions := (ty.find? fun sub =>
    match sub with
    | .const c _ => carriers.contains c || c == ``KindOfProperty
    | _ => false).isSome
  if mentions then return true
  match fuel with
  | 0 => return false
  | fuel + 1 =>
    if let .const c _ := ty.getAppFn then
      if (BoundaryAudit.nominalKindOf? (← getEnv) c).isSome then return true
      if let some (.inductInfo ii) := (← getEnv).find? c then
        if ii.ctors.length == 1 then
          if let some ctor := ii.ctors.head?.bind (← getEnv).find? then
            if ← kindBearing carriers ctor.type fuel then return true
    for a in ty.getAppArgs do
      unless a.hasLooseBVars do
        if (← Meta.isType a) then
          if ← kindBearing carriers a fuel then return true
    return false

/-- The result type's right-spine product components — `A × B × C` is three output
positions. A parenthesized left factor stays one component: positions follow what the
signature spells. -/
partial def prodComponents (ty : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if ty.isAppOfArity ``Prod 2 then
    let args := ty.getAppArgs
    prodComponents args[1]! (acc.push args[0]!)
  else
    acc.push ty

/-- The value-side view of the result tuple: the right-spine `Prod.mk` components when
the body is a literal spine of the expected width — the per-component attribution
behind the output-flow reading — and `none` when the body computes its tuple another
way (a branch, a call), where attribution falls back to every kinded output. -/
partial def prodValueComps (e : Expr) (n : Nat) (acc : Array Expr := #[]) :
    Option (Array Expr) :=
  match e with
  | .mdata _ b => prodValueComps b n acc
  | _ =>
    if acc.size + 1 == n then some (acc.push e)
    else if e.isAppOfArity ``Prod.mk 4 then
      prodValueComps e.getAppArgs[3]! n (acc.push e.getAppArgs[2]!)
    else none

/-- The `@[kindConst]` constants `e` references, in body order, deduplicated — a port is
an interface node, so a constant read twice is one port (the occurrence reading keeps
the two incidence positions).

`dissected` is the assembly's member set. **A member's call site is an edge, not a
port**: the head of an application the walk reads as a procedure edge is not a
configuration read, however the callee is tagged — its result comes off the edge, and
declaring a port for it too would leave an orphan on the boundary that the deploying
contract has to state. The call's *arguments* are read as usual, which is where a
deployment's constants actually enter. -/
partial def configReads (consts : NameSet) (dissected : NameSet) (e : Expr)
    (acc : Array Name := #[]) : Array Name :=
  match e with
  | .const n _ =>
    if consts.contains n && !acc.contains n then acc.push n else acc
  | .app .. =>
    let f := e.getAppFn
    let headDissected := match f with
      | .const n _ => dissected.contains n
      | _ => false
    let acc := if headDissected then acc else configReads consts dissected f acc
    e.getAppArgs.foldl (fun acc a => configReads consts dissected a acc) acc
  | .lam _ t b _ | .forallE _ t b _ =>
    configReads consts dissected b (configReads consts dissected t acc)
  | .letE _ t v b _ =>
    configReads consts dissected b
      (configReads consts dissected v (configReads consts dissected t acc))
  | .mdata _ b | .proj _ _ b => configReads consts dissected b acc
  | _ => acc

/-! ## Reading an edge off a binder type -/

/-- A rational literal's value, read off its elaborated spelling (`1 / 2`, `-1`, `3`).
`none` for anything else — a parametric exponent has no `Rat` to carry as edge data. -/
partial def ratOfExpr? (e : Expr) : Option Rat :=
  let e := e.cleanupAnnotations
  if let some n := e.rawNatLit? then some (mkRat (Int.ofNat n) 1)
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    (e.getAppArgs[1]!).rawNatLit?.map fun n => mkRat (Int.ofNat n) 1
  else if e.isAppOfArity ``Neg.neg 3 then
    (ratOfExpr? e.getAppArgs[2]!).map fun q => -q
  else if e.isAppOfArity ``HDiv.hDiv 6 then do
    let a ← ratOfExpr? e.getAppArgs[4]!
    let b ← ratOfExpr? e.getAppArgs[5]!
    pure (a / b)
  else none

/-- The edge a binder type states — its `EdgeFamily` label, operand-kind expressions,
and result-kind expression — or `none` for a non-edge binder. A `PowerKind` whose
exponent is not a rational literal throws: the edge vocabulary carries a `Rat` exponent,
and a kind-generic power step monomorphizes at its discharging call sites. -/
def edgeOfBinderType? (ty : Expr) :
    MetaM (Option (EdgeFamily × Array Expr × Expr)) := do
  let ty := ty.cleanupAnnotations
  let a := ty.getAppArgs
  if ty.isAppOfArity ``ProductKind 3 then return some (.product, #[a[0]!, a[1]!], a[2]!)
  if ty.isAppOfArity ``QuotientKind 3 then return some (.quotient, #[a[0]!, a[1]!], a[2]!)
  if ty.isAppOfArity ``ReciprocalKind 2 then return some (.reciprocal, #[a[0]!], a[1]!)
  if ty.isAppOfArity ``TranscendentalKind 2 then
    return some (.transcendental, #[a[0]!], a[1]!)
  -- a re-expression relates the value converted; the two reference quantities are the
  -- edge's configuration, and a signature that states them is stating its conversion,
  -- not taking two more inputs
  if ty.isAppOfArity ``ReferenceKind 2 then return some (.reference, #[a[0]!], a[1]!)
  -- a same-kind sum or difference: the witness names one kind, and that one kind is both
  -- operands and the result — the shared index is the whole of the claim
  if ty.isAppOfArity ``DifferenceKind 1 then
    return some (.additive, #[a[0]!, a[0]!], a[0]!)
  if ty.isAppOfArity ``PowerKind 3 then
    let some p := ratOfExpr? a[0]!
      | throwError "a power exponent here is not a rational literal — the graph's edge \
          vocabulary carries a `Rat` exponent, so a kind-generic power step is read at \
          the call sites that discharge it"
    return some (.power p, #[a[1]!], a[2]!)
  if ty.isAppOfArity ``KindMul 3 then return some (.tableMul, #[a[0]!, a[1]!], a[2]!)
  if ty.isAppOfArity ``KindDiv 3 then return some (.tableDiv, #[a[0]!, a[1]!], a[2]!)
  return none

/-- The table subset of `edgeOfBinderType?` — what one level of instance unfolding is
allowed to find inside an instance argument's own telescope. -/
def tableEdgeOfType? (ty : Expr) : Option (EdgeFamily × Array Expr × Expr) :=
  let ty := ty.cleanupAnnotations
  let a := ty.getAppArgs
  if ty.isAppOfArity ``KindMul 3 then some (.tableMul, #[a[0]!, a[1]!], a[2]!)
  else if ty.isAppOfArity ``KindDiv 3 then some (.tableDiv, #[a[0]!, a[1]!], a[2]!)
  else none

/-- Does a binder type state any edge — witness family or table class? The pure
pre-check behind producer classification. -/
def statesEdgeType (ty : Expr) : Bool :=
  let ty := ty.cleanupAnnotations
  ty.isAppOfArity ``ProductKind 3 || ty.isAppOfArity ``QuotientKind 3
    || ty.isAppOfArity ``ReciprocalKind 2 || ty.isAppOfArity ``TranscendentalKind 2
    || ty.isAppOfArity ``PowerKind 3 || ty.isAppOfArity ``ReferenceKind 2
    || ty.isAppOfArity ``DifferenceKind 1
    || ty.isAppOfArity ``KindMul 3 || ty.isAppOfArity ``KindDiv 3

/-! ## The walk — occurrences, introductions, exits, wiring -/

/-- One harvested occurrence: the graph occurrence plus the two markers the graph value
does not carry. `assumed` — the license is a hypothesis or instance *binder* of the
step's own interface: the occurrence wires this step's graph but is excluded from the
enumeration (the authored occurrence sits at the discharging caller).
`partialIncidence` — the consuming signature exposes fewer carrier operands than the
family relates: a sub-step boundary, excluded from the wiring, so the verdict refuses
what one step's body cannot exhibit. -/
structure StepOccurrence where
  /-- The occurrence, in the graph's vocabulary. -/
  occ : Occurrence NodeId KindRef
  /-- The full operand-kind list the license states — the edge's own equation, which a
  partial incidence does not truncate (the operand list is what the site exposes). -/
  edgeKinds : Array KindRef
  /-- License discharged from the step's own hypothesis or instance binder. -/
  assumed : Bool
  /-- Fewer operands exposed than the family relates — a sub-step boundary. -/
  partialIncidence : Bool
deriving Inhabited

/-- `alphaK · betaK → gammaK ⟨x, y⟩` — the edge with its incidence, in the enumeration
grammar (`EdgeFamily.render` over the kinds the license states). -/
def StepOccurrence.render (o : StepOccurrence) : String :=
  let names := o.occ.operands.map (renderNode ·.1)
  s!"{o.occ.family.render (o.edgeKinds.toList.map (·.render)) o.occ.resultKind.render} \
    ⟨{String.intercalate ", " names}⟩"

/-- The graph rendering of an occurrence: the enumeration line, the result node it
wires, and its marker if any. -/
def StepOccurrence.renderWired (o : StepOccurrence) : String :=
  let marker :=
    if o.partialIncidence then " (partial)" else if o.assumed then " (assumed)" else ""
  s!"{o.render} ⇒ {renderNode o.occ.result}{marker}"

/-- The registries and attribution the walk carries: the audit's carrier, boundary, and
attestor registries, the occurrence site, whether the harvested declaration is itself a
`@[kindConst]` mint (its value then wires through a declared source) or a
`@[kindEmission]` shell (its carrier-constructor mints are the sanctioned grid↔kernel
boundary, wired through `attested "[kindEmission]"` sources), and the assembly set —
the declarations an assembly reads as sub-step procedure edges rather than opaque
calls. -/
structure HarvestCtx where
  env : Environment
  carriers : Array Name
  carrierSpecs : Array BoundaryAudit.CarrierSpec
  configConsts : NameSet
  ingestConsts : NameSet
  attestors : Array BoundaryAudit.AttestSpec
  site : String
  declKindConst : Bool
  declEmission : Bool := false
  subSteps : Array Name := #[]
  /-- The declaration's unkinded explicit arguments as the value walk sees them — the
  lambda binders at the gap-kept positions, each with its rendered name — so a minting
  application can be checked for the unkinded information it consumes (module header,
  "Unkinded positions"). -/
  unkindedFVars : Array (FVarId × String) := #[]

/-- The walk's accumulator: occurrences, introduction events, exits, the counter
behind synthesized interior nodes (`_1`, `_2`, … in walk order), and the unkinded
flows — each an unkinded argument reaching a kinded node outside the kinded
algebra. -/
structure WalkSt where
  occs : Array StepOccurrence := #[]
  intros : Array (Intro NodeId KindRef) := #[]
  exits : Array NodeId := #[]
  freshCount : Nat := 0
  leaks : Array (String × NodeId) := #[]
  /-- The body's flat kind-bearing name namespace — every `let`, do-bind, or matcher
  binder that minted a node. A second kind-bearing binding at a name already here is
  refused: one flat namespace, or a contract naming it would name two things. -/
  bodyNames : Array String := #[]

/-- The next synthesized interior node. -/
def WalkSt.nextFresh (st : WalkSt) : NodeId × WalkSt :=
  let n := st.freshCount + 1
  ({ root := .fresh n }, { st with freshCount := n })

/-- Record an exit, once per node. -/
def WalkSt.exit (st : WalkSt) (n : NodeId) : WalkSt :=
  if st.exits.contains n then st else { st with exits := st.exits.push n }

/-- Record an unkinded flow, once per (source, target) pair. -/
def WalkSt.leak (st : WalkSt) (src : String) (dst : NodeId) : WalkSt :=
  if st.leaks.contains (src, dst) then st
  else { st with leaks := st.leaks.push (src, dst) }

/-- Wire `node` from the named `src` by the identity `copy`, introducing `node` as
`derived` when the walk owns its introduction (a `let` binder or synthesized node —
never a port). -/
def WalkSt.copyTo (st : WalkSt) (site : String) (src node : NodeId) (kind : KindRef)
    (owned : Bool) : WalkSt :=
  let st := if owned then { st with intros := st.intros.push ⟨node, kind, .derived⟩ }
            else st
  let so : StepOccurrence :=
    ⟨⟨.copy, [(src, kind)], node, kind, site, .anonymous⟩, #[kind], false, false⟩
  { st with occs := st.occs.push so }

/-- A value's assignment target: the node its producer lands on. -/
inductive Target where
  /-- Produce onto this node; `owned` says the walk owns its introduction event (a
  `let` binder or synthesized interior node — never a port). -/
  | one (node : NodeId) (kind : KindRef) (owned : Bool)
  /-- The root of a multi-output producer: one slot per component — empty for an
  un-kinded one, one entry for a carrier-typed one, and one entry *per carrier field
  path* for a container-typed one (`carrierPaths`) — each entry a node, its kind, and
  whether the walk owns its introduction (an output port's slot is not owned; a matcher
  binder's is). -/
  | tuple (comps : List (List (NodeId × KindRef × Bool)))

/-- The single-node view of an optional target. -/
def Target.asOne? : Option Target → Option (NodeId × KindRef × Bool)
  | some (.one n k o) => some (n, k, o)
  | _ => none

/-- The target a slot group assigns to the value that fills it: nothing where the group
is empty (an un-kinded position), the node itself where the group is one, and a
one-component `tuple` where it is several — a container's carrier field paths, which the
value side splits at the constructor that assembles them (`ctorFieldSlots`). -/
def Target.ofSlots : List (NodeId × KindRef × Bool) → Option Target
  | [] => none
  | [(n, k, o)] => some (.one n k o)
  | ss => some (.tuple [ss])

/-- Introduce a *source* (an attested or gated mint) at the target: directly on a node
the walk owns, or through a synthesized source node wired to a port by `copy`. With no
target the source is still recorded — a mint is a mint wherever it sits. Returns the
source node introduced, so the minting site can attribute its unkinded flows to it. -/
def sourceAt (h : HarvestCtx) (tier : IntroTier) (kind : KindRef)
    (t1 : Option (NodeId × KindRef × Bool)) (st : WalkSt) : NodeId × WalkSt :=
  match t1 with
  | some (n, k, true) => (n, { st with intros := st.intros.push ⟨n, k, tier⟩ })
  | some (n, k, false) =>
    let (m, st) := st.nextFresh
    let st := { st with intros := st.intros.push ⟨m, k, tier⟩ }
    let so : StepOccurrence :=
      ⟨⟨.copy, [(m, k)], n, k, h.site, .anonymous⟩, #[k], false, false⟩
    (m, { st with occs := st.occs.push so })
  | none =>
    let (m, st) := st.nextFresh
    (m, { st with intros := st.intros.push ⟨m, kind, tier⟩ })

/-- The unkinded flows into a mint: each unkinded argument occurring in the minting
application flows into the mint's node — unkinded information minting kinded
information, the reading the red arrows draw (module header, "Unkinded
positions"). -/
def mintLeaks (h : HarvestCtx) (e : Expr) (node : NodeId) (st : WalkSt) : WalkSt :=
  h.unkindedFVars.foldl (init := st) fun st (fv, nm) =>
    if e.containsFVar fv then st.leak nm node else st

/-- The body with every minting application replaced by a closed marker: what remains
is the logic the kinded algebra never licensed, so an unkinded argument surviving the
mask into a kinded output's defining expression steers that output from outside the
algebra. (The replacement is type-incorrect and never elaborated — it exists only for
the free-variable containment check.) -/
def maskMints (h : HarvestCtx) (e : Expr) : Expr :=
  e.replace fun sub =>
    match sub.getAppFn with
    | .const c _ =>
      if (h.attestors.any fun s => s.declName == c && sub.getAppNumArgs == s.arity)
          || h.ingestConsts.contains c
          || (h.declEmission && h.carrierSpecs.any fun s =>
                s.ctorName == c && sub.getAppNumArgs == s.ctorArity) then
        some (mkConst ``Unit)
      else none
    | _ => none

/-- No reading produced the target. A `let` binder the walk owns is still introduced
(`derived`, with nothing deriving it — the verdict then refuses, which is the point: an
unproduced derivation target is an anonymous mint). A port of a `@[kindConst]`
declaration is the sanctioned exception: its value is the declared constant mint, wired
through an `attested "[kindConst]"` source. -/
def opaqueTarget (h : HarvestCtx) (t1 : Option (NodeId × KindRef × Bool))
    (st : WalkSt) : WalkSt :=
  match t1 with
  | some (n, k, true) => { st with intros := st.intros.push ⟨n, k, .derived⟩ }
  | some (n, k, false) =>
    if h.declKindConst then
      let (m, st) := st.nextFresh
      let st := { st with intros := st.intros.push ⟨m, k, .attested "[kindConst]"⟩ }
      let so : StepOccurrence :=
        ⟨⟨.copy, [(m, k)], n, k, h.site, .anonymous⟩, #[k], false, false⟩
      { st with occs := st.occs.push so }
    else st
  | none => st

/-- The rendered name of a step declaration — its last component, which labels a level
in reports and figures. Purely a display form: node and edge identity carry the full
declaration name. Members whose last components collide are refused at assembly, so the
*renderings* stay unambiguous too. -/
def stepNameOf (ci : ConstantInfo) : MetaM String :=
  return lastComponent ci.name

/-- One edge stated by a consuming application's binders, kinds as references. -/
structure BinderEdge where
  family : EdgeFamily
  opKinds : Array KindRef
  resKind : KindRef
  assumed : Bool

/-- Every edge a constant-headed application's instantiated binder types state —
directly (witness `Prop`s and table classes), or one instance-unfold away: a
constant-headed instance argument's own telescope is searched for `KindMul`/`KindDiv`
positions, with authoredness judged on the argument filling that position (a registered
instance is authored; a threaded instance binder is assumed). -/
def binderEdges (h : HarvestCtx) (ctx : BinderCtx) (args : Array Expr)
    (btys : Array Expr) : MetaM (Array BinderEdge) := do
  let mut edges : Array BinderEdge := #[]
  for i in [0:args.size] do
    if let some (fam, opTys, resTy) ← edgeOfBinderType? btys[i]! then
      let opKinds ← opTys.mapM (kindRefOf ctx)
      let resKind ← kindRefOf ctx resTy
      edges := edges.push
        { family := fam, opKinds, resKind, assumed := !witnessAuthored ctx args[i]! }
    else if let .const ic _ := args[i]!.getAppFn then
      if let some ii := h.env.find? ic then
        let uargs := args[i]!.getAppArgs
        if let some ubtys := KindEdges.instantiatedBinderTypes ii.type uargs then
          for u in [0:uargs.size] do
            if let some (fam, opTys, resTy) := tableEdgeOfType? ubtys[u]! then
              let opKinds ← opTys.mapM (kindRefOf ctx)
              let resKind ← kindRefOf ctx resTy
              edges := edges.push
                { family := fam, opKinds, resKind,
                  assumed := !witnessAuthored ctx uargs[u]! }
  return edges

/-- Would this expression, as an operand, produce a node of its own — an attestor
application, a gated ingest, an emission-shell mint, a sub-step application, or a
consuming application (an edge stated directly or one instance-unfold away)? Such an
operand is walked onto a synthesized node so the outer occurrence and the inner
producer name the same thing. -/
def isProducerApp (h : HarvestCtx) (a : Expr) : Bool :=
  if a.isAppOfArity ``HAdd.hAdd 6 || a.isAppOfArity ``HSub.hSub 6 then true else
  match a.getAppFn with
  | .const c _ =>
    (h.attestors.any fun s => s.declName == c && a.getAppNumArgs == s.arity)
      || h.ingestConsts.contains c
      || (h.subSteps.contains c && a.getAppNumArgs > 0)
      || (h.declEmission && h.carrierSpecs.any fun s =>
            s.ctorName == c && a.getAppNumArgs == s.ctorArity)
      || (match h.env.find? c with
          | some ci =>
            match KindEdges.instantiatedBinderTypes ci.type a.getAppArgs with
            | some btys =>
              btys.any statesEdgeType
                || a.getAppArgs.any fun ia =>
                    match ia.getAppFn with
                    | .const ic _ =>
                      match h.env.find? ic with
                      | some ii =>
                        match KindEdges.instantiatedBinderTypes ii.type ia.getAppArgs with
                        | some ubtys => ubtys.any fun u => (tableEdgeOfType? u).isSome
                        | none => false
                      | none => false
                    | _ => false
            | none => false
          | none => false)
  | _ => false

/-- Is `e` a **field path** — one or more container projections rooted at a variable
(`span.lo.q`)? Such an expression names an interface node (`carrierPaths` ported it),
so it reaches a target the way a binder does: through the identity wire. A *carrier's*
projection is excluded — that is the erasure boundary, read as an exit. -/
partial def containerPath (env : Environment) (carriers : Array Name) (e : Expr)
    (depth : Nat := 0) : Bool :=
  match e with
  | .mdata _ b => containerPath env carriers b depth
  | .fvar .. | .bvar .. => depth > 0
  | .proj sn _ b => !carriers.contains sn && containerPath env carriers b (depth + 1)
  | .app .. =>
    match e.getAppFn with
    | .const c _ =>
      match env.getProjectionFnInfo? c with
      | some pi =>
        !carriers.contains c.getPrefix &&
          (match e.getAppArgs[pi.numParams]? with
           | some s => containerPath env carriers s (depth + 1)
           | none => false)
      | none => false
    | _ => false
  | _ => false

/-- Does this operand expression **name an interface node the graph already has** — a
binder, a `let`-bound name, a container field path rooted at one, a declared constant, a
structure projection — or does it only name the *function* that computed it?

`refName` answers the first cases faithfully and answers an application by walking it
down to its head constant, which names a **declaration, not a node**. An occurrence
citing such a name refers to a node no introduction ever made: `kindOf?` returns none,
`occurrencesTyped` refuses, and the whole level falls to interface mode for a reason with
nothing metrological in it. So operand naming and operand declaration must agree — an
operand that names no node is given one of its own, and the walk produces onto it.

A `@[kindConst]` read is the case that already agreed by construction: its call names the
configuration port the constant declares, which is a node. -/
def namesNode (h : HarvestCtx) (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ | .bvar _ | .letE .. | .const .. | .proj .. | .lit _ => true
  | .app .. =>
    containerPath h.env h.carriers e
      || (match e.getAppFn with
          | .const c _ => h.configConsts.contains c
          | _ => false)
  | _ => false

/-- The node an erasure victim denotes, or a refusal. An erased value the graph cannot
name — an inline compound, a literal — used to degrade the exit to a rendering of
whatever expression stood there, an exit no contract could truthfully cite; the boundary
is the one place degradation must not pass, so the harvest refuses instead: let-bind the
value you erase, and the exit names that node. -/
def exitVictim (h : HarvestCtx) (ctx : BinderCtx) (e : Expr) : MetaM NodeId := do
  let id ← nodeIdOf ctx e
  let nameable := namesNode h e &&
    (match id.root with | .unresolved _ => false | _ => true)
  unless nameable do
    throwError "a value erased in '{h.site}' is a compound the graph cannot name — \
      let-bind the value you erase, so the exit names a node of the boundary"
  return id

/-- **The literal container assembly** — a single-constructor structure application read
as its field arguments, each paired with the slot sub-group its own carrier paths name.
Packaging is transparent to dataflow: a step that bundles what it computed lands its
components on the very nodes the bundle's ports name, so re-typing a result from a naked
tuple to the record that names its components moves no wire (`Prod.mk` is this same
reading at the anonymous constructor, and it is where the reading came from).

The grouping re-runs the enumeration that built the slots — one entry for a carrier-typed
field, its path count for a container-typed one, in constructor order, which is
`carrierPaths`'s own loop — and returns `none` when the two disagree, so any drift
degrades to the opaque reading instead of misattributing a component. `none` too when the
value is not such an application, and when its head is a **registered carrier**: a carrier
is a leaf, never a container, and its constructor is a mint, not packaging. -/
def ctorFieldSlots (h : HarvestCtx) (ctx : BinderCtx) (e : Expr)
    (slots : List (NodeId × KindRef × Bool)) :
    MetaM (Option (Array (Expr × List (NodeId × KindRef × Bool)))) := do
  let .const c _ := e.getAppFn | return none
  let some (.ctorInfo ci) := h.env.find? c | return none
  if h.carriers.contains ci.induct then return none
  unless isStructure h.env ci.induct do return none
  let args := e.getAppArgs
  unless args.size == ci.numParams + ci.numFields do return none
  -- the field types come off the *constructor*, instantiated at this application's
  -- parameters — not off the field values. A value the walk is carrying may be an open
  -- binder with no type to read, and a container assembled from `let`-bound components is
  -- the ordinary case, not the exception.
  let some btys := KindEdges.instantiatedBinderTypes ci.type args | return none
  let mut rest := slots
  let mut out : Array (Expr × List (NodeId × KindRef × Bool)) := #[]
  for j in [ci.numParams:args.size] do
    let f := args[j]!
    let fty := btys[j]!
    let width ← match ← carrierKind? h.env h.carriers ctx fty with
      | some _ => pure 1
      | none => pure (← carrierPaths h.env h.carriers ctx fty).size
    if rest.length < width then return none
    out := out.push (f, rest.take width)
    rest := rest.drop width
  if !rest.isEmpty then return none
  return some out

/-- The target a binder of type `t` assigns to its producer: the binder's own node when
the type is a carrier, and one node **per carrier field path** when it is a container —
`u.q`, `span.lo.q` — so a producer that returns a bundled value lands on the same nodes
the consumer's ports name. Without the container case a bundled result would leave its
producer targetless, and a step that merely re-bundles what it computed would read as
having computed nothing: the same gap container ports, container operands and container
configuration constants each closed at their own position, here at a binding. `none`
when the type is neither. -/
def bindingTarget (h : HarvestCtx) (ctx : BinderCtx) (nm : String) (t : Expr) :
    MetaM (Option Target) := do
  match ← carrierKind? h.env h.carriers ctx t with
  | some k => return some (.one (NodeId.letBound nm) k true)
  | none =>
    let paths ← carrierPaths h.env h.carriers ctx t
    if paths.isEmpty then return none
    return some (.tuple [paths.toList.map fun (p, k) =>
      ({ NodeId.letBound nm with path := p }, k, true)])

/-- Admit one body name into the flat kind-bearing namespace, or refuse: the name must
be accessible — a machine-generated binder is nobody's interface — and not already
minted by another kind-bearing `let`, do-bind, or matcher binder, across match arms
included, because one flat namespace is what lets a contract's `letBound` reference name
exactly one node (`Provenance.lean`, "The reference vocabulary"). -/
def registerBodyName (st : WalkSt) (site : String) (nm : Name) : MetaM WalkSt := do
  if nm.hasMacroScopes || nm.isAnonymous then
    throwError "a kind-bearing binding in '{site}' has no accessible name — name it, \
      so a boundary can refer to what it binds"
  let s := toString nm
  if st.bodyNames.contains s then
    throwError "two kind-bearing bindings in '{site}' are named '{s}' — one flat \
      namespace cannot hold both; rename one"
  return { st with bodyNames := st.bodyNames.push s }

mutual

/-- The value walk: every subexpression visited in body order (a `let` value before its
consumers, an outer consuming application before its operand producers), each producer
landing on the node its position assigns. -/
partial def walk (h : HarvestCtx) (e : Expr) (ctx : BinderCtx)
    (target : Option Target) (st : WalkSt) : MetaM WalkSt := do
  match e with
  | .mdata _ b => walk h b ctx target st
  | .letE nm t v b _ =>
    let st ← walk h t ctx none st
    let bt ← bindingTarget h ctx (toString nm) t
    let st ← if bt.isSome then registerBodyName st h.site nm else pure st
    let st ← walk h v ctx bt st
    walk h b ((nm, some v) :: ctx) target st
  | .lam nm t b _ =>
    let st ← walk h t ctx none st
    walk h b ((nm, none) :: ctx) none st
  | .forallE nm t b _ =>
    let st ← walk h t ctx none st
    walk h b ((nm, none) :: ctx) none st
  | .proj sn _ b =>
    if containerPath h.env h.carriers e then
      match Target.asOne? target with
      | some (n, k, owned) => return st.copyTo h.site (← nodeIdOf ctx e) n k owned
      | none => return st
    let st := opaqueTarget h (Target.asOne? target) st
    let st ← if h.carrierSpecs.any (·.structName == sn) then
        pure (st.exit (← exitVictim h ctx b))
      else pure st
    walk h b ctx none st
  | .fvar .. | .bvar .. =>
    match Target.asOne? target with
    | some (n, k, owned) => return st.copyTo h.site (← nodeIdOf ctx e) n k owned
    | none => return st
  | _ =>
    -- a multi-output root: split a literal tuple onto its component slots
    if let some (.tuple comps) := target then
      if e.isAppOfArity ``Prod.mk 4 then
        let args := e.getAppArgs
        let st ← walk h args[0]! ctx none st
        let st ← walk h args[1]! ctx none st
        -- a component's own slot group assigns its target: one node where the component
        -- is carrier-typed, and the group itself where it is a container the component
        -- expression assembles (`Target.ofSlots`)
        match comps with
        | c :: rest =>
          let st ← walk h args[2]! ctx (Target.ofSlots c) st
          let restT : Option Target := match rest with
            | [c'] => Target.ofSlots c'
            | _ => some (.tuple rest)
          walk h args[3]! ctx restT st
        | [] => walk h args[3]! ctx none st
      else
        -- a literal container assembly: the constructor is packaging, transparent to
        -- dataflow, so each field lands on the slots its own path names
        let fields? ← match comps with
          | [ss] => ctorFieldSlots h ctx e ss
          | _ => pure none
        match fields? with
        | some fields =>
          let mut st := st
          for (f, ss) in fields do
            st ← walk h f ctx (Target.ofSlots ss) st
          return st
        | none =>
          match e.getAppFn with
          | .const c _ =>
            -- a multi-output sub-step call: one procedure edge per kinded slot
            if h.subSteps.contains c && e.isApp then
              walkSubStep h c e ctx (.inr comps) st
            else
              -- an opaque multi-output producer: the outputs stay unwired
              walkApp h e ctx none st
          | _ => walkApp h e ctx none st
    else if containerPath h.env h.carriers e then
      -- a container field: its port node reaches the target through the identity wire
      match Target.asOne? target with
      | some (n, k, owned) => return st.copyTo h.site (← nodeIdOf ctx e) n k owned
      | none => return st
    else
      walkApp h e ctx (Target.asOne? target) st

/-- The application readings, in order: do-elaboration transparency, attested mint,
gated ingest, emission-shell mint, sub-step procedure edge, erasure, consuming
application, tuple destructuring, configuration read, opaque. -/
partial def walkApp (h : HarvestCtx) (e : Expr) (ctx : BinderCtx)
    (t1 : Option (NodeId × KindRef × Bool)) (st : WalkSt) : MetaM WalkSt := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- the do-elaboration's administrative heads are transparent to dataflow: reading
  -- through them lets a straight-line monadic body wire exactly like its pure
  -- spelling (loops and multi-alternative control flow stay opaque)
  if e.isAppOfArity ``Id.run 2 then
    return ← walk h args[1]! ctx (t1.map fun (n, k, o) => .one n k o) st
  if e.isAppOfArity ``Pure.pure 4 then
    return ← walk h args[3]! ctx (t1.map fun (n, k, o) => .one n k o) st
  if e.isAppOfArity ``Bind.bind 6 then
    match args[5]! with
    | .lam nm t b _ =>
      let st ← walk h t ctx none st
      let bt ← bindingTarget h ctx (toString nm) t
      let st ← if bt.isSome then registerBodyName st h.site nm else pure st
      let st ← walk h args[4]! ctx bt st
      return ← walk h b ((nm, none) :: ctx) (t1.map fun (n, k, o) => .one n k o) st
    | f =>
      let st ← walk h args[4]! ctx none st
      return ← walk h f ctx none st
  if e.isAppOfArity ``letFun 4 then
    match args[3]! with
    | .lam nm t b _ =>
      let st ← walk h t ctx none st
      let bt ← bindingTarget h ctx (toString nm) t
      let st ← if bt.isSome then registerBodyName st h.site nm else pure st
      let st ← walk h args[2]! ctx bt st
      return ← walk h b ((nm, some args[2]!) :: ctx) (t1.map fun (n, k, o) => .one n k o) st
    | f =>
      let st ← walk h args[2]! ctx none st
      return ← walk h f ctx none st
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let st ← walk h args[1]! ctx none st
    -- both branches produce the target; an owned introduction happens once, here
    let (t1', st) := match t1 with
      | some (n, k, true) =>
        (some (n, k, false), { st with intros := st.intros.push ⟨n, k, .derived⟩ })
      | t => (t, st)
    let branch (st : WalkSt) (b : Expr) : MetaM WalkSt :=
      match b with
      | .lam nm t bb _ => do
        let st ← walk h t ctx none st
        walk h bb ((nm, none) :: ctx) (t1'.map fun (n, k, o) => .one n k o) st
      | b => walk h b ctx (t1'.map fun (n, k, o) => .one n k o) st
    let st ← branch st args[3]!
    return ← branch st args[4]!
  let .const c _ := fn
    | do
      let st := opaqueTarget h t1 st
      if e.isApp then
        let st ← walk h fn ctx none st
        args.foldlM (fun st a => walk h a ctx none st) st
      else
        pure st
  -- a sum constructor is transparent toward the quantity it wraps: `some x` produces
  -- whatever `x` produces, onto the conditional port the case addresses. Which case a
  -- value took is the interface's claim (`conditionalPaths`), not a step in the
  -- derivation, so the wrapper carries no edge of its own; a case with no quantity in
  -- it — `none`, an error payload — produces nothing, and nothing is what it means.
  if t1.isSome then
    if let some (.ctorInfo ci) := h.env.find? c then
      if let some (.inductInfo ii) := h.env.find? ci.induct then
        if ii.ctors.length > 1 && args.size == ci.numParams + ci.numFields then
          -- the walk carries bound variables of its own, and only a closed argument has
          -- a type to read; an open one leaves the case opaque, as every open reading is
          let mut carried : Array Expr := #[]
          for i in [ci.numParams:args.size] do
            let a := args[i]!
            unless a.hasLooseBVars do
              if (← carrierKind? h.env h.carriers ctx (← Meta.inferType a)).isSome then
                carried := carried.push a
          if let #[x] := carried then
            return ← walk h x ctx (t1.map fun (n, k, o) => .one n k o) st
          return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- an attested mint: a declared source carrying its harvested reason
  if let some asp := h.attestors.find? (fun a => a.declName == c) then
    if args.size == asp.arity then
      let reason := match args[asp.reasonIdx]? with
        | some (.lit (.strVal s)) => s
        | _ => "…"
      let kind ← match args[asp.kindIdx]? with
        | some ka => kindRefOf ctx ka
        | none => pure (.rendered "_")
      let (n, st) := sourceAt h (.attested reason) kind t1 st
      let st := mintLeaks h e n st
      return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- a gated ingest: raw data admitted through a check
  if h.ingestConsts.contains c then
    let kind := (t1.map fun (_, k, _) => k).getD (.rendered "_")
    let (n, st) := sourceAt h .gated kind t1 st
    let st := mintLeaks h e n st
    return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- an emission-shell mint: `@[kindEmission]` sanctions this declaration's carrier
  -- constructors as the grid↔kernel boundary — the mint enters through a declared
  -- source carrying the tier as its reason
  if h.declEmission && h.carrierSpecs.any (fun s =>
      s.ctorName == c && args.size == s.ctorArity) then
    let kind := (t1.map fun (_, k, _) => k).getD (.rendered "_")
    let (n, st) := sourceAt h (.attested "[kindEmission]") kind t1 st
    let st := mintLeaks h e n st
    return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- a sub-step application: the assembly reads the whole call as a procedure edge
  if h.subSteps.contains c && !args.isEmpty then
    return ← walkSubStep h c e ctx (.inl t1) st
  -- an erasure: the operand's value leaves the calculus for the bare carrier
  if let some victim := h.carrierSpecs.findSome? (fun s =>
      if e.isAppOfArity s.projName s.projArity then e.getAppArgs[s.projArity - 1]?
      else none) then
    let st := opaqueTarget h t1 st
    let st := st.exit (← exitVictim h ctx victim)
    return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- a same-kind sum or difference written through the arithmetic instances. Family A
  -- authors no witness — the shared kind index *is* the certificate, so the edge is
  -- structural, harvested rather than looked for, exactly as the identity wire is. The
  -- kinds are read off the operation's own type arguments, so no argument has to be
  -- closed for this reading to apply.
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 then
    let kx ← carrierKind? h.env h.carriers ctx args[0]!
    let ky ← carrierKind? h.env h.carriers ctx args[1]!
    let kr ← carrierKind? h.env h.carriers ctx args[2]!
    if let (some kx, some ky, some kr) := (kx, ky, kr) then
      if kx == ky && ky == kr then
        let mut st := st
        let mut opNames : Array NodeId := #[]
        let mut opTargets : Std.HashMap Nat Target := {}
        for j in [4, 5] do
          let a := args[j]!
          if isProducerApp h a || !namesNode h a then
            let (m, st') := st.nextFresh
            st := st'
            opNames := opNames.push m
            opTargets := opTargets.insert j (.one m kr true)
          else
            opNames := opNames.push (← nodeIdOf ctx a)
        let mut resNode : NodeId := { root := .unresolved "" }
        match t1 with
        | some (n, k, owned) =>
          if owned then st := { st with intros := st.intros.push ⟨n, k, .derived⟩ }
          resNode := n
        | none =>
          let (m, st') := st.nextFresh
          st := { st' with intros := st'.intros.push ⟨m, kr, .derived⟩ }
          resNode := m
        let ops := (opNames.zip #[kx, ky]).toList
        let addOp := if e.isAppOfArity ``HAdd.hAdd 6 then ``HAdd.hAdd else ``HSub.hSub
        let so : StepOccurrence :=
          ⟨⟨.additive, ops, resNode, kr, h.site, addOp⟩, #[kx, ky], false, false⟩
        st := { st with occs := st.occs.push so }
        for j in [4, 5] do
          st ← walk h args[j]! ctx (opTargets.get? j) st
        return st
  -- a consuming application: binder-stated edges with carrier siblings
  if let some ci := h.env.find? c then
    if !args.isEmpty then
      if let some btys := KindEdges.instantiatedBinderTypes ci.type args then
        let edges ← binderEdges h ctx args btys
        -- the incidence slots: a carrier-typed argument position, and one per carrier
        -- field path of a container-typed one — an operand handed over inside a role
        -- wrapper is the quantity it wraps, named as the wrapper spells it
        let mut opSlots : Array (Nat × List String × KindRef) := #[]
        for j in [0:args.size] do
          let bty := btys[j]!
          let isCarrier := match bty.consumeTypeAnnotations.getAppFn with
            | .const cc _ => h.carriers.contains cc
            | _ => false
          if isCarrier then
            opSlots := opSlots.push
              (j, [], (← carrierKind? h.env h.carriers ctx bty).getD (.rendered "_"))
          else
            for (p, k) in ← carrierPaths h.env h.carriers ctx bty do
              opSlots := opSlots.push (j, p, k)
        if !edges.isEmpty && !opSlots.isEmpty then
          -- name the operands; a nested producer gets a synthesized node to land on
          let mut st := st
          let mut opNames : Array NodeId := #[]
          let mut opTargets : Std.HashMap Nat Target := {}
          for (j, p, k) in opSlots do
            let a := args[j]!
            if p.isEmpty && (isProducerApp h a || !namesNode h a) then
              let (m, st') := st.nextFresh
              st := st'
              opNames := opNames.push m
              opTargets := opTargets.insert j (.one m k true)
            else
              let base ← nodeIdOf ctx a
              opNames := opNames.push { base with path := base.path ++ p }
          -- emit, the first full edge landing on the target node
          let mut consumed := false
          for be in edges do
            let partialInc := opSlots.size < be.family.operandCount
            let ops := (opNames.zip be.opKinds).toList
            let mut resNode : NodeId := { root := .unresolved "" }
            if !partialInc && !consumed && t1.isSome then
              let (n, k, owned) := t1.get!
              consumed := true
              if owned then
                st := { st with intros := st.intros.push ⟨n, k, .derived⟩ }
              resNode := n
            else
              let (m, st') := st.nextFresh
              st := { st' with intros := st'.intros.push ⟨m, be.resKind, .derived⟩ }
              resNode := m
            let so : StepOccurrence :=
              ⟨⟨be.family, ops, resNode, be.resKind, h.site, c⟩, be.opKinds, be.assumed,
               partialInc⟩
            st := { st with occs := st.occs.push so }
          if !consumed then
            st := opaqueTarget h t1 st
          -- recurse into the arguments, nested producers onto their nodes
          for j in [0:args.size] do
            st := (← walk h args[j]! ctx (opTargets.get? j) st)
          return st
  -- a nominal selection: a `match` on a designation of a registered nominal kind. Every
  -- alternative carries the result's kind — the selector chooses between values of one
  -- kind, which is the whole content of a nominal comparison — so the branches become
  -- operand nodes of one `select` edge and the label is its first operand. Without this
  -- the discriminant is naked data flowing into a kinded result, which is what a
  -- selector genuinely looked like before it had a kind to be read at.
  if let some ma ← Meta.matchMatcherApp? e (alsoCasesOn := true) then
    -- the walk carries bound variables of its own, and only a closed term has a type to
    -- read; a discriminant still under one of those binders leaves the selection opaque,
    -- as every open reading is. Reading it anyway is not a wrong answer but a thrown one:
    -- `inferType` rejects a loose bound variable, and the whole ledger fails with it.
    if ma.discrs.size == 1 && ma.alts.size ≥ 2 && !ma.discrs[0]!.hasLooseBVars then
      if let some kn := nominalKind? h.env (← Meta.inferType ma.discrs[0]!) then
        let selKind : KindRef := .decl kn
        let resK? ← match t1 with
          | some (_, k, _) => pure (some k)
          | none =>
            if e.hasLooseBVars then pure none
            else carrierKind? h.env h.carriers ctx (← Meta.inferType e)
        -- a nullary designation still arrives under a placeholder binder — the matcher
        -- gives every alternative a parameter whether its constructor carries data or
        -- not — so each alternative is peeled to the term it actually computes
        let mut peeled : Array (Expr × BinderCtx) := #[]
        for i in [0:ma.alts.size] do
          let mut body := ma.alts[i]!
          let mut ctx' := ctx
          let mut ok := true
          for _ in [0:ma.altNumParams[i]!] do
            match body with
            | .lam nm _ b _ => ctx' := (nm, none) :: ctx'; body := b
            | _ => ok := false
          if ok then peeled := peeled.push (body, ctx')
        if peeled.size == ma.alts.size then
        if let some resK := resK? then
          let mut st := st
          let d := ma.discrs[0]!
          let mut selNode : NodeId := { root := .unresolved "" }
          if namesNode h d then
            selNode ← nodeIdOf ctx d
          else
            let (m, st') := st.nextFresh
            st := st'
            selNode := m
            st ← walk h d ctx (some (.one m selKind true)) st
          let mut ops : List (NodeId × KindRef) := [(selNode, selKind)]
          for (alt, ctx') in peeled do
            let (m, st') := st.nextFresh
            st := st'
            st ← walk h alt ctx' (some (.one m resK true)) st
            ops := ops ++ [(m, resK)]
          let mut resNode : NodeId := { root := .unresolved "" }
          match t1 with
          | some (n, _, owned) =>
            if owned then st := { st with intros := st.intros.push ⟨n, resK, .derived⟩ }
            resNode := n
          | none =>
            let (m, st') := st.nextFresh
            st := { st' with intros := st'.intros.push ⟨m, resK, .derived⟩ }
            resNode := m
          let so : StepOccurrence :=
            ⟨⟨.select ma.alts.size, ops, resNode, resK, h.site, .anonymous⟩,
             (ops.map (·.2)).toArray, false, false⟩
          st := { st with occs := st.occs.push so }
          return ← ma.remaining.foldlM (fun st a => walk h a ctx none st) st
  -- a single-alternative matcher: tuple destructuring — the discriminant produces
  -- onto the alternative's binders, and the alternative is the continuation
  if let some ma ← Meta.matchMatcherApp? e (alsoCasesOn := true) then
    if ma.discrs.size == 1 && ma.alts.size == 1 then
      let mut binders : Array (Name × Expr) := #[]
      let mut body := ma.alts[0]!
      let mut peeled := true
      for _ in [0:ma.altNumParams[0]!] do
        match body with
        | .lam nm t b _ => binders := binders.push (nm, t); body := b
        | _ => peeled := false
      if peeled then
        -- kinded slots, each binder type read in the progressively extended context;
        -- a container binder takes one slot per carrier field path, the nodes named as
        -- the continuation spells the projections. A matcher binder is a body name:
        -- it joins the flat namespace the `let`s share, and is refused on reuse.
        let mut st := st
        let mut ctx' := ctx
        let mut slots : List (List (NodeId × KindRef × Bool)) := []
        for (nm, t) in binders do
          let slot ← match ← carrierKind? h.env h.carriers ctx' t with
            | some k => pure [(NodeId.letBound (toString nm), k, true)]
            | none => do
              let paths ← carrierPaths h.env h.carriers ctx' t
              pure (paths.toList.map fun (p, k) =>
                ({ NodeId.letBound (toString nm) with path := p }, k, true))
          unless slot.isEmpty do
            st ← registerBodyName st h.site nm
          slots := slots ++ [slot]
          ctx' := (nm, none) :: ctx'
        st ← walk h ma.discrs[0]! ctx (some (.tuple slots)) st
        st ← walk h body ctx' (t1.map fun (n, k, o) => .one n k o) st
        return ← ma.remaining.foldlM (fun st a => walk h a ctx none st) st
  -- a configuration read: the identity wire from the constant's port node
  if h.configConsts.contains c then
    if let some (n, k, owned) := t1 then
      let st := st.copyTo h.site (← nodeIdOf ctx e) n k owned
      return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- opaque: no reading applies (a raw mint, a sub-step call, a bare computation)
  let st := opaqueTarget h t1 st
  args.foldlM (fun st a => walk h a ctx none st) st

/-- A sub-step application read as a procedure edge (assembly mode). The callee's
carrier-typed argument positions are the incidence — named like a consuming
application's operands, nested producers landing on synthesized nodes — and the edge
derives the call's target: the single target node (or a synthesized one), or one
occurrence per kinded slot when the caller destructures a multi-output callee. Operand
kinds are the callee's *instantiated* binder kinds and a synthesized result's kind its
instantiated conclusion kind — the call site is where a kind-generic step becomes
concrete. -/
partial def walkSubStep (h : HarvestCtx) (c : Name) (e : Expr) (ctx : BinderCtx)
    (targets : Sum (Option (NodeId × KindRef × Bool))
      (List (List (NodeId × KindRef × Bool))))
    (st : WalkSt) : MetaM WalkSt := do
  let args := e.getAppArgs
  let fallback (st : WalkSt) : MetaM WalkSt := do
    let st := match targets with
      | .inl t1 => opaqueTarget h t1 st
      | .inr _ => st
    args.foldlM (fun st a => walk h a ctx none st) st
  let some ci := h.env.find? c | fallback st
  let some btys := KindEdges.instantiatedBinderTypes ci.type args | fallback st
  -- the incidence slots: a carrier-typed argument position, and one per carrier field
  -- path of a container-typed one — the callee's input ports, in the same order
  let mut opSlots : Array (Nat × List String × KindRef) := #[]
  for j in [0:args.size] do
    let bty := btys[j]!
    -- a leaf of the callee's interface: a registered carrier, or a registered nominal
    -- designation set. The witness path above admits carriers only — a witness relates
    -- kinds-of-QUANTITY, and an extra operand there would shift the positions its
    -- equation names — but a procedure edge's operands are the callee's input ports,
    -- and a designation port is one of those.
    let isCarrier := match bty.consumeTypeAnnotations.getAppFn with
      | .const cc _ => h.carriers.contains cc || (BoundaryAudit.nominalKindOf? h.env cc).isSome
      | _ => false
    if isCarrier then
      opSlots := opSlots.push
        (j, [], (← carrierKind? h.env h.carriers ctx bty).getD (.rendered "_"))
    else
      for (p, k) in ← carrierPaths h.env h.carriers ctx bty do
        opSlots := opSlots.push (j, p, k)
  -- no incidence exposed: the call relates nothing this graph can see, so it is not an
  -- edge. A zero-operand `step` would be a mint wearing an edge's name.
  if opSlots.isEmpty then return ← fallback st
  let opKinds : Array KindRef := opSlots.map (·.2.2)
  -- name the operands; a nested producer gets a synthesized node to land on — one node
  -- per carrier field path when its value is a container, so the outer occurrence and
  -- the inner producer name the same thing whichever shape the value travels in
  let mut st := st
  let mut fresh : Std.HashMap Nat NodeId := {}
  for (j, _, _) in opSlots do
    unless fresh.contains j do
      if isProducerApp h args[j]! || !namesNode h args[j]! then
        let (m, st') := st.nextFresh
        st := st'
        fresh := fresh.insert j m
  let mut opNames : Array NodeId := #[]
  for (j, p, _) in opSlots do
    match fresh[j]? with
    | some m => opNames := opNames.push { m with path := m.path ++ p }
    | none =>
      let base ← nodeIdOf ctx args[j]!
      opNames := opNames.push { base with path := base.path ++ p }
  let mut opTargets : Std.HashMap Nat Target := {}
  for (j, m) in fresh.toList do
    let slots := (opSlots.filterMap fun (j', p, k) =>
      if j' == j then some ({ m with path := m.path ++ p }, k, true) else none).toList
    opTargets := opTargets.insert j
      (match slots with
       | [(n, k, o)] => .one n k o
       | ss => .tuple [ss])
  let ops := (opNames.zip opKinds).toList
  -- the procedure edge names the callee in full: identity, not rendering — the
  -- assembly resolves it to a call-site instance and the renderer shortens it
  let fam := Provenance.EdgeFamily.step c none opSlots.size
  let emit (st : WalkSt) (node : NodeId) (kind : KindRef) (owned : Bool) : WalkSt :=
    let st := if owned then { st with intros := st.intros.push ⟨node, kind, .derived⟩ }
              else st
    let so : StepOccurrence := ⟨⟨fam, ops, node, kind, h.site, c⟩, opKinds, false, false⟩
    { st with occs := st.occs.push so }
  match targets with
  | .inl t1 =>
    match t1 with
    | some (n, k, owned) => st := emit st n k owned
    | none =>
      -- an unassigned single result still derives: onto a synthesized node, at the
      -- callee's instantiated conclusion kind
      let kind ← match KindEdges.instantiatedConclusion ci.type args with
        | some concl => pure ((← carrierKind? h.env h.carriers ctx concl).getD (.rendered "_"))
        | none => pure (KindRef.rendered "_")
      let (m, st') := st.nextFresh
      st := emit st' m kind true
  | .inr comps =>
    -- one procedure edge per kinded node of every slot: a container component derives
    -- each of its field paths from the same call
    for c in comps do
      for (n, k, owned) in c do
        st := emit st n k owned
  -- recurse into the arguments, nested producers onto their nodes
  for j in [0:args.size] do
    st := (← walk h args[j]! ctx (opTargets.get? j) st)
  return st

end

/-- The occurrence reading of a bare value expression against explicit registries — the
walk on an expression that is not a declaration (validation probes build these by hand).
Ports, tiers, and attribution need the declaration; the occurrences do not. -/
def occurrencesOfValue (env : Environment) (carriers : Array Name) (e : Expr) :
    MetaM (Array StepOccurrence) := do
  let h : HarvestCtx :=
    { env, carriers, carrierSpecs := #[], configConsts := {}, ingestConsts := {},
      attestors := #[], site := "<expr>", declKindConst := false }
  return (← walk h e [] none {}).occs

/-! ## The constructed object and its renderings -/

/-- An unkinded signature position (module header, "Unkinded positions"): an explicit
binder or result component whose type carries no kind information at all — naked data
crossing the interface, which does not conform to the calculus's methodology. The
kinded ports gap-keep the position; the harvest names it, so every report marks it
red. -/
structure UnkindedSlot where
  /-- The binder name, or the gap-kept `result.{i}` position. -/
  node : String
  /-- The rendered type — what the signature states instead of a kind. -/
  type : String
  /-- `input` for a binder, `output` for a result component. -/
  dir : PortDir
deriving Repr, Inhabited, BEq

/-- One unkinded line: `unkinded input nR : Nat`. -/
def renderUnkinded (u : UnkindedSlot) : String :=
  s!"unkinded {u.dir.label} {u.node} : {u.type}"

/-- One unkinded-flow line: `unkinded flow: nR ⇒ _1` — the path by which unkinded
information mints or steers kinded information, outside the kinded algebra. -/
def renderLeak (l : String × NodeId) : String :=
  s!"unkinded flow: {l.1} ⇒ {renderNode l.2}"

/-- The harvest of one step: the graph's constituents, with the two markers
(`assumed` / `partialIncidence`) the graph value does not carry, the unkinded
positions of its signature, and their flows into the kinded nodes. `provenance` is the
constructed object — the unkinded reading deliberately stays outside it: the wiring
judgment the kernel decides is about the kinded algebra, and the red inventory is the
record of what falls outside that algebra, carried by the renderings. -/
structure StepGraph where
  ports : List (Port NodeId KindRef)
  intros : List (Intro NodeId KindRef)
  occs : Array StepOccurrence
  exits : List NodeId
  unkinded : List UnkindedSlot := []
  leaks : List (String × NodeId) := []

/-- **The constructed graph value.** Partial-incidence occurrences are excluded from
the wiring — a sub-step boundary is not an edge of this step's graph — so a step that
hides an operand behind a helper is refused until assembly closes it. -/
def StepGraph.provenance (s : StepGraph) : Provenance NodeId KindRef :=
  { ports := s.ports
    intros := s.intros
    occurrences := ((s.occs.filter (!·.partialIncidence)).map (·.occ)).toList
    exits := s.exits }

/-- One port line: `input x : alphaK`. -/
def renderPort (p : Port NodeId KindRef) : String :=
  s!"{p.dir.label} {renderNode p.node} : {p.kind.render}"

/-- One introduction line: `derived t : deltaK`, `gated _1 : k`,
`attested "reason" _1 : k`. -/
def renderIntro (i : Intro NodeId KindRef) : String :=
  s!"{i.tier.label} {renderNode i.node} : {i.kind.render}"

/-- The full graph rendering: ports, unkinded positions, introductions, wired
occurrences (markers kept), exits, unkinded flows, and the evaluated well-formedness
verdict. -/
def StepGraph.renderLines (s : StepGraph) : List String :=
  s.ports.map renderPort
    ++ s.unkinded.map renderUnkinded
    ++ s.intros.map renderIntro
    ++ (s.occs.map (·.renderWired)).toList
    ++ s.exits.map (fun n => s!"exit {renderNode n}")
    ++ s.leaks.map renderLeak
    ++ [s!"well-formed: {s.provenance.wellFormed}"]

/-- Construct the step graph of a declaration: the interface off the signature (inputs
in signature order, configuration reads in body order, outputs in component order —
a binder or component at a non-carrier type is no port, and output node names keep
component positions), then the wiring off the elaborated value. `subSteps` is the
assembly set: constant heads the walk reads as procedure edges rather than opaque
calls. -/
def stepGraphOf (decl : Name) (subSteps : Array Name := #[]) : MetaM StepGraph := do
  let env ← getEnv
  let some info := env.find? decl
    | throwError "unknown declaration '{decl}'"
  let carriers := operandCarriers env
  let cfgConsts := configConstants env
  let h : HarvestCtx :=
    { env, carriers
      carrierSpecs := (BoundaryAudit.kindCarrierNames env).filterMap
        (BoundaryAudit.mkCarrierSpec env)
      configConsts := cfgConsts
      ingestConsts := ingestConstants env
      attestors := (BoundaryAudit.kindAttestNames env).filterMap
        (BoundaryAudit.mkAttestSpec env)
      site := toString decl
      declKindConst := (BoundaryAudit.boundaryTags env).any fun t =>
        t.decl == decl && t.tier == .kindConst
      declEmission := (BoundaryAudit.boundaryTags env).any fun t =>
        t.decl == decl && t.tier == .kindEmission
      subSteps }
  Meta.forallTelescope info.type fun fvars resultTy => do
    let mut ports : Array (Port NodeId KindRef) := #[]
    let mut unkinded : Array UnkindedSlot := #[]
    let mut unkIdx : Array (Nat × String) := #[]
    -- the signature's name gates, before any port is minted. A kind-bearing binder or a
    -- kind binder with an inaccessible name would put a machine-generated name on the
    -- interface — nobody's reference — and two sharing one name would make one
    -- reference two nodes; both are refused here, where the signature is the fix.
    let mut portNames : Array String := #[]
    let mut kindParams : Array String := #[]
    for fv in fvars do
      let ty ← fv.fvarId!.getType
      let unm := (← fv.fvarId!.getDecl).userName
      if ty.isConstOf ``KindOfProperty then
        if unm.hasMacroScopes || unm.isAnonymous then
          throwError "a kind binder of '{decl}' has no accessible name — name it, so \
            ports can state their kind by it"
        let s := toString unm
        if kindParams.contains s then
          throwError "two kind binders of '{decl}' are named '{s}' — a kind stated by \
            that name would not say which; rename one"
        kindParams := kindParams.push s
      else
        let kinded := (← carrierKind? env carriers [] ty).isSome
          || !(← carrierPaths env carriers [] ty).isEmpty
          || (← signatureKind? env carriers [] ty).isSome
        if kinded then
          if unm.hasMacroScopes || unm.isAnonymous then
            throwError "a kind-bearing binder of '{decl}' has no accessible name — name \
              it, so the port it states is a reference someone can write"
          let s := toString unm
          if portNames.contains s then
            throwError "two kind-bearing binders of '{decl}' are named '{s}' — one \
              reference cannot name both; rename one"
          portNames := portNames.push s
    for idx in [0:fvars.size] do
      let fv := fvars[idx]!
      let ty ← fv.fvarId!.getType
      if let some k ← carrierKind? env carriers [] ty then
        ports := ports.push
          { node := NodeId.binder (toString (← fv.fvarId!.getUserName)), kind := k
            dir := .input }
      else
        -- a container binder states its kinds through its fields: one port per carrier
        -- field path, named as the body spells the projection
        let paths ← carrierPaths env carriers [] ty
        if !paths.isEmpty then
          let nm := toString (← fv.fvarId!.getUserName)
          for (p, k) in paths do
            ports := ports.push
              { node := { NodeId.binder nm with path := p }, kind := k, dir := .input }
        else if let some sig ← signatureKind? env carriers [] ty then
          -- a functional binder ports at its kind signature — the module-valued port:
          -- a kind-typed arrow is an anonymous contract, so the type is the declaration
          -- and the harvest derives the port mechanically
          ports := ports.push
            { node := NodeId.binder (toString (← fv.fvarId!.getUserName)), kind := sig
              dir := .input }
        else
          -- the unkinded reading: an explicit data binder whose type carries no kind
          -- information at all (propositions and sorts are interface logic, not data)
          let bi := (← fv.fvarId!.getDecl).binderInfo
          if bi.isExplicit && !ty.isSort && !(← Meta.isProp ty)
              && !(← kindBearing carriers ty) then
            let nm := toString (← fv.fvarId!.getUserName)
            unkinded := unkinded.push ⟨nm, toString (← Meta.ppExpr ty), .input⟩
            unkIdx := unkIdx.push (idx, nm)
    if let some v := info.value? then
      for c in configReads cfgConsts (subSteps.foldl NameSet.insert {}) v do
        let some ci := env.find? c | continue
        -- the constant's full name: a config port is an interface node, and its
        -- identity cannot depend on who is reading
        let node := NodeId.config c
        -- a container-typed constant states its kinds the way a container binder does:
        -- one config port per carrier field path (a configured quantity does not stop
        -- being one for travelling in a role)
        let slots ← Meta.forallTelescope ci.type fun _ resTy => do
          match ← carrierKind? env carriers [] resTy with
          | some k => return #[(([] : List String), k)]
          | none => carrierPaths env carriers [] resTy
        if slots.isEmpty then
          ports := ports.push { node := node, kind := .unkinded, dir := .config }
        else
          for (p, k) in slots do
            ports := ports.push
              { node := { node with path := p }, kind := k, dir := .config }
    let comps := prodComponents resultTy
    let mut outSlots : Array (List (NodeId × KindRef × Bool)) := #[]
    for i in [0:comps.size] do
      let node := if comps.size == 1 then NodeId.result else NodeId.resultAt (i + 1)
      match ← carrierKind? env carriers [] comps[i]! with
      | some k =>
        ports := ports.push { node := node, kind := k, dir := .output }
        outSlots := outSlots.push [(node, k, false)]
      | none =>
        let cty := comps[i]!
        let paths ← carrierPaths env carriers [] cty
        let cases ← if paths.isEmpty then conditionalPaths env carriers [] cty
                    else pure #[]
        if !paths.isEmpty then
          for (p, k) in paths do
            ports := ports.push
              { node := { node with path := p }, kind := k, dir := .output }
          outSlots := outSlots.push
            (paths.toList.map fun (p, k) => ({ node with path := p }, k, false))
        else if !cases.isEmpty then
          for (p, k) in cases do
            ports := ports.push
              { node := { node with path := p }, kind := k, dir := .conditional }
          outSlots := outSlots.push
            (cases.toList.map fun (p, k) => ({ node with path := p }, k, false))
        else
          outSlots := outSlots.push []
          if !cty.isSort && !(← Meta.isProp cty) && !(← kindBearing carriers cty) then
            unkinded := unkinded.push
              ⟨renderNode node, toString (← Meta.ppExpr cty), .output⟩
    let st ← match info.value? with
      | none => pure {}
      | some v =>
        Meta.lambdaTelescope v fun lamFvars body => do
          let hv := { h with unkindedFVars := unkIdx.filterMap fun (idx, nm) =>
            lamFvars[idx]?.map fun fv => (fv.fvarId!, nm) }
          let rootTarget : Option Target :=
            if comps.size == 1 then Target.ofSlots outSlots[0]!
            else if outSlots.any (!·.isEmpty) then
              some (.tuple outSlots.toList)
            else
              none
          let mut st ← walk hv body [] rootTarget {}
          -- the output flows: an unkinded argument surviving the mint mask into a
          -- kinded output's defining expression steers that output from outside the
          -- kinded algebra — per component on a literal tuple spine, else every
          -- kinded output
          -- the defining expression behind each output slot: a literal tuple splits per
          -- component, and a component the body assembles by its own constructor splits
          -- again per field (`ctorFieldSlots`), so a bundled result is attributed per
          -- port and not wholesale. `none` where the body computes its result another
          -- way (a branch, a call), and attribution falls back to every kinded output.
          let attrib? : Option (Array (Expr × List (NodeId × KindRef × Bool))) ←
            match prodValueComps body comps.size with
            | none => pure none
            | some vs => do
              let mut out : Array (Expr × List (NodeId × KindRef × Bool)) := #[]
              for ci in [0:vs.size] do
                match ← ctorFieldSlots hv [] vs[ci]! outSlots[ci]! with
                | some fss => out := out ++ fss
                | none => out := out.push (vs[ci]!, outSlots[ci]!)
              pure (some out)
          for (fv, nm) in hv.unkindedFVars do
            match attrib? with
            | some parts =>
              for (ve, slot) in parts do
                if (maskMints hv ve).containsFVar fv then
                  for (n, _, _) in slot do st := st.leak nm n
            | none =>
              if (maskMints hv body).containsFVar fv then
                for slot in outSlots do
                  for (n, _, _) in slot do st := st.leak nm n
          pure st
    return { ports := ports.toList, intros := st.intros.toList, occs := st.occs,
             exits := st.exits.toList, unkinded := unkinded.toList,
             leaks := st.leaks.toList }

/-! ## The assembly — the multi-step graph

An assembly reads a set of declarations as ONE pipeline. Each member contributes a
*level*: its walked graph, with the other members read as sub-step procedure edges,
when that graph is well-formed — the body exhibits its wiring (`walked`) — and
otherwise its signature box: ports plus the level's own procedure edge deriving each
output port from the input ports, interior accountability left to the boundary audit's
per-declaration tiers (`interface`). Levels are renamed into per-step namespaces
(`step/node`) and unioned, and every walked call site is dissected into the callee's
box: the caller's operands wire to the callee's input ports by `copy` — those ports
demote to derived interior nodes — the callee's own level derives its outputs, and the
caller's procedure edge stands as the call's derivation. **Demotion runs both ways**: the
output slot a call consumes demotes too, because a result some member of the assembly
takes is interior to the assembly, and an interface that reported it would count every
intermediate value as something the pipeline hands out. What survives both demotions is
the assembly's boundary — the value a `Contract` is compared against. A kind-generic callee is
monomorphized by its call site: the wires state the instantiated kinds, so the box is
renamed through the call's kind assignment — the assembly's form of "carrier-generic
code becomes concrete where its witnesses are discharged". **A level belongs to a call
site, not to a member**: the members expand into a call tree and each call gets its own
instance of the callee's box, monomorphized by that call and named `member#k` where
there is more than one to tell apart. One box for two calls would either conflate the
invocations' operands onto one input node — a false claim that passes, since both wires
land on a declared node — or, for a kind-generic step called at two kinds, contradict
itself on them. A call is identified by its operands, so a multi-output call's several
procedure edges stay one call and their order is its slot order. What instances do *not*
duplicate is what they cite: **a configuration port is an address, an argument is a
position**, so a member's instances share its config ports and only the first declares
them — the rule the signature harvest already keeps within a body, where a constant read
twice is one port and two incidence positions. Three ports for one constant would tell a
deployment to bind it three times and `Contract.discharges` would count it three times
over; inputs are not shared, because two instances take two data.

The *citation* relation — which member's value references which — is harvested by
constant scan and rendered (`cites: a → b`), never wired: a call inside an interior
the walk cannot wire is a citation a figure may draw dashed, not an edge of the
checked object. Well-formedness is checked on the assembled object, and
`#kind_assembly_decide` has the kernel re-derive it.

The membership choice itself is judged by `#kind_contract` / `#kind_contract_decide`,
against a `Provenance.Contract` the author declares: the assembly's surviving ports and
exits must be the ones the contract states, so a member added or dropped moves the
boundary and the comparison says which way. Well-formedness cannot make that judgment —
it is monotone under disjoint union (`Provenance`, "What well-formedness does not
claim") — which is why the boundary is declared rather than inferred, and why the
rendering prints the two difference lists whenever they are non-empty. The contract names
its own members, so those commands take no bracket list: the scope is assembled *from the
declaration under judgment*, and every other consumer of the same scope — a figure
generator, a downstream tier — reads the member list off it instead of restating it. -/

/-- One level of an assembly: the declaration, its rendered name (the node-namespace
prefix), its inclusion mode (`walked` — the wired interior; otherwise the interface
box), the level graph contributed — in its own node namespace, monomorphized by
its wired call sites, call-fed input ports already demoted — and `src`, the assembly's
own provenance: the member's declaring source file, working-directory-relative when it
resolves under it (the go-to-definition search path answers), the module name when no
file resolves, empty when unattributed — so a rendering can state where each assembled
definition lives. -/
structure AssemblyLevel where
  decl : Name
  name : String
  /-- The level's identity — the call-site instance the nodes of this level carry. -/
  lvl : Provenance.Level
  walked : Bool
  graph : Provenance NodeId KindRef
  src : String := ""
  /-- The member's unkinded signature positions, in the level's node namespace — the
  red inventory a rendering marks (module header, "Unkinded positions"). -/
  unkinded : List UnkindedSlot := []
  /-- The member's unkinded flows, namespaced, kept where the target node is declared
  in the level's contributed graph — the red arrows. -/
  leaks : List (String × NodeId) := []
deriving Inhabited

/-- A multi-step assembly: the levels with their modes, the one union graph the
verdict and the kernel theorem are stated on, and the citation relation (by member
declaration name; renderings shorten). -/
structure Assembly where
  levels : Array AssemblyLevel
  graph : Provenance NodeId KindRef
  cites : Array (Name × Name)

/-- The signature box of an interface-mode level: its ports, plus the level's own
procedure edge deriving each output port from the input ports — the signature's claim,
with interior accountability the audit's. -/
def interfaceBox (member : Name) (g : StepGraph) : Provenance NodeId KindRef :=
  let ins := g.ports.filter (·.dir == .input)
  let outs := g.ports.filter (·.dir.produced)
  { ports := g.ports
    intros := []
    occurrences := outs.map fun o =>
      ⟨.step member none ins.length, ins.map (fun p => (p.node, p.kind)), o.node, o.kind,
       lastComponent member, .anonymous⟩
    exits := [] }

/-- Assemble a set of declarations into one multi-step graph (module section, "The
assembly"): per-level harvests with the other members as sub-steps, walked-or-interface
inclusion, call-site dissection with monomorphizing kind maps and port demotion,
member-constant wiring,
namespaced union, and the citation scan. -/
def assemble (decls : Array Name) : MetaM Assembly := do
  let env ← getEnv
  -- the node-namespace prefixes and procedure-edge labels; two members sharing one
  -- would share a node namespace, so the collision is refused rather than merged
  let mut names : Array String := #[]
  for d in decls do
    let some ci := env.find? d | throwError "unknown declaration '{d}'"
    let n ← stepNameOf ci
    if names.contains n then
      throwError "two assembly members are named '{n}' — one node namespace cannot hold both"
    names := names.push n
  -- the assembly's own provenance: each member's declaring module resolved to its
  -- source file through the go-to-definition search path, rendered relative to the
  -- working directory when under it; the module name stands in when no file resolves
  let srcSearch ← getSrcSearchPath
  let cwd := (← IO.FS.realPath (← IO.currentDir)).toString ++ "/"
  let mut srcs : Array String := #[]
  for d in decls do
    let mod := match env.getModuleIdxFor? d with
      | some idx => env.allImportedModuleNames[idx.toNat]!
      | none => env.mainModule
    let src ← match (← srcSearch.findModuleWithExt "lean" mod) with
      | some p =>
        let ps := (← IO.FS.realPath p).toString
        pure (if ps.startsWith cwd then (ps.drop cwd.length).toString else ps)
      | none => pure (toString mod)
    srcs := srcs.push src
  -- per-level harvests: walked exactly when the wired interior is well-formed; the
  -- unkinded reading rides along either way (a signature fact and a body fact — the
  -- interface box changes neither)
  let mut walkedFlags : Array Bool := #[]
  let mut contribs : Array (Provenance NodeId KindRef) := #[]
  let mut unks : Array (List UnkindedSlot) := #[]
  let mut lks : Array (List (String × NodeId)) := #[]
  for i in [0:decls.size] do
    let d := decls[i]!
    let g ← stepGraphOf d (subSteps := decls.filter (· != d))
    unks := unks.push g.unkinded
    lks := lks.push g.leaks
    let p := g.provenance
    if p.wellFormed then
      walkedFlags := walkedFlags.push true
      contribs := contribs.push p
    else
      walkedFlags := walkedFlags.push false
      contribs := contribs.push (interfaceBox d g)
  -- call-site dissection: the instance tree, its wires, demotions, and per-instance
  -- kind assignments. **A level belongs to a call site, not to a member.** A callee
  -- wired from two call sites is two instantiations — different operands, and for a
  -- kind-generic step different kinds — and one box cannot state both: it would either
  -- conflate the invocations' operands onto one input node or contradict itself on
  -- their kinds, and the first of those passes silently. So the members expand into a
  -- *call tree*: each call gets its own copy of the callee's box, in its own node
  -- namespace, monomorphized by that call. A member with a single call site keeps its
  -- plain name, because there is nothing to tell apart.
  --
  -- One call is one *group* of the caller's procedure edges: a multi-output call emits
  -- one edge per output slot over the same operands, so the operand list is what
  -- identifies the call and the group's order is the slot order.
  --
  -- the members some walked member calls; the rest are the tree's roots
  let mut isCallee : Array Bool := .replicate decls.size false
  for i in [0:decls.size] do
    unless walkedFlags[i]! do continue
    for o in contribs[i]!.occurrences do
      if let .step t _ _ := o.family then
        if let some j := decls.findIdx? (· == t) then
          isCallee := isCallee.set! j true
  -- the instances, in discovery order: the member, the calling instance, the call's
  -- operands, and the caller-occurrence indices the call spans
  let mut iMem : Array Nat := #[]
  let mut iParent : Array (Option Nat) := #[]
  let mut iOps : Array (List (NodeId × KindRef)) := #[]
  let mut iOccs : Array (Array Nat) := #[]
  let mut iChildren : Array (Array (Nat × Array Nat)) := #[]
  for j in [0:decls.size] do
    unless isCallee[j]! do
      iMem := iMem.push j; iParent := iParent.push none
      iOps := iOps.push []; iOccs := iOccs.push #[]
  let mut cur := 0
  let mut growing := true
  while growing do
    growing := false
    while cur < iMem.size do
      iChildren := iChildren.push #[]
      let i := iMem[cur]!
      if walkedFlags[i]! then
        let occs := contribs[i]!.occurrences.toArray
        let mut groups : Array (Nat × List (NodeId × KindRef) × Array Nat) := #[]
        for oi in [0:occs.size] do
          let o := occs[oi]!
          if let .step t _ _ := o.family then
            if let some j := decls.findIdx? (· == t) then
              match groups.findIdx? (fun g => g.1 == j && g.2.1 == o.operands) with
              | some gi => groups := groups.modify gi fun g => (g.1, g.2.1, g.2.2.push oi)
              | none => groups := groups.push (j, o.operands, #[oi])
        for (j, ops, ois) in groups do
          if iMem.size > 4096 then
            throwError "the assembly's call tree does not close — a member reaches itself"
          iChildren := iChildren.modify cur (·.push (iMem.size, ois))
          iMem := iMem.push j; iParent := iParent.push (some cur)
          iOps := iOps.push ops; iOccs := iOccs.push ois
      cur := cur + 1
    -- a member no root reaches is still a level: membership is the author's claim, and
    -- a scope that mentions a declaration nothing in it calls still answers for it
    for j in [0:decls.size] do
      unless iMem.contains j do
        iMem := iMem.push j; iParent := iParent.push none
        iOps := iOps.push []; iOccs := iOccs.push #[]
        growing := true
  -- the instance identities: the member's declaration name with a 1-based ordinal,
  -- always present in the identity; `Level.render` collapses the ordinal in names
  let mut instCount : Array Nat := .replicate decls.size 0
  for k in [0:iMem.size] do instCount := instCount.modify iMem[k]! (· + 1)
  let mut seenInst : Array Nat := .replicate decls.size 0
  let mut iName : Array String := #[]
  let mut iLevel : Array Provenance.Level := #[]
  let mut iOrd : Array Nat := #[]
  for k in [0:iMem.size] do
    let j := iMem[k]!
    let n := seenInst[j]! + 1
    seenInst := seenInst.set! j n
    let lvl := Provenance.Level.inst decls[j]! n
    iLevel := iLevel.push lvl
    iOrd := iOrd.push n
    iName := iName.push lvl.render
  -- the wires: each call's operands onto its own instance's input ports, with that
  -- instance's kind assignment and both demotions
  let mut wires : Array (Provenance.Occurrence NodeId KindRef) := #[]
  let mut demoted : Array NodeId := #[]
  let mut demotedOuts : Array NodeId := #[]
  let mut kindPairs : Array (Array (KindRef × KindRef)) := .replicate iMem.size #[]
  for k in [0:iMem.size] do
    let some pk := iParent[k]! | continue
    let callerLvl := iLevel[pk]!
    let calleeLvl := iLevel[k]!
    let j := iMem[k]!
    let calleeIns := contribs[j]!.ports.filter (·.dir == .input)
    let calleeOuts := contribs[j]!.ports.filter (·.dir.produced)
    -- a caller operand that is one of the caller's own config addresses lives in the
    -- member-wide scope, exactly where the caller's transform will declare that port
    let callerCfg : List NodeId :=
      (contribs[iMem[pk]!]!.ports.filter (·.dir == .config)).map (·.node)
    for (p, opc) in calleeIns.zip iOps[k]! do
      let src : NodeId :=
        if callerCfg.contains opc.1 then
          { opc.1 with level := some (.member decls[iMem[pk]!]!) }
        else { opc.1 with level := some callerLvl }
      let dst : NodeId := { p.node with level := some calleeLvl }
      wires := wires.push ⟨.copy, [(src, opc.2)], dst, opc.2, iName[pk]!, .anonymous⟩
      unless demoted.contains dst do
        demoted := demoted.push dst
      kindPairs := kindPairs.modify k (·.push (p.kind, opc.2))
    -- the call's results monomorphize the callee's output kinds, in slot order, and
    -- the consumed slot demotes: what a caller in the assembly takes is interior to
    -- the assembly, the dual of the input demotion above
    let pocc := contribs[iMem[pk]!]!.occurrences.toArray
    for s in [0:iOccs[k]!.size] do
      if let some out := calleeOuts[s]? then
        let o := pocc[iOccs[k]![s]!]!
        kindPairs := kindPairs.modify k (·.push (out.kind, o.resultKind))
        let dst : NodeId := { out.node with level := some calleeLvl }
        unless demotedOuts.contains dst do
          demotedOuts := demotedOuts.push dst
  -- **A configuration constant that is also a member is a wire, not a source.** A
  -- deployment constant read as `c.field` declares a configuration port at that address,
  -- which is right when `c` is somebody else's business. When `c` is a *member of this
  -- assembly* the address names a value this assembly computes, and reading it as a
  -- source hides the computation behind it: a geometry read as two numbers states two
  -- numbers, and the angle they were computed from never reaches the boundary at all. So
  -- the read becomes an identity wire off the member's own result and both ends demote —
  -- the consumer's port because what a member of the assembly feeds is interior to it,
  -- the producer's output for the same reason a consumed call result demotes. What
  -- surfaces in their place is the producing member's own interface, which is the thing
  -- that was being hidden.
  let mut cfgWires : Array (Provenance.Occurrence NodeId KindRef) := #[]
  let mut demotedCfg : Array NodeId := #[]
  let mut wiredCite : Array (Nat × Nat) := #[]
  for j in [0:decls.size] do
    -- one instance only: a constant is read at an address, and an address that named
    -- two instances would not be one
    if instCount[j]! > 1 then continue
    let prodDecl := decls[j]!
    for j' in [0:decls.size] do
      if j' == j then continue
      for q in contribs[j']!.ports do
        if q.dir != .config then continue
        unless q.node.root == .const prodDecl do continue
        let src : NodeId :=
          { level := some (.inst prodDecl 1), root := .result none, path := q.node.path }
        let dst : NodeId := { q.node with level := some (.member decls[j']!) }
        unless demotedCfg.contains dst do
          demotedCfg := demotedCfg.push dst
          cfgWires := cfgWires.push ⟨.copy, [(src, q.kind)], dst, q.kind, names[j]!, .anonymous⟩
        unless demotedOuts.contains src do demotedOuts := demotedOuts.push src
        unless wiredCite.contains (j', j) do wiredCite := wiredCite.push (j', j)
  -- transform each instance: name its calls after the instances they reach,
  -- monomorphize, namespace, demote — then union, the members in declaration order
  let mut levels : Array AssemblyLevel := #[]
  let mut graph : Provenance NodeId KindRef := ⟨[], [], [], []⟩
  let mut declaredCfg : Array NodeId := #[]
  let mut order : Array Nat := #[]
  for j in [0:decls.size] do
    for k in [0:iMem.size] do
      if iMem[k]! == j then order := order.push k
  for k in order do
    let j := iMem[k]!
    let name := iName[k]!
    let lvl := iLevel[k]!
    -- first assignment wins, as ever: the association list is searched in push order
    let kmap := kindPairs[k]!.toList
    let p := contribs[j]!
    -- a procedure edge names the instance it reaches, so two calls to one member are
    -- two edges to two boxes rather than two edges that read alike
    let mut calleeAt : Std.HashMap Nat (Name × Nat) := {}
    for (c, ois) in iChildren[k]! do
      for oi in ois do
        calleeAt := calleeAt.insert oi (decls[iMem[c]!]!, iOrd[c]!)
    let occArr := p.occurrences.toArray
    let mut newOccs : Array (Provenance.Occurrence NodeId KindRef) := #[]
    for oi in [0:occArr.size] do
      let o := occArr[oi]!
      newOccs := newOccs.push <|
        match o.family with
        | .step _ _ a =>
          if walkedFlags[j]! then
            match calleeAt[oi]? with
            | some (m, ord) => { o with family := .step m (some ord) a }
            | none => o
          else { o with family := .step decls[j]! (some iOrd[k]!) a }
        | _ => o
    let p := { p with occurrences := newOccs.toList }
    let p := p.mapKinds (Provenance.KindRef.subst kmap)
    -- **A configuration port is an address, an argument is a position.** A member's
    -- instances are one member reading one constant, so their config ports carry the
    -- *member's* namespace and only the first instance declares them — the same rule the
    -- signature harvest already keeps within a body, where a constant read twice is one
    -- port and two incidence positions. Three ports for one constant would tell a
    -- deployment to bind it three times, and `Contract.discharges` would count it three
    -- times over. Inputs are not shared: two instances take two data.
    let member := decls[j]!
    let cfgNodes : Array NodeId :=
      p.ports.foldl (init := #[]) fun acc q =>
        if q.dir == .config then acc.push q.node else acc
    let p := p.mapNodes fun n =>
      if cfgNodes.contains n then { n with level := some (.member member) }
      else { n with level := some lvl }
    let (demotedPorts, keptPorts) := p.ports.partition fun q =>
      (q.dir == .input && demoted.contains q.node)
        || (q.dir.produced && demotedOuts.contains q.node)
        || (q.dir == .config && demotedCfg.contains q.node)
    let keptPorts := keptPorts.filter fun q =>
      q.dir != .config || !declaredCfg.contains q.node
    for q in keptPorts do
      if q.dir == .config then declaredCfg := declaredCfg.push q.node
    let p := { p with
      ports := keptPorts
      intros := demotedPorts.map (fun q => ⟨q.node, q.kind, .derived⟩) ++ p.intros }
    let nsUnk := unks[j]!.map fun u => { u with node := s!"{name}/{u.node}" }
    let nsLks := (lks[j]!.map fun (s, t) =>
        (s!"{name}/{s}", { t with level := some lvl })).filter
      fun (_, t) => (p.kindOf? t).isSome
    levels := levels.push ⟨decls[j]!, name, lvl, walkedFlags[j]!, p, srcs[j]!, nsUnk, nsLks⟩
    graph := graph.union p
  graph := graph.union ⟨[], [], wires.toList ++ cfgWires.toList, []⟩
  -- the citation relation: which member's value references which
  let mut cites : Array (Name × Name) := #[]
  for i in [0:decls.size] do
    let d := decls[i]!
    let others : NameSet :=
      (decls.filter (· != d)).foldl (init := {}) (·.insert ·)
    if let some v := (env.find? d).bind (·.value?) then
      -- every reference counts here, dissected heads included: the citation relation is
      -- who mentions whom, not who ports what
      for c in configReads others {} v do
        if let some j := decls.findIdx? (· == c) then
          -- unless the walk *wired* it: a citation is a reference the graph could not
          -- carry, and one that became an identity wire is carried
          unless wiredCite.contains (i, j) do
            cites := cites.push (decls[i]!, decls[j]!)
  return { levels, graph, cites }

/-- Render one graph occurrence in the wired grammar: the edge equation over the kinds
its operands state, the incidence, the result node. -/
def renderOccurrence (o : Provenance.Occurrence NodeId KindRef) : String :=
  let names := o.operands.map (renderNode ·.1)
  let eq := o.family.render (o.operands.map (·.2.render)) o.resultKind.render
  s!"{eq} ⟨{String.intercalate ", " names}⟩ ⇒ {renderNode o.result}"

/-- The assembly rendering: each level with its inclusion mode, the union graph's
ports, introductions, occurrences, and exits, the levels' unkinded positions and
flows, the citation relation, and the evaluated verdict. -/
def Assembly.renderLines (a : Assembly) : List String :=
  (a.levels.toList.map fun l =>
      s!"level {l.name}: {if l.walked then "walked" else "interface"}")
    ++ a.graph.ports.map renderPort
    ++ a.graph.intros.map renderIntro
    ++ a.graph.occurrences.map renderOccurrence
    ++ a.graph.exits.map (fun n => s!"exit {renderNode n}")
    ++ (a.levels.toList.flatMap fun l => l.unkinded.map renderUnkinded)
    ++ (a.levels.toList.flatMap fun l => l.leaks.map renderLeak)
    ++ a.cites.toList.map (fun (x, y) =>
        s!"cites: {lastComponent x} → {lastComponent y}")
    ++ [s!"well-formed: {a.graph.wellFormed}"]

/-! ## Reflection — the harvested graph as a term, for the kernel

`Provenance NodeId KindRef` reflected as an `Expr` literal, so `#kind_graph_decide` can
state `WellFormed` on the constructed object and have the kernel reduce the checker —
"the kernel checks the wiring", literally, on harvested graphs and not only hand-authored
ones. -/

private def nodeIdE : Expr := mkConst ``Provenance.NodeId
private def kindRefE : Expr := mkConst ``Provenance.KindRef

/-- `KindRef` as a term. Hand-recursive because the nested `List` defeats a derived
instance the same way it defeats derived `BEq`. -/
private partial def kindRefToExpr : KindRef → Expr
  | .decl n => mkApp (mkConst ``Provenance.KindRef.decl) (toExpr n)
  | .param b => mkApp (mkConst ``Provenance.KindRef.param) (toExpr b)
  | .sig cs => mkApp (mkConst ``Provenance.KindRef.sig) (listE cs)
  | .tuple cs => mkApp (mkConst ``Provenance.KindRef.tuple) (listE cs)
  | .unkinded => mkConst ``Provenance.KindRef.unkinded
  | .rendered s => mkApp (mkConst ``Provenance.KindRef.rendered) (toExpr s)
where
  listE (cs : List KindRef) : Expr :=
    cs.foldr (init := mkApp (mkConst ``List.nil [levelZero]) kindRefE) fun c acc =>
      mkApp3 (mkConst ``List.cons [levelZero]) kindRefE (kindRefToExpr c) acc

instance : ToExpr KindRef where
  toTypeExpr := kindRefE
  toExpr := kindRefToExpr

instance : ToExpr NodeRef where
  toTypeExpr := mkConst ``Provenance.NodeRef
  toExpr
    | .binder n => mkApp (mkConst ``Provenance.NodeRef.binder) (toExpr n)
    | .letBound n => mkApp (mkConst ``Provenance.NodeRef.letBound) (toExpr n)
    | .result c => mkApp (mkConst ``Provenance.NodeRef.result) (toExpr c)
    | .const n => mkApp (mkConst ``Provenance.NodeRef.const) (toExpr n)
    | .fresh n => mkApp (mkConst ``Provenance.NodeRef.fresh) (toExpr n)
    | .unresolved r => mkApp (mkConst ``Provenance.NodeRef.unresolved) (toExpr r)

instance : ToExpr Provenance.Level where
  toTypeExpr := mkConst ``Provenance.Level
  toExpr
    | .inst m k => mkApp2 (mkConst ``Provenance.Level.inst) (toExpr m) (toExpr k)
    | .member m => mkApp (mkConst ``Provenance.Level.member) (toExpr m)

instance : ToExpr NodeId where
  toTypeExpr := nodeIdE
  toExpr n := mkApp3 (mkConst ``Provenance.NodeId.mk)
    (toExpr n.level) (toExpr n.root) (toExpr n.path)

instance : ToExpr PortDir where
  toTypeExpr := mkConst ``Provenance.PortDir
  toExpr
    | .input => mkConst ``Provenance.PortDir.input
    | .config => mkConst ``Provenance.PortDir.config
    | .param => mkConst ``Provenance.PortDir.param
    | .output => mkConst ``Provenance.PortDir.output
    | .conditional => mkConst ``Provenance.PortDir.conditional

instance : ToExpr IntroTier where
  toTypeExpr := mkConst ``Provenance.IntroTier
  toExpr
    | .derived => mkConst ``Provenance.IntroTier.derived
    | .gated => mkConst ``Provenance.IntroTier.gated
    | .attested r => mkApp (mkConst ``Provenance.IntroTier.attested) (toExpr r)

instance : ToExpr EdgeFamily where
  toTypeExpr := mkConst ``Provenance.EdgeFamily
  toExpr
    | .product => mkConst ``Provenance.EdgeFamily.product
    | .quotient => mkConst ``Provenance.EdgeFamily.quotient
    | .reciprocal => mkConst ``Provenance.EdgeFamily.reciprocal
    | .transcendental => mkConst ``Provenance.EdgeFamily.transcendental
    | .power p => mkApp (mkConst ``Provenance.EdgeFamily.power) (toExpr p)
    | .reference => mkConst ``Provenance.EdgeFamily.reference
    | .additive => mkConst ``Provenance.EdgeFamily.additive
    | .tableMul => mkConst ``Provenance.EdgeFamily.tableMul
    | .tableDiv => mkConst ``Provenance.EdgeFamily.tableDiv
    | .copy => mkConst ``Provenance.EdgeFamily.copy
    | .step m i a =>
      mkApp3 (mkConst ``Provenance.EdgeFamily.step) (toExpr m) (toExpr i) (toExpr a)
    | .select n => mkApp (mkConst ``Provenance.EdgeFamily.select) (toExpr n)

instance : ToExpr (Port NodeId KindRef) where
  toTypeExpr := mkApp2 (mkConst ``Provenance.Port) nodeIdE kindRefE
  toExpr p := mkApp5 (mkConst ``Provenance.Port.mk) nodeIdE kindRefE
    (toExpr p.node) (toExpr p.kind) (toExpr p.dir)

instance : ToExpr (Intro NodeId KindRef) where
  toTypeExpr := mkApp2 (mkConst ``Provenance.Intro) nodeIdE kindRefE
  toExpr i := mkApp5 (mkConst ``Provenance.Intro.mk) nodeIdE kindRefE
    (toExpr i.node) (toExpr i.kind) (toExpr i.tier)

instance : ToExpr (Occurrence NodeId KindRef) where
  toTypeExpr := mkApp2 (mkConst ``Provenance.Occurrence) nodeIdE kindRefE
  toExpr o := mkApp8 (mkConst ``Provenance.Occurrence.mk) nodeIdE kindRefE
    (toExpr o.family) (toExpr o.operands) (toExpr o.result) (toExpr o.resultKind)
    (toExpr o.site) (toExpr o.op)

instance : ToExpr (Provenance NodeId KindRef) where
  toTypeExpr := mkApp2 (mkConst ``PropertyKindCalculus.Provenance) nodeIdE kindRefE
  toExpr g := mkApp6 (mkConst ``PropertyKindCalculus.Provenance.mk) nodeIdE kindRefE
    (toExpr g.ports) (toExpr g.intros) (toExpr g.occurrences) (toExpr g.exits)

/-! ## The declared boundary — reading a contract, rendering the comparison

A contract is an ordinary declaration, so the commands take its *name* and state the
kernel proposition on that constant: what the kernel checks is the author's definition,
never a copy of it. The value is additionally read out — by evaluation — so a
disagreement can be *rendered* as the two difference lists instead of a `decide`
failure. The split is deliberate: evaluation informs the message, the kernel carries the
claim. -/

private unsafe def evalContractUnsafe (e : Expr) :
    MetaM (Provenance.Contract NodeId KindRef) :=
  Meta.evalExpr (Provenance.Contract NodeId KindRef)
    (mkApp2 (mkConst ``Provenance.Contract) nodeIdE kindRefE) e

/-- The declared contract's value, for rendering the comparison. Replaced at run time by
the evaluator; the safe body stands only where no evaluator is available, and no
proposition rests on it. -/
@[implemented_by evalContractUnsafe]
private def evalContract (_e : Expr) : MetaM (Provenance.Contract NodeId KindRef) :=
  throwError "contract values cannot be read in this environment"

/-- The declared contract's value, with the type check that gives a legible error before
the evaluator is asked for one. -/
def contractValueOf (cname : Name) : MetaM (Provenance.Contract NodeId KindRef) := do
  let want := mkApp2 (mkConst ``Provenance.Contract) nodeIdE kindRefE
  unless ← Meta.isDefEq (← Meta.inferType (mkConst cname)) want do
    throwError "'{cname}' is not a 'Provenance.Contract NodeId KindRef'"
  evalContract (mkConst cname)

/-- The wiring theorem of an assembly, however its scope was named: `d₁.kindAssemblyWf`,
by kernel reduction of the structural checker on the assembled object. Errors out —
before troubling the kernel — when the assembly is not well-formed. -/
def assemblyWfDecl (a : Assembly) : Elab.TermElabM Unit := do
  unless a.graph.wellFormed do
    throwError "the kind assembly is not well-formed — render it with #kind_assembly"
  let prop ← Meta.mkAppM ``Provenance.WellFormed #[toExpr a.graph]
  let proof ← Meta.mkDecideProof prop
  let name := a.levels[0]!.decl ++ `kindAssemblyWf
  addDecl (.thmDecl { name, levelParams := [], type := prop, value := proof })
  Lean.logInfo m!"kernel-accepted: the kind assembly is well-formed (theorem '{name}')"

/-- The scope a contract declares, as the assembly its members compute. The one place a
member list becomes a graph, so a probe and a figure generator that name the same
contract are looking at the same object. -/
def assembleContract (c : Provenance.Contract NodeId KindRef) : MetaM Assembly := do
  if c.members.isEmpty then
    throwError "the contract '{c.name}' declares no members"
  let env ← getEnv
  let decls ← c.members.toArray.mapM fun n => do
    unless env.contains n do
      throwError "the contract '{c.name}' names '{n}', which is not a declaration"
    pure n
  assemble decls

/-- The boundary comparison as lines: the contract's name, its parameters — the
obligations it hands to the tier below — and then either agreement or the two difference
lists, an undeclared port being a boundary the graph has and the contract does not, an
unrealized one the reverse. -/
def renderContractLines (c : Provenance.Contract NodeId KindRef)
    (g : Provenance NodeId KindRef) : List String :=
  let params := c.params
  [s!"contract '{c.name}': {c.ports.length} ports, {c.exits.length} exits"]
    ++ (if params.isEmpty then [] else
        [s!"params: {String.intercalate ", " (params.map renderNode)}"])
    ++ c.deciders.map (fun (n, d) => s!"decides {renderNode n}: {d}")
    ++ c.aggregations.map (fun (n, a) => s!"aggregates {renderNode n}: {a.label}")
    ++ c.suppliers.map (fun (n, s) => s!"supplies {renderNode n}: {s}")
    ++ (if c.declaresUniquely then [] else ["declared twice: the contract repeats a node"])
    ++ (c.undeclared g).map (fun p => s!"undeclared {renderPort p}")
    ++ (c.unrealized g).map (fun p => s!"unrealized {renderPort p}")
    ++ (c.undeclaredExits g).map (fun n => s!"undeclared exit {renderNode n}")
    ++ (c.unrealizedExits g).map (fun n => s!"unrealized exit {renderNode n}")
    ++ [s!"boundary agrees: {c.agrees g}"]

/-- The tier comparison as lines: what the deploying contract did with each parameter it
inherited — `bound` where the wider scope feeds it, `restated` where it is passed on —
followed by whatever is unanswered, then the verdict. Two declarations, no graph. -/
def renderDischargeLines (c d : Provenance.Contract NodeId KindRef) : List String :=
  [s!"tier '{c.name}' over '{d.name}': {d.members.length} members inherited, \
     {d.params.length} parameters"]
    ++ (c.bound d).map (fun n => s!"bound {renderNode n}")
    ++ (c.params.filter (d.params.contains ·)).map (fun n => s!"restated {renderNode n}")
    ++ (c.unscoped d).map (fun m => s!"outside the scope: {m}")
    ++ (c.undischarged d).map (fun n => s!"undischarged {renderNode n}")
    ++ (c.droppedExits d).map (fun n => s!"dropped exit {renderNode n}")
    ++ [s!"discharges: {c.discharges d}"]

/-! ## The commands — four renderings of one producer -/

open Elab Command in
/-- `#kind_occurrences d` prints every authored license discharged inline in `d`'s
value — each consuming application's edge with the operand quantities that met there, in
body order, with multiplicity — as a single `info` message suitable for `#guard_msgs`
pinning. Assumed occurrences (hypothesis- or instance-binder licenses), identity
wires, and procedure edges are the graph's and the assembly's business, not the
enumeration's. -/
elab "#kind_occurrences " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let occs := (← stepGraphOf decl).occs.filter fun o =>
    !o.assumed && !(o.occ.family matches .copy) && !(o.occ.family matches .step _ _ _)
  if occs.isEmpty then
    logInfo m!"no inline kind occurrences in '{decl}'"
  else
    let lines := occs.toList.map (·.render)
    logInfo m!"inline kind occurrences in '{decl}':\n{String.intercalate "\n" lines}"

open Elab Command in
/-- `#kind_ports d` prints every port `d`'s kind-typed signature states — inputs,
configuration reads, outputs, each with its stated kind — followed by the signature's
unkinded positions, red in the figure (module header, "Unkinded positions"), as a
single `info` message suitable for `#guard_msgs` pinning. -/
elab "#kind_ports " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let g ← stepGraphOf decl
  let lines := g.ports.map renderPort ++ g.unkinded.map renderUnkinded
  if lines.isEmpty then
    logInfo m!"no kind ports in '{decl}'"
  else
    logInfo m!"kind ports of '{decl}':\n{String.intercalate "\n" lines}"

open Elab Command in
/-- `#kind_graph d` prints the constructed step graph — ports, introduction events,
wired occurrences (with `assumed`/`partial` markers), exits — and the evaluated
well-formedness verdict, as a single `info` message suitable for `#guard_msgs`
pinning. -/
elab "#kind_graph " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let g ← stepGraphOf decl
  logInfo m!"kind graph of '{decl}':\n{String.intercalate "\n" g.renderLines}"

open Elab Command in
/-- `#kind_graph_decide d` reflects the constructed graph into a term and adds the
theorem `d.kindGraphWf : (graph).WellFormed`, proved by `decide` — kernel reduction of
the structural checker on the harvested object. Errors out (before troubling the
kernel) when the graph is not well-formed. -/
elab "#kind_graph_decide " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let g := (← stepGraphOf decl).provenance
  unless g.wellFormed do
    throwError "the kind graph of '{decl}' is not well-formed — render it with #kind_graph"
  let prop ← Meta.mkAppM ``Provenance.WellFormed #[toExpr g]
  let proof ← Meta.mkDecideProof prop
  let name := decl ++ `kindGraphWf
  addDecl (.thmDecl { name, levelParams := [], type := prop, value := proof })
  logInfo m!"kernel-accepted: the kind graph of '{decl}' is well-formed (theorem '{name}')"

open Elab Command in
/-- `#kind_assembly [d₁, d₂, …]` assembles the listed declarations into one multi-step
graph (module section, "The assembly") and prints it — each level with its inclusion
mode, the union graph, the citation relation, and the evaluated verdict — as a single
`info` message suitable for `#guard_msgs` pinning. -/
elab "#kind_assembly " "[" ids:ident,* "]" : command => liftTermElabM do
  let decls ← ids.getElems.mapM fun id => realizeGlobalConstNoOverload id
  if decls.isEmpty then throwError "#kind_assembly expects at least one declaration"
  let a ← assemble decls
  logInfo m!"kind assembly of {decls.size} steps:\n{String.intercalate "\n" a.renderLines}"

open Elab Command in
/-- `#kind_assembly c` is the same rendering over the scope a contract declares: the
members come off `c` rather than off the call site, so the graph shown is the one whose
boundary `#kind_contract c` judges, and a scope is spelled once however many readings it
has. -/
elab "#kind_assembly " c:ident : command => liftTermElabM do
  let a ← assembleContract (← contractValueOf (← realizeGlobalConstNoOverload c))
  logInfo m!"kind assembly of {a.levels.size} steps:\n{String.intercalate "\n" a.renderLines}"

/-- A kind reference as paste-able constructor syntax — what `#kind_boundary_syntax`
prints, so a computed boundary can be declared by copying rather than retyped. -/
partial def kindRefSyntax : KindRef → String
  | .decl n => s!".decl ``{n}"
  | .param b => s!".param \"{b}\""
  | .sig cs => ".sig [" ++ String.intercalate ", " (cs.map kindRefSyntax) ++ "]"
  | .tuple cs => ".tuple [" ++ String.intercalate ", " (cs.map kindRefSyntax) ++ "]"
  | .unkinded => ".unkinded"
  | .rendered s => s!".rendered \"{s}\""

/-- A node identifier as paste-able constructor syntax, through the smart
constructors. -/
def nodeIdSyntax (n : NodeId) : String :=
  let base := match n.root with
    | .binder s => s!"(NodeId.binder \"{s}\")"
    | .letBound s => s!"(NodeId.letBound \"{s}\")"
    | .result none => "NodeId.result"
    | .result (some i) => s!"(NodeId.resultAt {i})"
    | .const c => s!"(NodeId.config ``{c})"
    | .fresh i => s!"(NodeId — fresh {i}: graph-interior, not declarable)"
    | .unresolved s => s!"(NodeId — unresolved \"{s}\": not declarable)"
  let withPath := n.path.foldl (fun acc seg => s!"({acc}.field \"{seg}\")") base
  match n.level with
  | some (.inst m 1) => s!"({withPath}.within ``{m})"
  | some (.inst m k) => s!"({withPath}.within ``{m} {k})"
  | some (.member m) => s!"({withPath}.shared ``{m})"
  | none => withPath

open Elab Command in
/-- `#kind_boundary_syntax [d₁, d₂, …]` assembles the listed declarations and prints
the surviving boundary — the ports and exits a `Provenance.Contract` over this scope
must declare — as paste-able constructor syntax, so declaring a boundary is copying
what the machine computed and then owning it, not retyping it. -/
elab "#kind_boundary_syntax " "[" ids:ident,* "]" : command => liftTermElabM do
  let decls ← ids.getElems.mapM fun id => realizeGlobalConstNoOverload id
  if decls.isEmpty then throwError "#kind_boundary_syntax expects at least one declaration"
  let a ← assemble decls
  let memberLines :=
    "  members := [" ++ String.intercalate ", " (decls.toList.map fun d => s!"``{d}") ++ "]"
  let portLines := a.graph.ports.map fun p =>
    s!"    ⟨{nodeIdSyntax p.node}, {kindRefSyntax p.kind}, .{p.dir.label}⟩"
  let exitLines := a.graph.exits.map fun n => s!"    {nodeIdSyntax n}"
  let ports := if portLines.isEmpty then "  ports := []"
    else "  ports := [\n" ++ String.intercalate ",\n" portLines ++ "]"
  let exits := if exitLines.isEmpty then "  exits := []"
    else "  exits := [\n" ++ String.intercalate ",\n" exitLines ++ "]"
  logInfo m!"boundary of this scope, as declarable syntax:\n\
    {memberLines}\n{ports}\n{exits}"

open Elab Command in
/-- `#kind_assembly_decide [d₁, d₂, …]` assembles the listed declarations, reflects
the union graph into a term, and adds the theorem `d₁.kindAssemblyWf :
(graph).WellFormed`, proved by `decide` — kernel reduction of the structural checker
on the assembled multi-step object. Errors out (before troubling the kernel) when the
assembly is not well-formed. -/
elab "#kind_assembly_decide " "[" ids:ident,* "]" : command => liftTermElabM do
  let decls ← ids.getElems.mapM fun id => realizeGlobalConstNoOverload id
  if decls.isEmpty then throwError "#kind_assembly_decide expects at least one declaration"
  let a ← assemble decls
  assemblyWfDecl a

open Elab Command in
/-- `#kind_assembly_decide c` proves the same wiring theorem over the scope a contract
declares — the wiring verdict and the boundary verdict then stand on one member list,
named once. -/
elab "#kind_assembly_decide " c:ident : command => liftTermElabM do
  let a ← assembleContract (← contractValueOf (← realizeGlobalConstNoOverload c))
  assemblyWfDecl a

/-- The decider clause's checks (`Contract.deciders`): each entry names a `conditional`
port of the contract, so a decider cannot be hung on an output that has no cases, and
its decider is a declaration in the environment, so the named predicate cannot dangle. -/
def checkDeciders (c : Provenance.Contract NodeId KindRef) : MetaM Unit := do
  let env ← getEnv
  for (n, d) in c.deciders do
    let some p := c.ports.find? (·.node == n)
      | throwError "the decider for '{renderNode n}' names no port of '{c.name}'"
    unless p.dir == .conditional do
      throwError "the decider for '{renderNode n}' names a port with role \
        '{p.dir.label}' — only a conditional port has cases to decide"
    unless (env.find? d).isSome do
      throwError "the decider '{d}' for '{renderNode n}' is not a declaration"

/-- The aggregation clause's checks (`Contract.aggregations`): each entry names a
*produced* port of the contract — an aggregation class says how a value the module
hands out composes, so a source port has none — and each name the class carries
answers for itself. A quasi-extensive tolerance is a declaration whose type is a
`Quantity` at the governed port's kind, because a per-join discrepancy is a quantity
of what the port produces, not a bare number; a named condition, sortal, transport,
or cancellation law is a declaration in the environment. What the checks do not
adjudicate is the truth of the class — like an `Assembles` entry it is the author's
curated claim, and `Recarving.distribution_license` is what an extensive claim buys
while `assemble_ne_measured` is what a wrong one costs. -/
def checkAggregations (c : Provenance.Contract NodeId KindRef) : MetaM Unit := do
  let env ← getEnv
  for (n, cls) in c.aggregations do
    let some p := c.ports.find? (·.node == n)
      | throwError "the aggregation class for '{renderNode n}' names no port of '{c.name}'"
    unless p.dir.produced do
      throwError "the aggregation class for '{renderNode n}' names a port with role \
        '{p.dir.label}' — an aggregation class says how a produced value composes, \
        and this port produces nothing"
    match cls with
    | .quasiExtensive tname =>
      let some tinfo := env.find? tname
        | throwError "the tolerance '{tname}' for '{renderNode n}' is not a declaration"
      let tk ← Meta.forallTelescopeReducing tinfo.type fun _ tconcl => do
        unless tconcl.isAppOf ``Quantity do
          throwError "the tolerance '{tname}' for '{renderNode n}' is not a 'Quantity' \
            — a per-join tolerance is a kinded quantity, not a bare number"
        kindRefOf [] (tconcl.getAppArgs[0]!)
      unless p.kind == tk do
        throwError "the tolerance '{tname}' for '{renderNode n}' is a quantity at kind \
          '{tk.render}', which is not the port's kind '{p.kind.render}' — a join's \
          discrepancy is a quantity of what the port produces"
    | .conditionallyExtensive e | .countKeyed e | .extensiveAbout e
    | .interfaceLicensed e =>
      unless (env.find? e).isSome do
        throwError "the aggregation class for '{renderNode n}' names '{e}', which is \
          not a declaration"
    | .extensive | .intensive | .wholeProper => pure ()

/-- The supplier clause's checks (`Contract.suppliers`): each entry names a port of the
contract whose kind is a *signature* — the `→`-joined module-valued port form, because
a supplier bound to a single-kind port would be a value, not a module — and names a
declaration whose own kind signature, read off its type exactly as the harvest reads a
functional binder (implicit and instance binders filled first, `supplierSignature?`),
is the declared one, component for component. What the checks do not adjudicate is
behavior: two suppliers of one signature agree on the interface, and whether they
agree on values is a `Relation` edge's theorem to carry, not a port list's. -/
def checkSuppliers (c : Provenance.Contract NodeId KindRef) : MetaM Unit := do
  let env ← getEnv
  let carriers := operandCarriers env
  for (n, s) in c.suppliers do
    let some p := c.ports.find? (·.node == n)
      | throwError "the supplier for '{renderNode n}' names no port of '{c.name}'"
    unless p.kind matches .sig _ do
      throwError "the supplier for '{renderNode n}' names a port at kind \
        '{p.kind.render}' — only a module-valued port (a signature kind) takes a \
        supplier"
    let some sinfo := env.find? s
      | throwError "the supplier '{s}' for '{renderNode n}' is not a declaration"
    let some ssig ← supplierSignature? env carriers sinfo.type
      | throwError "the supplier '{s}' for '{renderNode n}' states no kind signature — \
          its explicit arguments are not a function over kinded quantities"
    unless ssig == p.kind do
      throwError "the supplier '{s}' for '{renderNode n}' states the signature \
        '{ssig.render}', which is not the port's '{p.kind.render}' — binding a module \
        of a different signature re-types the argument"

open Elab Command in
/-- `#kind_contract c` assembles the members the contract `c` declares and compares that
assembly's boundary with the boundary `c` declares — its parameters and decided
conditional ports, then the ports and exits each side has and the other does not, then
the verdict — as a single `info` message suitable for `#guard_msgs` pinning. This is the
scope reading: `#kind_assembly` says whether the wiring holds together, and this says
whether the members are the ones the declared interface belongs to. -/
elab "#kind_contract " c:ident : command => liftTermElabM do
  let cname ← realizeGlobalConstNoOverload c
  let ctr ← contractValueOf cname
  checkDeciders ctr
  checkAggregations ctr
  checkSuppliers ctr
  let a ← assembleContract ctr
  logInfo m!"kind contract over {ctr.members.length} steps:\n\
    {String.intercalate "\n" (renderContractLines ctr a.graph)}"

open Elab Command in
/-- `#kind_contract_decide c` assembles the members the contract `c` declares, reflects
the union graph into a term, and adds the theorem `c.kindContractOk : c.Agrees (graph)`,
proved by `decide` — kernel reduction of the boundary comparison against the author's own
contract definition, which the proposition names rather than copies. Errors out (before
troubling the kernel) when the boundaries disagree, printing the difference lists. -/
elab "#kind_contract_decide " c:ident : command => liftTermElabM do
  let cname ← realizeGlobalConstNoOverload c
  let ctr ← contractValueOf cname
  checkDeciders ctr
  checkAggregations ctr
  checkSuppliers ctr
  let a ← assembleContract ctr
  unless ctr.agrees a.graph do
    throwError "the boundary declared by '{cname}' is not the one its members compute:\n\
      {String.intercalate "\n" (renderContractLines ctr a.graph)}"
  let prop ← Meta.mkAppM ``Provenance.Contract.Agrees #[mkConst cname, toExpr a.graph]
  let proof ← Meta.mkDecideProof prop
  let name := cname ++ `kindContractOk
  addDecl (.thmDecl { name, levelParams := [], type := prop, value := proof })
  logInfo m!"kernel-accepted: '{cname}' is the boundary of its {ctr.members.length}-step \
    assembly (theorem '{name}')"

/-- The subjects of a contract sweep: every constant under the given namespace prefixes
whose type is headed by `Provenance.Contract` (headed by, not equal to — the type takes
its two parameters), split into the checked and the `@[kindCounterexample]`-exempted,
each sorted by name. Enrollment is by type, so declaring a boundary is enrolling it —
the sweeps cannot be evaded by forgetting a command, and only the exemption is an
authored mark, which is the side of the asymmetry a build catches when forgotten. -/
def contractSweepSubjects (scopes : Array Name) : Elab.TermElabM (Array Name × Array Name) := do
  let env ← getEnv
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut names : Array Name := #[]
  let mut exempted : Array Name := #[]
  for (n, info) in env.constants.toList do
    if n.isInternal then continue
    unless scopes.any (·.isPrefixOf n) do continue
    if info.type.getAppFn.isConstOf ``Provenance.Contract then
      if exempt.contains n then exempted := exempted.push n
      else names := names.push n
  return (names.qsort (fun a b => a.toString < b.toString),
          exempted.qsort (fun a b => a.toString < b.toString))

open Elab Command in
/-- `#kind_contracts ns…` — the boundary survey: every `Provenance.Contract` declared
under the given namespaces, re-checked exactly as `#kind_contract` checks one — the
decider, aggregation, and supplier clauses, then the declared boundary against the one
the members compute — rendered one line per contract in declaration-name order as a
single `info` message suitable for `#guard_msgs` pinning. Membership is by type, so a
boundary cannot be declared and left out of the sweep. A contract that fails renders as
a `✗` row carrying the refusal, so the pin is the gate; a `@[kindCounterexample]`-tagged
declaration renders as a `⊘` row and is not checked, so a falsification probe can stand
beside the gate it exercises. The header counts the contracts, the violations, and the
exemptions, so a scope with none pins `0` rather than passing invisibly. The check is
context-free: a boundary's references resolve in the environment, so the sweep needs no
namespace replay and no `open`s from anywhere. -/
elab "#kind_contracts " nss:ident* : command => liftTermElabM do
  if nss.isEmpty then
    throwError "#kind_contracts expects at least one namespace"
  let (names, exempted) ← contractSweepSubjects (nss.map (·.getId))
  let mut lines : Array String := #[]
  let mut violated := 0
  for n in names do
    let res : Except String String ←
      try
          let ctr ← contractValueOf n
          checkDeciders ctr
          checkAggregations ctr
          checkSuppliers ctr
          let a ← assembleContract ctr
          if ctr.agrees a.graph then
            pure (.ok s!"'{ctr.name}' — {ctr.ports.length} ports, \
              {ctr.exits.length} exits, {ctr.members.length} member step(s)")
          else
            let diffs :=
              (ctr.undeclared a.graph).map (fun p => s!"undeclared {renderPort p}")
                ++ (ctr.unrealized a.graph).map (fun p => s!"unrealized {renderPort p}")
                ++ (ctr.undeclaredExits a.graph).map
                    (fun x => s!"undeclared exit {renderNode x}")
                ++ (ctr.unrealizedExits a.graph).map
                    (fun x => s!"unrealized exit {renderNode x}")
                ++ (if ctr.declaresUniquely then [] else ["declared twice"])
            pure (.error s!"'{ctr.name}' — {String.intercalate "; " diffs}")
      catch e => pure (.error (← e.toMessageData.toString))
    match res with
    | .ok row => lines := lines.push s!"  {n}: {row}"
    | .error row =>
      violated := violated + 1
      lines := lines.push s!"  ✗ {n}: {row}"
  for n in exempted do
    lines := lines.push s!"  ⊘ {n}: counterexample, exempted"
  let violations := if violated == 0 then "" else s!", {violated} violated"
  let exemptions := if exempted.isEmpty then "" else s!", {exempted.size} exempted"
  let summary := s!"kind contracts — {names.size + exempted.size} \
    contract(s){violations}{exemptions}"
  if lines.isEmpty then logInfo m!"{summary}"
  else logInfo m!"{summary}\n{String.intercalate "\n" lines.toList}"
  recordAuditReceipt "kind_contracts" (nss.map (·.getId))

open Elab Command in
/-- `#kind_contracts_decide ns…` — the sweep as a hard gate with kernel receipts: every
`Provenance.Contract` under the given namespaces is checked as `#kind_contract_decide`
checks one, and every violation throws — there is no reading of this command that states
one. Each passing contract gains the kernel theorem `c.kindContractOk : c.Agrees (graph)`
unless that theorem already stands (added by a per-name `#kind_contract_decide` upstream,
or by an earlier sweep — the sweep is idempotent across layers, and the row says which).
`@[kindCounterexample]`-tagged declarations are skipped and counted. -/
elab "#kind_contracts_decide " nss:ident* : command => liftTermElabM do
  if nss.isEmpty then
    throwError "#kind_contracts_decide expects at least one namespace"
  let (names, exempted) ← contractSweepSubjects (nss.map (·.getId))
  let mut lines : Array String := #[]
  for n in names do
    let a ← do
        let ctr ← contractValueOf n
        checkDeciders ctr
        checkAggregations ctr
        checkSuppliers ctr
        let a ← assembleContract ctr
        unless ctr.agrees a.graph do
          throwError "the boundary declared by '{n}' is not the one its members compute:\n\
            {String.intercalate "\n" (renderContractLines ctr a.graph)}"
        pure a
    let thmName := n ++ `kindContractOk
    if (← getEnv).contains thmName then
      lines := lines.push s!"  {n}: theorem '{thmName}' already stands"
    else
      let prop ← Meta.mkAppM ``Provenance.Contract.Agrees #[mkConst n, toExpr a.graph]
      let proof ← Meta.mkDecideProof prop
      addDecl (.thmDecl { name := thmName, levelParams := [], type := prop, value := proof })
      lines := lines.push s!"  {n}: kernel-accepted (theorem '{thmName}')"
  for n in exempted do
    lines := lines.push s!"  ⊘ {n}: counterexample, exempted"
  let exemptions := if exempted.isEmpty then "" else s!", {exempted.size} exempted"
  let summary := s!"kind contracts — {names.size} contract(s) kernel-accepted{exemptions}"
  if lines.isEmpty then logInfo m!"{summary}"
  else logInfo m!"{summary}\n{String.intercalate "\n" lines.toList}"
  -- The decide sweep is the report sweep with kernel receipts, so it discharges both: a
  -- document that runs only the stronger form must not read `partial` for the weaker.
  recordAuditReceipt "kind_contracts_decide" (nss.map (·.getId))
  recordAuditReceipt "kind_contracts" (nss.map (·.getId))

open Elab Command in
/-- `#kind_discharges c d` compares two contracts — no graph, no harvest: what the
deploying contract `c` did with each parameter the deployed contract `d` handed it, and
whether anything was left unanswered. -/
elab "#kind_discharges " c:ident d:ident : command => liftTermElabM do
  let ctr ← contractValueOf (← realizeGlobalConstNoOverload c)
  let inner ← contractValueOf (← realizeGlobalConstNoOverload d)
  logInfo m!"kind tier:\n{String.intercalate "\n" (renderDischargeLines ctr inner)}"

open Elab Command in
/-- `#kind_discharges_decide c d` adds the theorem `c.kindDischarges.d : c.Discharges d`,
proved by `decide` — kernel reduction of the tier relation on the two authors' own
contract definitions, which the proposition names rather than copies. Errors out (before
troubling the kernel) when the tiers do not stack, printing what is unanswered. -/
elab "#kind_discharges_decide " c:ident d:ident : command => liftTermElabM do
  let cname ← realizeGlobalConstNoOverload c
  let dname ← realizeGlobalConstNoOverload d
  let ctr ← contractValueOf cname
  let inner ← contractValueOf dname
  unless ctr.discharges inner do
    throwError "'{cname}' does not discharge '{dname}':\n\
      {String.intercalate "\n" (renderDischargeLines ctr inner)}"
  let prop ← Meta.mkAppM ``Provenance.Contract.Discharges #[mkConst cname, mkConst dname]
  let proof ← Meta.mkDecideProof prop
  let name := cname ++ `kindDischarges ++ .mkSimple (dname.getString!)
  addDecl (.thmDecl { name, levelParams := [], type := prop, value := proof })
  logInfo m!"kernel-accepted: '{cname}' discharges '{dname}' (theorem '{name}')"
  recordAuditReceipt "kind_discharges_decide" #[cname, dname]


/-! ## The theorem edge (`Provenance`, "The theorem edge")

A `Relation` names two contracts, what a theorem claims of them, and the theorem. None
of that is decidable, so nothing here is reflected into a kernel proposition — the
witness already *is* one. What this checks is everything around it, and it throws rather
than reporting, so the pin cannot express a violation and needs no separate gate. -/

private unsafe def evalRelationUnsafe (e : Expr) : MetaM Provenance.Relation :=
  Meta.evalExpr Provenance.Relation (mkConst ``Provenance.Relation) e

/-- The declared relation's value. Replaced at run time by the evaluator; the safe body
stands only where no evaluator is available. -/
@[implemented_by evalRelationUnsafe]
private def evalRelation (_e : Expr) : MetaM Provenance.Relation :=
  throwError "relation values cannot be read in this environment"

/-- The declared relation's value, with the type check that gives a legible error before
the evaluator is asked for one. -/
def relationValueOf (rname : Name) : MetaM Provenance.Relation := do
  unless ← Meta.isDefEq (← Meta.inferType (mkConst rname)) (mkConst ``Provenance.Relation) do
    throwError "'{rname}' is not a 'Provenance.Relation'"
  evalRelation (mkConst rname)

/-- The members of a contract that a statement mentions by name. This is the check that
keeps a theorem edge from being decoration: a theorem naming neither boundary is a true
statement about something else. -/
def mentionedMembers (c : Provenance.Contract NodeId KindRef) (mentions : NameSet) :
    List Name :=
  c.members.filter fun m => mentions.contains m

/-- The result of checking one theorem edge: the evaluated relation, the two boundary
names as their contracts render them, and the report body — everything below the header
line, one entry per rendered line. -/
structure CheckedRelation where
  rel : Provenance.Relation
  leftName : String
  rightName : String
  lines : List String

/-- The full check of one theorem edge — `#kind_relation`'s body, named so the survey
command re-runs it per edge. Checks, throwing on the first violation: the witness is a
theorem (not a definition, not an axiom); its axiom profile carries no `sorryAx`; its
conclusion has the shape the claimed kind names (`equals` an `Eq`; `boundedBy` an order
relation; `inverts` an `Eq` one of whose sides composes members of both boundaries;
`refines` an `Eq` under at least one bound hypothesis); a named `tolerance` is a
declaration whose type is a `Quantity` at the kind of an output port of the left
boundary; every named hypothesis is a declaration the witness statement mentions; every
license rung names a sorry-free theorem as its repair or restatement; a named
`wellPosed` is a sorry-free theorem concluding with `∃!`, on an `inverts` edge only,
accompanied by the `domain` declaration its statement mentions; a named `ambiguity` is a
sorry-free theorem concluding with the negation of an `∃!`, on an `inverts` edge only;
and the statement mentions at least one member of *each* boundary. -/
def checkRelation (rname : Name) : MetaM CheckedRelation := do
  let rel ← relationValueOf rname
  let env ← getEnv
  let left ← contractValueOf rel.left
  let right ← contractValueOf rel.right
  let wname := rel.witness
  let some info := env.find? wname
    | throwError "the witness '{rel.witness}' is not a declaration"
  unless info matches .thmInfo _ do
    throwError "the witness '{wname}' is not a theorem — a relation between two \
      boundaries is carried by a proof, and a definition asserts nothing"
  let axs ← Lean.collectAxioms wname
  if axs.contains ``sorryAx then
    throwError "the witness '{wname}' depends on 'sorryAx' — it proves nothing yet"
  -- the shape of the conclusion, where the claimed kind names one. Checked *inside* the
  -- telescope: outside it the statement's own binders have left scope and the message
  -- would name them as raw metavariables
  Meta.forallTelescopeReducing info.type fun fvars concl => do
    -- the head symbol, not the rendered conclusion: what the claim is about is the
    -- relation the statement concludes with, and a pretty-printed statement wraps at a
    -- width nothing here controls
    let head := match concl.getAppFn with
      | .const c _ => toString c
      | _ => "no constant"
    -- does an expression mention a member of the contract — the per-side reading of
    -- `mentionedMembers`, for the round-trip check
    let mentionsMemberOf (e : Expr) (c : Provenance.Contract NodeId KindRef) : Bool :=
      let ms := e.foldConsts ({} : NameSet) fun cn s => s.insert cn
      !(mentionedMembers c ms).isEmpty
    match rel.kind with
    | .equals =>
      unless concl.isAppOf ``Eq do
        throwError "'{wname}' is claimed to state an equality, but its conclusion is \
          headed by '{head}', not 'Eq'"
    | .boundedBy =>
      unless concl.isAppOf ``LE.le || concl.isAppOf ``LT.lt do
        throwError "'{wname}' is claimed to state a bound, but its conclusion is headed \
          by '{head}', which is not an order relation"
    | .inverts =>
      unless concl.isAppOf ``Eq do
        throwError "'{wname}' is claimed to state an inversion, but its conclusion is \
          headed by '{head}', not 'Eq' — an inversion is a round-trip equality"
      let args := concl.getAppArgs
      let dflt := mkConst ``Unit
      let sides := [args.getD (args.size - 2) dflt, args.getD (args.size - 1) dflt]
      unless sides.any fun e => mentionsMemberOf e left && mentionsMemberOf e right do
        throwError "'{wname}' is claimed to state an inversion, but neither side of its \
          equality composes a member of '{left.name}' with a member of '{right.name}' — \
          the round trip is not in the statement"
    | .refines =>
      unless concl.isAppOf ``Eq do
        throwError "'{wname}' is claimed to state a refinement, but its conclusion is \
          headed by '{head}', not 'Eq' — a refinement answers with the same value"
      let hasHyp ← fvars.anyM fun fv => do Meta.isProp (← fv.fvarId!.getType)
      unless hasHyp do
        throwError "'{wname}' is claimed to hold under a stated hypothesis, but its \
          statement binds none — a refinement with no hypothesis is an equality claim"
  -- the tolerance: a bound is governed by a kinded quantity at a produced port's kind,
  -- not by a bare number in prose
  let mut toleranceLines : List String := []
  unless rel.tolerance.isAnonymous do
    let tname := rel.tolerance
    let some tinfo := env.find? tname
      | throwError "the tolerance '{rel.tolerance}' is not a declaration"
    let tk ← Meta.forallTelescopeReducing tinfo.type fun _ tconcl => do
      unless tconcl.isAppOf ``Quantity do
        throwError "the tolerance '{tname}' is not a 'Quantity' — a tolerance is a \
          kinded quantity, not a bare number"
      kindRefOf [] (tconcl.getAppArgs[0]!)
    let outKinds := (left.ports.filter (·.dir.produced)).map (·.kind)
    unless outKinds.contains tk do
      throwError "the tolerance '{tname}' is a quantity at kind '{tk.render}', which \
        is not the kind of any output port of '{left.name}' — a bound governs what the \
        boundary produces"
    toleranceLines := [s!"tolerance: {tname} : {tk.render}"]
  -- the named side conditions: each a declaration the witness statement mentions, so
  -- the listed domain is the stated one
  let mentions := info.type.foldConsts ({} : NameSet) fun c s => s.insert c
  let mut hypothesisLines : List String := []
  unless rel.hypotheses.isEmpty do
    for hn in rel.hypotheses do
      unless (env.find? hn).isSome do
        throwError "the hypothesis '{hn}' is not a declaration"
      unless mentions.contains hn do
        throwError "'{wname}' does not mention the hypothesis '{hn}' — a side condition \
          the statement does not state is not one the claim holds under"
    hypothesisLines :=
      [s!"hypotheses: {String.intercalate ", " (rel.hypotheses.map toString)}"]
  -- the license clause: each rung answered for by a named, sorry-free theorem — a rung
  -- claimed with no repair and no restatement is refused, because a side condition does
  -- not transfer by being assumed to
  let mut licenseLines : List String := []
  for l in rel.licenses do
    if l.rung.isEmpty then
      throwError "a license names the carrier rung it extends the claim to; one rung \
        was left empty"
    let ev := l.transfer.evidence
    if ev.isAnonymous then
      throwError "the license at rung '{l.rung}' claims the relation with no repair and \
        no restatement — name the repair theorem that carries it across, or the witness \
        that restates it at that rung"
    let en := ev
    let some einfo := env.find? en
      | throwError "the license at rung '{l.rung}' names '{ev}', which is not a \
          declaration"
    unless einfo matches .thmInfo _ do
      throwError "the license at rung '{l.rung}' names '{en}', which is not a theorem \
        — a transfer is carried by a proof"
    let eaxs ← Lean.collectAxioms en
    if eaxs.contains ``sorryAx then
      throwError "the license at rung '{l.rung}' rests on '{en}', which depends on \
        'sorryAx' — it proves nothing yet"
    licenseLines := licenseLines ++ [s!"license: {l.label}"]
  -- the well-posedness clause: an inversion may claim that its answer exists and is
  -- unique, and the claim is proved on a *declared* domain — the witness a sorry-free
  -- theorem concluding with `∃!`, the domain a declaration that statement mentions.
  -- `ExistsUnique` is matched by name, unresolved, so the check needs no import of the
  -- library that defines `∃!`; an environment that can state one has it in scope.
  let headOf (e : Expr) : String := match e.getAppFn with
    | .const c _ => toString c
    | _ => "no constant"
  let mut wellPosedLines : List String := []
  unless rel.wellPosed.isAnonymous do
    unless rel.kind matches .inverts do
      throwError "the edge names a well-posedness witness but claims \
        '{rel.kind.label}' — existence and uniqueness answer an inversion"
    let wpn := rel.wellPosed
    let some wpinfo := env.find? wpn
      | throwError "the well-posedness witness '{rel.wellPosed}' is not a declaration"
    unless wpinfo matches .thmInfo _ do
      throwError "the well-posedness witness '{wpn}' is not a theorem — existence and \
        uniqueness are carried by a proof"
    let wpaxs ← Lean.collectAxioms wpn
    if wpaxs.contains ``sorryAx then
      throwError "the well-posedness witness '{wpn}' depends on 'sorryAx' — it proves \
        nothing yet"
    Meta.forallTelescope wpinfo.type fun _ wpconcl => do
      unless wpconcl.isAppOf `ExistsUnique do
        throwError "'{wpn}' is claimed to prove existence and uniqueness, but its \
          conclusion is headed by '{headOf wpconcl}', not '∃!'"
    if rel.domain.isAnonymous then
      throwError "the well-posedness witness '{wpn}' comes with no domain — existence \
        and uniqueness are proved on a declared domain, so name the box or predicate \
        its statement mentions"
    let dn := rel.domain
    unless (env.find? dn).isSome do
      throwError "the domain '{rel.domain}' is not a declaration"
    let wpMentions := wpinfo.type.foldConsts ({} : NameSet) fun c s => s.insert c
    unless wpMentions.contains dn do
      throwError "'{wpn}' does not mention the domain '{rel.domain}' — the declared \
        domain is the stated one, never wider"
    wellPosedLines := [s!"well-posed: {wpn} on {rel.domain}"]
  if rel.wellPosed.isAnonymous && !rel.domain.isAnonymous then
    throwError "the edge names a domain with no well-posedness witness — the domain is \
      where existence and uniqueness hold, so it accompanies the witness"
  -- the ambiguity clause: where the inversion is not single-valued, the edge surfaces
  -- that as a declaration — a sorry-free theorem concluding with the negation of an
  -- `∃!` — rather than resolving it to whichever root the algorithm reached first
  let mut ambiguityLines : List String := []
  unless rel.ambiguity.isAnonymous do
    unless rel.kind matches .inverts do
      throwError "the edge names an ambiguity witness but claims '{rel.kind.label}' — \
        ambiguity is an inversion's finding"
    let an := rel.ambiguity
    let some ainfo := env.find? an
      | throwError "the ambiguity witness '{rel.ambiguity}' is not a declaration"
    unless ainfo matches .thmInfo _ do
      throwError "the ambiguity witness '{an}' is not a theorem — a surfaced ambiguity \
        is carried by a proof"
    let aaxs ← Lean.collectAxioms an
    if aaxs.contains ``sorryAx then
      throwError "the ambiguity witness '{an}' depends on 'sorryAx' — it proves \
        nothing yet"
    Meta.forallTelescope ainfo.type fun _ aconcl => do
      unless aconcl.isAppOf ``Not && aconcl.appArg!.isAppOf `ExistsUnique do
        throwError "'{an}' is claimed to surface an ambiguity, but its conclusion is \
          headed by '{headOf aconcl}', not the negation of an '∃!' — the uniqueness \
          that fails is what the witness states"
    ambiguityLines := [s!"ambiguity: {an}"]
  let lm := mentionedMembers left mentions
  let rm := mentionedMembers right mentions
  if lm.isEmpty then
    throwError "'{wname}' names no member of '{left.name}' — a theorem that does not \
      mention a boundary is not about it"
  if rm.isEmpty then
    throwError "'{wname}' names no member of '{right.name}' — a theorem that does not \
      mention a boundary is not about it"
  let claim := if rel.claim.isEmpty then [] else [s!"claims: {rel.claim}"]
  return { rel, leftName := left.name, rightName := right.name,
           lines := [s!"witness: {wname}"] ++ claim ++ toleranceLines ++ hypothesisLines
             ++ licenseLines ++ wellPosedLines ++ ambiguityLines
             ++ [s!"names on the left: {String.intercalate ", " (lm.map toString)}",
                 s!"names on the right: {String.intercalate ", " (rm.map toString)}",
                 s!"axioms: {String.intercalate ", " (axs.toList.map toString)}"] }

open Elab Command in
/-- `#kind_relation r` checks the theorem edge `r` declares between two contracts
(`checkRelation` — the witness a sorry-free theorem, the conclusion in the claimed
shape, the optional tolerance/hypothesis/license/well-posedness/ambiguity clauses each
answered for by name, the statement mentioning members of both boundaries) and prints
it. Every failure throws, so the command is the report and the gate at once — there is
no reading of it that states a violation. -/
elab "#kind_relation " r:ident : command => liftTermElabM do
  let c ← checkRelation (← realizeGlobalConstNoOverload r)
  logInfo m!"kind relation: '{c.leftName}' {c.rel.kind.label} '{c.rightName}'\n\
    {String.intercalate "\n" c.lines}"

open Elab Command in
/-- `#kind_relations ns…` — the theorem-edge survey: every `Provenance.Relation`
declared under the given namespaces, re-checked exactly as `#kind_relation` checks one,
rendered one line per edge in declaration-name order as a single `info` message suitable
for `#guard_msgs` pinning. An edge that fails its check renders as a `✗` row carrying the
refusal — like `#kind_scc`'s `⚠` rows, the violation is *in* the report, so the pin is
the gate: a passing scope pins clean rows and a newly violated edge fails the pin. A
`@[kindCounterexample]`-tagged edge renders as a `⊘` row and is not checked, so a
falsification probe can stand beside the gate it exercises. The header counts the edges,
the violations, and the exemptions, so a scope with none pins `0` rather than passing
invisibly. -/
elab "#kind_relations " nss:ident* : command => liftTermElabM do
  if nss.isEmpty then
    throwError "#kind_relations expects at least one namespace"
  let scopes := nss.map (·.getId)
  let env ← getEnv
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut names : Array Name := #[]
  for (n, info) in env.constants.toList do
    if n.isInternal then continue
    unless scopes.any (·.isPrefixOf n) do continue
    if info.type.isConstOf ``Provenance.Relation then names := names.push n
  let sorted := names.qsort fun a b => a.toString < b.toString
  let mut lines : Array String := #[]
  let mut exemptLines : Array String := #[]
  let mut violated := 0
  let mut exempted := 0
  for n in sorted do
    if exempt.contains n then
      exempted := exempted + 1
      exemptLines := exemptLines.push s!"  ⊘ {n}: counterexample, exempted"
      continue
    try
      let c ← checkRelation n
      let extras := String.join <|
        (if c.rel.tolerance.isAnonymous then []
         else [s!" [tolerance: {c.rel.tolerance}]"])
          ++ (if c.rel.licenses.isEmpty then []
              else [s!" [rungs: {String.intercalate ", " (c.rel.licenses.map (·.rung))}]"])
          ++ (if c.rel.wellPosed.isAnonymous then []
              else [s!" [well-posed: {c.rel.wellPosed} on {c.rel.domain}]"])
          ++ (if c.rel.ambiguity.isAnonymous then []
              else [s!" [ambiguity: {c.rel.ambiguity}]"])
      lines := lines.push
        s!"  {n}: '{c.leftName}' {c.rel.kind.label} '{c.rightName}' — \
          {c.rel.witness}{extras}"
    catch e =>
      violated := violated + 1
      lines := lines.push s!"  ✗ {n}: {← e.toMessageData.toString}"
  lines := lines ++ exemptLines
  let violations := if violated == 0 then "" else s!", {violated} violated"
  let exemptions := if exempted == 0 then "" else s!", {exempted} exempted"
  let summary := s!"kind relations — {names.size} theorem edge(s){violations}{exemptions}"
  if lines.isEmpty then logInfo m!"{summary}"
  else logInfo m!"{summary}\n{String.intercalate "\n" lines.toList}"
  recordAuditReceipt "kind_relations" (nss.map (·.getId))

/-! ## The assembly at the scale of its steps

Every reading above is per node. Two facts about the *shape* of an assembly are asked
for often enough — by the overview figure, by the ledger's JSON — that computing them
twice would be two chances to disagree: how big each level's interface is, and which
pairs of levels information crosses between. Both are functions of the assembled value,
so both live here, beside it. -/

/-- What one level says at the scale of the whole assembly: the size of its interface
by role, the size of the interior the walk introduced, and its unkinded count. -/
structure LevelTally where
  ins : Nat
  cfgs : Nat
  outs : Nat
  interior : Nat
  unkinded : Nat
deriving Repr, Inhabited, BEq

/-- The tally of a level. `param` counts with `config`: both are boundary values this
tier does not compute, and the question at this scale is how much crosses the
interface, not which tier below is expected to bind it. -/
def tallyOf (l : AssemblyLevel) : LevelTally :=
  { ins := (l.graph.ports.filter (fun p => p.dir == .input)).length
    cfgs := (l.graph.ports.filter (fun p => p.dir == .config || p.dir == .param)).length
    outs := (l.graph.ports.filter (fun p => p.dir.produced)).length
    interior := l.graph.intros.length
    unkinded := l.unkinded.length }

/-- The level a namespaced node belongs to, by its rendered name — the grouping key the
figures and the ledger use. The crossings below are exactly the occurrences whose
operands and result disagree on it. -/
def levelOfNode (n : NodeId) : Option String :=
  n.level.map (·.render)

/-- The cross-level wires, aggregated: one entry per ordered pair of levels that
information crosses between, with how many occurrences cross it. An occurrence with two
operands in one source level counts once — the entry says that information crosses
here, and how often, not how wide each crossing is. -/
def crossings (a : Assembly) : Array (String × String × Nat) := Id.run do
  let mut acc : Array (String × String × Nat) := #[]
  for o in a.graph.occurrences do
    let some dst := levelOfNode o.result | continue
    let mut seen : Array String := #[]
    for oc in o.operands do
      let some src := levelOfNode oc.1 | continue
      if src == dst || seen.contains src then continue
      seen := seen.push src
      match acc.findIdx? (fun e => e.1 == src && e.2.1 == dst) with
      | some i => acc := acc.set! i (src, dst, acc[i]!.2.2 + 1)
      | none => acc := acc.push (src, dst, 1)
  return acc

/-- The levels a member stands for: itself, or its instances when the member was
dissected at more than one call site. -/
def levelsOfMember (a : Assembly) (m : Name) : Array String :=
  a.levels.filterMap fun l => if l.decl == m then some l.name else none

/-- The citation relation with both endpoints resolved to levels, deduplicated. A
citation names a *member*; a member dissected at several call sites is several levels,
and an endpoint that resolves to no level at all is dropped — drawing it would put a box
in the figure that the assembly does not have. -/
def citeEdges (a : Assembly) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for (src, dst) in a.cites do
    for s in levelsOfMember a src do
      for d in levelsOfMember a dst do
        unless out.contains (s, d) do out := out.push (s, d)
  return out

end PropertyKindCalculus.KindIncidence
