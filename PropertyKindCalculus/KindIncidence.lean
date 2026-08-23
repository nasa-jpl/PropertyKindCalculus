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
and a bundled signature states MORE than the loose one, not less. A sum type has no field
path (which constructor a value took is not a signature fact), and a carrier is a leaf,
never a container — its own field is the erasure boundary.

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
loop or genuine multi-alternative control flow stays opaque. What no reading
recognizes — a raw `⟨…⟩` mint, an opaque sub-step call outside an assembly, a loop
body's result, a point-free body — produces nothing, and the verdict says so: an
unreached derivation target is exactly an anonymous mint. A container *value* is
attributed where the structure assigns its slots — a call destructured into a container
binder derives each of that binder's field paths — and a container assembled inline by
its own constructor produces nothing, the same verdict a raw mint gets.

**Unkinded positions** are read alongside the ports: an explicit binder or result
component whose type carries no kind information at all — no registered carrier, no
kind vocabulary anywhere in it — is naked data crossing the interface, which does not
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
computed on the assembled multi-step object.

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

namespace PropertyKindCalculus.KindIncidence

open Lean
open PropertyKindCalculus.Provenance (Port Intro Occurrence EdgeFamily IntroTier PortDir)

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
  | .const .. => return toString (← Meta.ppExpr e)
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

/-- Render a kind (or exponent) argument of an instantiated binder type:
pretty-printed when closed; by binder name when it still carries loose bound variables —
a parametric kind under an inner binder, where the pretty printer has no context. -/
def renderKindArg (ctx : BinderCtx) (e : Expr) : MetaM String :=
  if e.hasLooseBVars then refName ctx e else return toString (← Meta.ppExpr e)

/-- The kind a carrier-headed type states, or `none` if `ty` is not headed by a
registered carrier: the argument(s) whose instantiated binder type is `KindOfProperty`,
rendered. Positional generic — `Quantity k R` and `IndividualQuantity o k R` both
resolve to `k`. -/
def carrierKind? (env : Environment) (carriers : Array Name) (ctx : BinderCtx)
    (ty : Expr) : MetaM (Option String) := do
  let ty := ty.consumeTypeAnnotations
  let .const c _ := ty.getAppFn | return none
  unless carriers.contains c do return none
  let some ci := env.find? c | return none
  let args := ty.getAppArgs
  let some btys := KindEdges.instantiatedBinderTypes ci.type args | return none
  let kindIdxs := (Array.range args.size).filter fun i =>
    btys[i]!.isConstOf ``KindOfProperty
  if kindIdxs.isEmpty then return none
  let ks ← kindIdxs.mapM fun i => renderKindArg ctx args[i]!
  return some (String.intercalate ", " ks.toList)

/-- **The carrier field paths of a container type** — the ports a record-carried
quantity contributes. A type that is not itself carrier-headed but is a
single-constructor structure states its kinds through its fields: an `IccQ k R` states
`k` twice, at `.lo.q` and `.hi.q`; a pair of quantities states one kind per component.
Each carrier-headed field (recursively, through nested single-constructor structures,
fuel-bounded) yields one `(path, kind)` — the path appended to the binder or result
name, so the port node reads exactly as the body spells the projection
(`refName`, "a field path for a container projection") and the two readings meet at the
same node.

A sum type has no field path (which constructor a value took is not a signature fact),
and a carrier is a leaf, never a container: its own field is the erasure boundary. -/
partial def carrierPaths (env : Environment) (carriers : Array Name) (ctx : BinderCtx)
    (ty : Expr) (fuel : Nat := 3) : MetaM (Array (String × String)) := do
  let ty := ty.consumeTypeAnnotations
  if ty.hasLooseBVars then return #[]
  if (← carrierKind? env carriers ctx ty).isSome then return #[]
  match fuel, ty.getAppFn with
  | fuel + 1, .const c _ =>
    unless isStructure env c do return #[]
    let some (.inductInfo ii) := env.find? c | return #[]
    unless ii.ctors.length == 1 do return #[]
    let x ← Meta.mkFreshExprMVar ty
    let mut out : Array (String × String) := #[]
    for f in getStructureFields env c do
      let some fty ← (try pure (some (← Meta.inferType (← Meta.mkProjection x f)))
                      catch _ => pure none) | continue
      match ← carrierKind? env carriers ctx fty with
      | some k => out := out.push (s!".{f}", k)
      | none =>
        for (p, k) in ← carrierPaths env carriers ctx fty fuel do
          out := out.push (s!".{f}{p}", k)
    return out
  | _, _ => return #[]

/-- Does a type carry kind information at all — a registered carrier or the kind
vocabulary itself, mentioned anywhere in the expression, or (one structure level down,
fuel-bounded) in the fields of the single-constructor inductive at its head? The
negative answer classifies a signature position as *unkinded* (module header,
"Unkinded positions"): naked data, red in every report. The positive answer without a
carrier field path (`carrierPaths`) is a kind-bearing position that ports nothing — a
sum over quantities, a function returning them: not naked data, and not an interface
node either. -/
partial def kindBearing (env : Environment) (carriers : Array Name) (ty : Expr)
    (fuel : Nat := 3) : Bool :=
  let mentions := (ty.find? fun sub =>
    match sub with
    | .const c _ => carriers.contains c || c == ``KindOfProperty
    | _ => false).isSome
  mentions ||
    match fuel, ty.getAppFn with
    | fuel + 1, .const c _ =>
      match env.find? c with
      | some (.inductInfo ii) =>
        ii.ctors.length == 1 &&
          (match ii.ctors.head?.bind env.find? with
           | some ctor => kindBearing env carriers ctor.type fuel
           | none => false)
      | _ => false
    | _, _ => false

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
the two incidence positions). -/
partial def configReads (consts : NameSet) (e : Expr) (acc : Array Name := #[]) :
    Array Name :=
  match e with
  | .const n _ =>
    if consts.contains n && !acc.contains n then acc.push n else acc
  | .app f a => configReads consts a (configReads consts f acc)
  | .lam _ t b _ | .forallE _ t b _ => configReads consts b (configReads consts t acc)
  | .letE _ t v b _ =>
    configReads consts b (configReads consts v (configReads consts t acc))
  | .mdata _ b | .proj _ _ b => configReads consts b acc
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
    || ty.isAppOfArity ``PowerKind 3 || ty.isAppOfArity ``KindMul 3
    || ty.isAppOfArity ``KindDiv 3

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
  occ : Occurrence String String
  /-- The full operand-kind list the license states — the edge's own equation, which a
  partial incidence does not truncate (the operand list is what the site exposes). -/
  edgeKinds : Array String
  /-- License discharged from the step's own hypothesis or instance binder. -/
  assumed : Bool
  /-- Fewer operands exposed than the family relates — a sub-step boundary. -/
  partialIncidence : Bool
deriving Inhabited

/-- `alphaK · betaK → gammaK ⟨x, y⟩` — the edge with its incidence, in the enumeration
grammar (`EdgeFamily.render` over the kinds the license states). -/
def StepOccurrence.render (o : StepOccurrence) : String :=
  let names := o.occ.operands.map (·.1)
  s!"{o.occ.family.render o.edgeKinds.toList o.occ.resultKind} ⟨{String.intercalate ", " names}⟩"

/-- The graph rendering of an occurrence: the enumeration line, the result node it
wires, and its marker if any. -/
def StepOccurrence.renderWired (o : StepOccurrence) : String :=
  let marker :=
    if o.partialIncidence then " (partial)" else if o.assumed then " (assumed)" else ""
  s!"{o.render} ⇒ {o.occ.result}{marker}"

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
  intros : Array (Intro String String) := #[]
  exits : Array String := #[]
  freshCount : Nat := 0
  leaks : Array (String × String) := #[]

/-- The next synthesized interior node. -/
def WalkSt.nextFresh (st : WalkSt) : String × WalkSt :=
  let n := st.freshCount + 1
  (s!"_{n}", { st with freshCount := n })

/-- Record an exit, once per node. -/
def WalkSt.exit (st : WalkSt) (n : String) : WalkSt :=
  if st.exits.contains n then st else { st with exits := st.exits.push n }

/-- Record an unkinded flow, once per (source, target) pair. -/
def WalkSt.leak (st : WalkSt) (src dst : String) : WalkSt :=
  if st.leaks.contains (src, dst) then st
  else { st with leaks := st.leaks.push (src, dst) }

/-- Wire `node` from the named `src` by the identity `copy`, introducing `node` as
`derived` when the walk owns its introduction (a `let` binder or synthesized node —
never a port). -/
def WalkSt.copyTo (st : WalkSt) (site src node kind : String) (owned : Bool) : WalkSt :=
  let st := if owned then { st with intros := st.intros.push ⟨node, kind, .derived⟩ }
            else st
  let so : StepOccurrence := ⟨⟨.copy, [(src, kind)], node, kind, site⟩, #[kind], false, false⟩
  { st with occs := st.occs.push so }

/-- A value's assignment target: the node its producer lands on. -/
inductive Target where
  /-- Produce onto this node; `owned` says the walk owns its introduction event (a
  `let` binder or synthesized interior node — never a port). -/
  | one (node kind : String) (owned : Bool)
  /-- The root of a multi-output producer: one slot per component — empty for an
  un-kinded one, one entry for a carrier-typed one, and one entry *per carrier field
  path* for a container-typed one (`carrierPaths`) — each entry a node, its kind, and
  whether the walk owns its introduction (an output port's slot is not owned; a matcher
  binder's is). -/
  | tuple (comps : List (List (String × String × Bool)))

/-- The single-node view of an optional target. -/
def Target.asOne? : Option Target → Option (String × String × Bool)
  | some (.one n k o) => some (n, k, o)
  | _ => none

/-- Introduce a *source* (an attested or gated mint) at the target: directly on a node
the walk owns, or through a synthesized source node wired to a port by `copy`. With no
target the source is still recorded — a mint is a mint wherever it sits. Returns the
source node introduced, so the minting site can attribute its unkinded flows to it. -/
def sourceAt (h : HarvestCtx) (tier : IntroTier) (kind : String)
    (t1 : Option (String × String × Bool)) (st : WalkSt) : String × WalkSt :=
  match t1 with
  | some (n, k, true) => (n, { st with intros := st.intros.push ⟨n, k, tier⟩ })
  | some (n, k, false) =>
    let (m, st) := st.nextFresh
    let st := { st with intros := st.intros.push ⟨m, k, tier⟩ }
    let so : StepOccurrence := ⟨⟨.copy, [(m, k)], n, k, h.site⟩, #[k], false, false⟩
    (m, { st with occs := st.occs.push so })
  | none =>
    let (m, st) := st.nextFresh
    (m, { st with intros := st.intros.push ⟨m, kind, tier⟩ })

/-- The unkinded flows into a mint: each unkinded argument occurring in the minting
application flows into the mint's node — unkinded information minting kinded
information, the reading the red arrows draw (module header, "Unkinded
positions"). -/
def mintLeaks (h : HarvestCtx) (e : Expr) (node : String) (st : WalkSt) : WalkSt :=
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
def opaqueTarget (h : HarvestCtx) (t1 : Option (String × String × Bool))
    (st : WalkSt) : WalkSt :=
  match t1 with
  | some (n, k, true) => { st with intros := st.intros.push ⟨n, k, .derived⟩ }
  | some (n, k, false) =>
    if h.declKindConst then
      let (m, st) := st.nextFresh
      let st := { st with intros := st.intros.push ⟨m, k, .attested "[kindConst]"⟩ }
      let so : StepOccurrence := ⟨⟨.copy, [(m, k)], n, k, h.site⟩, #[k], false, false⟩
      { st with occs := st.occs.push so }
    else st
  | none => st

/-- The rendered name of a step declaration — the pretty printer's spelling in the
current namespace context, without the explicit-argument `@` marker a signature with
implicit binders would carry: the name labels a procedure edge and prefixes a node
namespace, where the marker is noise. -/
def stepNameOf (ci : ConstantInfo) : MetaM String := do
  let s := toString (← Meta.ppExpr (mkConst ci.name (ci.levelParams.map mkLevelParam)))
  return if s.startsWith "@" then (s.drop 1).toString else s

/-- One edge stated by a consuming application's binders, kinds rendered. -/
structure BinderEdge where
  family : EdgeFamily
  opKinds : Array String
  resKind : String
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
      let opKinds ← opTys.mapM (renderKindArg ctx)
      let resKind ← renderKindArg ctx resTy
      edges := edges.push
        { family := fam, opKinds, resKind, assumed := !witnessAuthored ctx args[i]! }
    else if let .const ic _ := args[i]!.getAppFn then
      if let some ii := h.env.find? ic then
        let uargs := args[i]!.getAppArgs
        if let some ubtys := KindEdges.instantiatedBinderTypes ii.type uargs then
          for u in [0:uargs.size] do
            if let some (fam, opTys, resTy) := tableEdgeOfType? ubtys[u]! then
              let opKinds ← opTys.mapM (renderKindArg ctx)
              let resKind ← renderKindArg ctx resTy
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
    let st ← match ← carrierKind? h.env h.carriers ctx t with
      | some k => walk h v ctx (some (.one (toString nm) k true)) st
      | none => walk h v ctx none st
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
      | some (n, k, owned) => return st.copyTo h.site (← refName ctx e) n k owned
      | none => return st
    let st := opaqueTarget h (Target.asOne? target) st
    let st ← if h.carrierSpecs.any (·.structName == sn) then
        pure (st.exit (← refName ctx b))
      else pure st
    walk h b ctx none st
  | .fvar .. | .bvar .. =>
    match Target.asOne? target with
    | some (n, k, owned) => return st.copyTo h.site (← refName ctx e) n k owned
    | none => return st
  | _ =>
    -- a multi-output root: split a literal tuple onto its component slots
    if let some (.tuple comps) := target then
      if e.isAppOfArity ``Prod.mk 4 then
        let args := e.getAppArgs
        let st ← walk h args[0]! ctx none st
        let st ← walk h args[1]! ctx none st
        -- a component's slot is single-node or it stays unwired: a literal tuple
        -- component that is itself a container is produced by its own expression, and
        -- the walk attributes a container value only where a call assigns its slots
        let oneOf : List (String × String × Bool) → Option Target
          | [(n, k, o)] => some (.one n k o)
          | _ => none
        match comps with
        | c :: rest =>
          let st ← walk h args[2]! ctx (oneOf c) st
          let restT : Option Target := match rest with
            | [c'] => oneOf c'
            | _ => some (.tuple rest)
          walk h args[3]! ctx restT st
        | [] => walk h args[3]! ctx none st
      else
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
      | some (n, k, owned) => return st.copyTo h.site (← refName ctx e) n k owned
      | none => return st
    else
      walkApp h e ctx (Target.asOne? target) st

/-- The application readings, in order: do-elaboration transparency, attested mint,
gated ingest, emission-shell mint, sub-step procedure edge, erasure, consuming
application, tuple destructuring, configuration read, opaque. -/
partial def walkApp (h : HarvestCtx) (e : Expr) (ctx : BinderCtx)
    (t1 : Option (String × String × Bool)) (st : WalkSt) : MetaM WalkSt := do
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
      let st ← match ← carrierKind? h.env h.carriers ctx t with
        | some k => walk h args[4]! ctx (some (.one (toString nm) k true)) st
        | none => walk h args[4]! ctx none st
      return ← walk h b ((nm, none) :: ctx) (t1.map fun (n, k, o) => .one n k o) st
    | f =>
      let st ← walk h args[4]! ctx none st
      return ← walk h f ctx none st
  if e.isAppOfArity ``letFun 4 then
    match args[3]! with
    | .lam nm t b _ =>
      let st ← walk h t ctx none st
      let st ← match ← carrierKind? h.env h.carriers ctx t with
        | some k => walk h args[2]! ctx (some (.one (toString nm) k true)) st
        | none => walk h args[2]! ctx none st
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
  -- an attested mint: a declared source carrying its harvested reason
  if let some asp := h.attestors.find? (fun a => a.declName == c) then
    if args.size == asp.arity then
      let reason := match args[asp.reasonIdx]? with
        | some (.lit (.strVal s)) => s
        | _ => "…"
      let kind ← match args[asp.kindIdx]? with
        | some ka => renderKindArg ctx ka
        | none => pure "_"
      let (n, st) := sourceAt h (.attested reason) kind t1 st
      let st := mintLeaks h e n st
      return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- a gated ingest: raw data admitted through a check
  if h.ingestConsts.contains c then
    let kind := (t1.map fun (_, k, _) => k).getD "_"
    let (n, st) := sourceAt h .gated kind t1 st
    let st := mintLeaks h e n st
    return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- an emission-shell mint: `@[kindEmission]` sanctions this declaration's carrier
  -- constructors as the grid↔kernel boundary — the mint enters through a declared
  -- source carrying the tier as its reason
  if h.declEmission && h.carrierSpecs.any (fun s =>
      s.ctorName == c && args.size == s.ctorArity) then
    let kind := (t1.map fun (_, k, _) => k).getD "_"
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
    let st := st.exit (← refName ctx victim)
    return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- a consuming application: binder-stated edges with carrier siblings
  if let some ci := h.env.find? c then
    if !args.isEmpty then
      if let some btys := KindEdges.instantiatedBinderTypes ci.type args then
        let edges ← binderEdges h ctx args btys
        let operandIdxs := (Array.range args.size).filter fun j =>
          match btys[j]!.consumeTypeAnnotations.getAppFn with
          | .const cc _ => h.carriers.contains cc
          | _ => false
        if !edges.isEmpty && !operandIdxs.isEmpty then
          -- name the operands; a nested producer gets a synthesized node to land on
          let mut st := st
          let mut opNames : Array String := #[]
          let mut opTargets : Std.HashMap Nat Target := {}
          for j in operandIdxs do
            let a := args[j]!
            if isProducerApp h a then
              let (m, st') := st.nextFresh
              st := st'
              let bk := (← carrierKind? h.env h.carriers ctx btys[j]!).getD "_"
              opNames := opNames.push m
              opTargets := opTargets.insert j (.one m bk true)
            else
              opNames := opNames.push (← refName ctx a)
          -- emit, the first full edge landing on the target node
          let mut consumed := false
          for be in edges do
            let partialInc := operandIdxs.size < be.family.operandCount
            let ops := (opNames.zip be.opKinds).toList
            let mut resNode := ""
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
              ⟨⟨be.family, ops, resNode, be.resKind, h.site⟩, be.opKinds, be.assumed,
               partialInc⟩
            st := { st with occs := st.occs.push so }
          if !consumed then
            st := opaqueTarget h t1 st
          -- recurse into the arguments, nested producers onto their nodes
          for j in [0:args.size] do
            st := (← walk h args[j]! ctx (opTargets.get? j) st)
          return st
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
        -- the continuation spells the projections
        let mut ctx' := ctx
        let mut slots : List (List (String × String × Bool)) := []
        for (nm, t) in binders do
          let slot ← match ← carrierKind? h.env h.carriers ctx' t with
            | some k => pure [(toString nm, k, true)]
            | none => do
              let paths ← carrierPaths h.env h.carriers ctx' t
              pure (paths.toList.map fun (p, k) => (s!"{nm}{p}", k, true))
          slots := slots ++ [slot]
          ctx' := (nm, none) :: ctx'
        let st ← walk h ma.discrs[0]! ctx (some (.tuple slots)) st
        let st ← walk h body ctx' (t1.map fun (n, k, o) => .one n k o) st
        return ← ma.remaining.foldlM (fun st a => walk h a ctx none st) st
  -- a configuration read: the identity wire from the constant's port node
  if h.configConsts.contains c then
    if let some (n, k, owned) := t1 then
      let st := st.copyTo h.site (← refName ctx e) n k owned
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
    (targets : Sum (Option (String × String × Bool))
      (List (List (String × String × Bool))))
    (st : WalkSt) : MetaM WalkSt := do
  let args := e.getAppArgs
  let fallback (st : WalkSt) : MetaM WalkSt := do
    let st := match targets with
      | .inl t1 => opaqueTarget h t1 st
      | .inr _ => st
    args.foldlM (fun st a => walk h a ctx none st) st
  let some ci := h.env.find? c | fallback st
  let some btys := KindEdges.instantiatedBinderTypes ci.type args | fallback st
  let stepName ← stepNameOf ci
  -- the incidence slots: a carrier-typed argument position, and one per carrier field
  -- path of a container-typed one — the callee's input ports, in the same order
  let mut opSlots : Array (Nat × String × String) := #[]
  for j in [0:args.size] do
    let bty := btys[j]!
    let isCarrier := match bty.consumeTypeAnnotations.getAppFn with
      | .const cc _ => h.carriers.contains cc
      | _ => false
    if isCarrier then
      opSlots := opSlots.push (j, "", (← carrierKind? h.env h.carriers ctx bty).getD "_")
    else
      for (p, k) in ← carrierPaths h.env h.carriers ctx bty do
        opSlots := opSlots.push (j, p, k)
  let opKinds : Array String := opSlots.map (·.2.2)
  -- name the operands; a nested producer gets a synthesized node to land on
  let mut st := st
  let mut opNames : Array String := #[]
  let mut opTargets : Std.HashMap Nat Target := {}
  for (j, p, k) in opSlots do
    let a := args[j]!
    if p.isEmpty && isProducerApp h a then
      let (m, st') := st.nextFresh
      st := st'
      opNames := opNames.push m
      opTargets := opTargets.insert j (.one m k true)
    else
      opNames := opNames.push s!"{← refName ctx a}{p}"
  let ops := (opNames.zip opKinds).toList
  let fam := Provenance.EdgeFamily.step stepName opSlots.size
  let emit (st : WalkSt) (node kind : String) (owned : Bool) : WalkSt :=
    let st := if owned then { st with intros := st.intros.push ⟨node, kind, .derived⟩ }
              else st
    let so : StepOccurrence := ⟨⟨fam, ops, node, kind, h.site⟩, opKinds, false, false⟩
    { st with occs := st.occs.push so }
  match targets with
  | .inl t1 =>
    match t1 with
    | some (n, k, owned) => st := emit st n k owned
    | none =>
      -- an unassigned single result still derives: onto a synthesized node, at the
      -- callee's instantiated conclusion kind
      let kind ← match KindEdges.instantiatedConclusion ci.type args with
        | some concl => pure ((← carrierKind? h.env h.carriers ctx concl).getD "_")
        | none => pure "_"
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
def renderLeak (l : String × String) : String :=
  s!"unkinded flow: {l.1} ⇒ {l.2}"

/-- The harvest of one step: the graph's constituents, with the two markers
(`assumed` / `partialIncidence`) the graph value does not carry, the unkinded
positions of its signature, and their flows into the kinded nodes. `provenance` is the
constructed object — the unkinded reading deliberately stays outside it: the wiring
judgment the kernel decides is about the kinded algebra, and the red inventory is the
record of what falls outside that algebra, carried by the renderings. -/
structure StepGraph where
  ports : List (Port String String)
  intros : List (Intro String String)
  occs : Array StepOccurrence
  exits : List String
  unkinded : List UnkindedSlot := []
  leaks : List (String × String) := []

/-- **The constructed graph value.** Partial-incidence occurrences are excluded from
the wiring — a sub-step boundary is not an edge of this step's graph — so a step that
hides an operand behind a helper is refused until assembly closes it. -/
def StepGraph.provenance (s : StepGraph) : Provenance String String :=
  { ports := s.ports
    intros := s.intros
    occurrences := ((s.occs.filter (!·.partialIncidence)).map (·.occ)).toList
    exits := s.exits }

/-- One port line: `input x : alphaK`. -/
def renderPort (p : Port String String) : String :=
  s!"{p.dir.label} {p.node} : {p.kind}"

/-- One introduction line: `derived t : deltaK`, `gated _1 : k`,
`attested "reason" _1 : k`. -/
def renderIntro (i : Intro String String) : String :=
  s!"{i.tier.label} {i.node} : {i.kind}"

/-- The full graph rendering: ports, unkinded positions, introductions, wired
occurrences (markers kept), exits, unkinded flows, and the evaluated well-formedness
verdict. -/
def StepGraph.renderLines (s : StepGraph) : List String :=
  s.ports.map renderPort
    ++ s.unkinded.map renderUnkinded
    ++ s.intros.map renderIntro
    ++ (s.occs.map (·.renderWired)).toList
    ++ s.exits.map (fun n => s!"exit {n}")
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
    let mut ports : Array (Port String String) := #[]
    let mut unkinded : Array UnkindedSlot := #[]
    let mut unkIdx : Array (Nat × String) := #[]
    for idx in [0:fvars.size] do
      let fv := fvars[idx]!
      let ty ← fv.fvarId!.getType
      if let some k ← carrierKind? env carriers [] ty then
        ports := ports.push
          { node := toString (← fv.fvarId!.getUserName), kind := k, dir := .input }
      else
        -- a container binder states its kinds through its fields: one port per carrier
        -- field path, named as the body spells the projection
        let paths ← carrierPaths env carriers [] ty
        if !paths.isEmpty then
          let nm := toString (← fv.fvarId!.getUserName)
          for (p, k) in paths do
            ports := ports.push { node := s!"{nm}{p}", kind := k, dir := .input }
        else
          -- the unkinded reading: an explicit data binder whose type carries no kind
          -- information at all (propositions and sorts are interface logic, not data)
          let bi := (← fv.fvarId!.getDecl).binderInfo
          if bi.isExplicit && !ty.isSort && !(← Meta.isProp ty)
              && !kindBearing env carriers ty then
            let nm := toString (← fv.fvarId!.getUserName)
            unkinded := unkinded.push ⟨nm, toString (← Meta.ppExpr ty), .input⟩
            unkIdx := unkIdx.push (idx, nm)
    if let some v := info.value? then
      for c in configReads cfgConsts v do
        let some ci := env.find? c | continue
        let node := toString (← Meta.ppExpr (mkConst c (ci.levelParams.map mkLevelParam)))
        let kind ← Meta.forallTelescope ci.type fun _ resTy =>
          return (← carrierKind? env carriers [] resTy).getD "_"
        ports := ports.push { node := node, kind := kind, dir := .config }
    let comps := prodComponents resultTy
    let mut outSlots : Array (List (String × String × Bool)) := #[]
    for i in [0:comps.size] do
      let node := if comps.size == 1 then "result" else s!"result.{i + 1}"
      match ← carrierKind? env carriers [] comps[i]! with
      | some k =>
        ports := ports.push { node := node, kind := k, dir := .output }
        outSlots := outSlots.push [(node, k, false)]
      | none =>
        let cty := comps[i]!
        let paths ← carrierPaths env carriers [] cty
        if !paths.isEmpty then
          for (p, k) in paths do
            ports := ports.push { node := s!"{node}{p}", kind := k, dir := .output }
          outSlots := outSlots.push
            (paths.toList.map fun (p, k) => (s!"{node}{p}", k, false))
        else
          outSlots := outSlots.push []
          if !cty.isSort && !(← Meta.isProp cty) && !kindBearing env carriers cty then
            unkinded := unkinded.push ⟨node, toString (← Meta.ppExpr cty), .output⟩
    let st ← match info.value? with
      | none => pure {}
      | some v =>
        Meta.lambdaTelescope v fun lamFvars body => do
          let hv := { h with unkindedFVars := unkIdx.filterMap fun (idx, nm) =>
            lamFvars[idx]?.map fun fv => (fv.fvarId!, nm) }
          let rootTarget : Option Target :=
            if comps.size == 1 then
              match outSlots[0]! with
              | [(n, k, _)] => some (.one n k false)
              | _ => none
            else if outSlots.any (!·.isEmpty) then
              some (.tuple outSlots.toList)
            else
              none
          let mut st ← walk hv body [] rootTarget {}
          -- the output flows: an unkinded argument surviving the mint mask into a
          -- kinded output's defining expression steers that output from outside the
          -- kinded algebra — per component on a literal tuple spine, else every
          -- kinded output
          let vcomps? := prodValueComps body comps.size
          for (fv, nm) in hv.unkindedFVars do
            match vcomps? with
            | some vs =>
              for ci in [0:vs.size] do
                for (n, _, _) in outSlots[ci]! do
                  if (maskMints hv vs[ci]!).containsFVar fv then st := st.leak nm n
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
caller's procedure edge stands as the call's derivation. A kind-generic callee is
monomorphized by its call site: the wires state the instantiated kinds, so the box is
renamed through the call's kind assignment — the assembly's form of "carrier-generic
code becomes concrete where its witnesses are discharged". A callee wired from two
call sites shares one box, conflating the invocations' operands; per-invocation box
instancing is recorded future work, and a pilot chain wires each callee once.

The *citation* relation — which member's value references which — is harvested by
constant scan and rendered (`cites: a → b`), never wired: a call inside an interior
the walk cannot wire is a citation a figure may draw dashed, not an edge of the
checked object. Well-formedness is checked on the assembled object, and
`#kind_assembly_decide` has the kernel re-derive it. -/

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
  walked : Bool
  graph : Provenance String String
  src : String := ""
  /-- The member's unkinded signature positions, in the level's node namespace — the
  red inventory a rendering marks (module header, "Unkinded positions"). -/
  unkinded : List UnkindedSlot := []
  /-- The member's unkinded flows, namespaced, kept where the target node is declared
  in the level's contributed graph — the red arrows. -/
  leaks : List (String × String) := []
deriving Inhabited

/-- A multi-step assembly: the levels with their modes, the one union graph the
verdict and the kernel theorem are stated on, and the citation relation. -/
structure Assembly where
  levels : Array AssemblyLevel
  graph : Provenance String String
  cites : Array (String × String)

/-- The signature box of an interface-mode level: its ports, plus the level's own
procedure edge deriving each output port from the input ports — the signature's claim,
with interior accountability the audit's. -/
def interfaceBox (name : String) (g : StepGraph) : Provenance String String :=
  let ins := g.ports.filter (·.dir == .input)
  let outs := g.ports.filter (·.dir == .output)
  { ports := g.ports
    intros := []
    occurrences := outs.map fun o =>
      ⟨.step name ins.length, ins.map (fun p => (p.node, p.kind)), o.node, o.kind, name⟩
    exits := [] }

/-- Assemble a set of declarations into one multi-step graph (module section, "The
assembly"): per-level harvests with the other members as sub-steps, walked-or-interface
inclusion, call-site dissection with monomorphizing kind maps and port demotion,
namespaced union, and the citation scan. -/
def assemble (decls : Array Name) : MetaM Assembly := do
  let env ← getEnv
  -- rendered names — the node-namespace prefixes and procedure-edge labels
  let mut names : Array String := #[]
  for d in decls do
    let some ci := env.find? d | throwError "unknown declaration '{d}'"
    names := names.push (← stepNameOf ci)
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
  let mut contribs : Array (Provenance String String) := #[]
  let mut unks : Array (List UnkindedSlot) := #[]
  let mut lks : Array (List (String × String)) := #[]
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
      contribs := contribs.push (interfaceBox names[i]! g)
  -- call-site dissection: wires, demotions, and per-callee kind assignments (a
  -- multi-output call emits one procedure edge per slot, so its input wires dedup)
  let mut wires : Array (Provenance.Occurrence String String) := #[]
  let mut wireKeys : Std.HashSet String := {}
  let mut demoted : Array String := #[]
  let mut kindPairs : Array (Array (String × String)) := .replicate decls.size #[]
  for i in [0:decls.size] do
    unless walkedFlags[i]! do continue
    let caller := names[i]!
    let mut seenPerCallee : Std.HashMap Nat Nat := {}
    for o in contribs[i]!.occurrences do
      let .step t _ := o.family | continue
      let some j := names.findIdx? (· == t) | continue
      let callee := names[j]!
      let calleeIns := contribs[j]!.ports.filter (·.dir == .input)
      let calleeOuts := contribs[j]!.ports.filter (·.dir == .output)
      -- operands wire the callee's input ports, positionally
      for (p, opc) in calleeIns.zip o.operands do
        let key := s!"{caller}/{opc.1}⇒{callee}/{p.node}"
        unless wireKeys.contains key do
          wireKeys := wireKeys.insert key
          wires := wires.push
            ⟨.copy, [(s!"{caller}/{opc.1}", opc.2)], s!"{callee}/{p.node}", opc.2, caller⟩
          if !demoted.contains s!"{callee}/{p.node}" then
            demoted := demoted.push s!"{callee}/{p.node}"
        kindPairs := kindPairs.modify j (·.push (p.kind, opc.2))
      -- the call's results monomorphize the callee's output kinds, in slot order
      let k := (seenPerCallee.get? j).getD 0
      seenPerCallee := seenPerCallee.insert j (k + 1)
      if let some out := calleeOuts[k % (max calleeOuts.length 1)]? then
        kindPairs := kindPairs.modify j (·.push (out.kind, o.resultKind))
  -- transform each level: monomorphize, namespace, demote — then union
  let mut levels : Array AssemblyLevel := #[]
  let mut graph : Provenance String String := ⟨[], [], [], []⟩
  for i in [0:decls.size] do
    let name := names[i]!
    let kmap : Std.HashMap String String :=
      kindPairs[i]!.foldl (init := {}) fun m pr =>
        if m.contains pr.1 then m else m.insert pr.1 pr.2
    let p := contribs[i]!
    let p := p.mapKinds (fun k => (kmap.get? k).getD k)
    let p := p.mapNodes (s!"{name}/{·}")
    let (demotedPorts, keptPorts) := p.ports.partition fun q =>
      q.dir == .input && demoted.contains q.node
    let p := { p with
      ports := keptPorts
      intros := demotedPorts.map (fun q => ⟨q.node, q.kind, .derived⟩) ++ p.intros }
    let nsUnk := unks[i]!.map fun u => { u with node := s!"{name}/{u.node}" }
    let nsLks := (lks[i]!.map fun (s, t) => (s!"{name}/{s}", s!"{name}/{t}")).filter
      fun (_, t) => (p.kindOf? t).isSome
    levels := levels.push ⟨decls[i]!, name, walkedFlags[i]!, p, srcs[i]!, nsUnk, nsLks⟩
    graph := graph.union p
  graph := graph.union ⟨[], [], wires.toList, []⟩
  -- the citation relation: which member's value references which
  let mut cites : Array (String × String) := #[]
  for i in [0:decls.size] do
    let d := decls[i]!
    let others : NameSet :=
      (decls.filter (· != d)).foldl (init := {}) (·.insert ·)
    if let some v := (env.find? d).bind (·.value?) then
      for c in configReads others v do
        if let some j := decls.findIdx? (· == c) then
          cites := cites.push (names[i]!, names[j]!)
  return { levels, graph, cites }

/-- Render one graph occurrence in the wired grammar: the edge equation over the kinds
its operands state, the incidence, the result node. -/
def renderOccurrence (o : Provenance.Occurrence String String) : String :=
  let names := o.operands.map (·.1)
  let eq := o.family.render (o.operands.map (·.2)) o.resultKind
  s!"{eq} ⟨{String.intercalate ", " names}⟩ ⇒ {o.result}"

/-- The assembly rendering: each level with its inclusion mode, the union graph's
ports, introductions, occurrences, and exits, the levels' unkinded positions and
flows, the citation relation, and the evaluated verdict. -/
def Assembly.renderLines (a : Assembly) : List String :=
  (a.levels.toList.map fun l =>
      s!"level {l.name}: {if l.walked then "walked" else "interface"}")
    ++ a.graph.ports.map renderPort
    ++ a.graph.intros.map renderIntro
    ++ a.graph.occurrences.map renderOccurrence
    ++ a.graph.exits.map (fun n => s!"exit {n}")
    ++ (a.levels.toList.flatMap fun l => l.unkinded.map renderUnkinded)
    ++ (a.levels.toList.flatMap fun l => l.leaks.map renderLeak)
    ++ a.cites.toList.map (fun (x, y) => s!"cites: {x} → {y}")
    ++ [s!"well-formed: {a.graph.wellFormed}"]

/-! ## Reflection — the harvested graph as a term, for the kernel

`Provenance String String` reflected as an `Expr` literal, so `#kind_graph_decide` can
state `WellFormed` on the constructed object and have the kernel reduce the checker —
"the kernel checks the wiring", literally, on harvested graphs and not only hand-authored
ones. -/

private def strE : Expr := mkConst ``String

instance : ToExpr PortDir where
  toTypeExpr := mkConst ``Provenance.PortDir
  toExpr
    | .input => mkConst ``Provenance.PortDir.input
    | .config => mkConst ``Provenance.PortDir.config
    | .output => mkConst ``Provenance.PortDir.output

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
    | .tableMul => mkConst ``Provenance.EdgeFamily.tableMul
    | .tableDiv => mkConst ``Provenance.EdgeFamily.tableDiv
    | .copy => mkConst ``Provenance.EdgeFamily.copy
    | .step nm a =>
      mkApp2 (mkConst ``Provenance.EdgeFamily.step) (toExpr nm) (toExpr a)

instance : ToExpr (Port String String) where
  toTypeExpr := mkApp2 (mkConst ``Provenance.Port) strE strE
  toExpr p := mkApp5 (mkConst ``Provenance.Port.mk) strE strE
    (toExpr p.node) (toExpr p.kind) (toExpr p.dir)

instance : ToExpr (Intro String String) where
  toTypeExpr := mkApp2 (mkConst ``Provenance.Intro) strE strE
  toExpr i := mkApp5 (mkConst ``Provenance.Intro.mk) strE strE
    (toExpr i.node) (toExpr i.kind) (toExpr i.tier)

instance : ToExpr (Occurrence String String) where
  toTypeExpr := mkApp2 (mkConst ``Provenance.Occurrence) strE strE
  toExpr o := mkApp7 (mkConst ``Provenance.Occurrence.mk) strE strE
    (toExpr o.family) (toExpr o.operands) (toExpr o.result) (toExpr o.resultKind)
    (toExpr o.site)

instance : ToExpr (Provenance String String) where
  toTypeExpr := mkApp2 (mkConst ``PropertyKindCalculus.Provenance) strE strE
  toExpr g := mkApp6 (mkConst ``PropertyKindCalculus.Provenance.mk) strE strE
    (toExpr g.ports) (toExpr g.intros) (toExpr g.occurrences) (toExpr g.exits)

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
    !o.assumed && !(o.occ.family matches .copy) && !(o.occ.family matches .step _ _)
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
/-- `#kind_assembly_decide [d₁, d₂, …]` assembles the listed declarations, reflects
the union graph into a term, and adds the theorem `d₁.kindAssemblyWf :
(graph).WellFormed`, proved by `decide` — kernel reduction of the structural checker
on the assembled multi-step object. Errors out (before troubling the kernel) when the
assembly is not well-formed. -/
elab "#kind_assembly_decide " "[" ids:ident,* "]" : command => liftTermElabM do
  let decls ← ids.getElems.mapM fun id => realizeGlobalConstNoOverload id
  if decls.isEmpty then throwError "#kind_assembly_decide expects at least one declaration"
  let a ← assemble decls
  unless a.graph.wellFormed do
    throwError "the kind assembly is not well-formed — render it with #kind_assembly"
  let prop ← Meta.mkAppM ``Provenance.WellFormed #[toExpr a.graph]
  let proof ← Meta.mkDecideProof prop
  let name := decls[0]! ++ `kindAssemblyWf
  addDecl (.thmDecl { name, levelParams := [], type := prop, value := proof })
  logInfo m!"kernel-accepted: the kind assembly is well-formed (theorem '{name}')"

end PropertyKindCalculus.KindIncidence
