/-
# `#kind_graph` — the step harvest: one constructed object, rendered four ways

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
`attested "[kindConst]"` source — the audit's tiers, carried into the graph. A carrier
projection marks its operand as an **exit**: the erasure boundary, beyond which the byte
gate carries the claim. What no reading recognizes — a raw `⟨…⟩` mint, an opaque
sub-step call, a monadic wrapper, a point-free body — produces nothing, and the verdict
says so: an unreached derivation target is exactly an anonymous mint. (A record-carried
quantity is not yet a port: the signature reading recognizes carrier-headed binders, so
record parameters enter the graph story when their carrier maps do.)

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

/-- Render an operand as a *name* — a binder name for a variable, the head constant for
an application (`let` bodies and projections descended), the literal for a literal: the
granularity the incidence relation records. -/
partial def refName (ctx : BinderCtx) (e : Expr) : MetaM String :=
  match e with
  | .app f _ => refName ctx f
  | .mdata _ b => refName ctx b
  | .const .. => return toString (← Meta.ppExpr e)
  | .fvar id => return toString (← id.getDecl).userName
  | .bvar i =>
    match ctx[i]? with
    | some (nm, _) => return toString nm
    | none => return "_"
  | .letE nm _ v b _ => refName ((nm, some v) :: ctx) b
  | .proj _ i b => return s!"{← refName ctx b}.{i}"
  | .lit (.natVal v) => return toString v
  | .lit (.strVal s) => return s!"\"{s}\""
  | _ => return "_"

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

/-- The result type's right-spine product components — `A × B × C` is three output
positions. A parenthesized left factor stays one component: positions follow what the
signature spells. -/
partial def prodComponents (ty : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if ty.isAppOfArity ``Prod 2 then
    let args := ty.getAppArgs
    prodComponents args[1]! (acc.push args[0]!)
  else
    acc.push ty

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
attestor registries, the occurrence site, and whether the harvested declaration is
itself a `@[kindConst]` mint (its value then wires through a declared source). -/
structure HarvestCtx where
  env : Environment
  carriers : Array Name
  carrierSpecs : Array BoundaryAudit.CarrierSpec
  configConsts : NameSet
  ingestConsts : NameSet
  attestors : Array BoundaryAudit.AttestSpec
  site : String
  declKindConst : Bool

/-- The walk's accumulator: occurrences, introduction events, exits, and the counter
behind synthesized interior nodes (`_1`, `_2`, … in walk order). -/
structure WalkSt where
  occs : Array StepOccurrence := #[]
  intros : Array (Intro String String) := #[]
  exits : Array String := #[]
  freshCount : Nat := 0

/-- The next synthesized interior node. -/
def WalkSt.nextFresh (st : WalkSt) : String × WalkSt :=
  let n := st.freshCount + 1
  (s!"_{n}", { st with freshCount := n })

/-- Record an exit, once per node. -/
def WalkSt.exit (st : WalkSt) (n : String) : WalkSt :=
  if st.exits.contains n then st else { st with exits := st.exits.push n }

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
  /-- The root of a multi-output step: one slot per result-type component, `none` for
  an un-kinded component. -/
  | tuple (comps : List (Option (String × String)))

/-- The single-node view of an optional target. -/
def Target.asOne? : Option Target → Option (String × String × Bool)
  | some (.one n k o) => some (n, k, o)
  | _ => none

/-- Introduce a *source* (an attested or gated mint) at the target: directly on a node
the walk owns, or through a synthesized source node wired to a port by `copy`. With no
target the source is still recorded — a mint is a mint wherever it sits. -/
def sourceAt (h : HarvestCtx) (tier : IntroTier) (kind : String)
    (t1 : Option (String × String × Bool)) (st : WalkSt) : WalkSt :=
  match t1 with
  | some (n, k, true) => { st with intros := st.intros.push ⟨n, k, tier⟩ }
  | some (n, k, false) =>
    let (m, st) := st.nextFresh
    let st := { st with intros := st.intros.push ⟨m, k, tier⟩ }
    let so : StepOccurrence := ⟨⟨.copy, [(m, k)], n, k, h.site⟩, #[k], false, false⟩
    { st with occs := st.occs.push so }
  | none =>
    let (m, st) := st.nextFresh
    { st with intros := st.intros.push ⟨m, kind, tier⟩ }

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
application, a gated ingest, or a consuming application (an edge stated directly or one
instance-unfold away)? Such an operand is walked onto a synthesized node so the outer
occurrence and the inner producer name the same thing. -/
def isProducerApp (h : HarvestCtx) (a : Expr) : Bool :=
  match a.getAppFn with
  | .const c _ =>
    (h.attestors.any fun s => s.declName == c && a.getAppNumArgs == s.arity)
      || h.ingestConsts.contains c
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
    -- a multi-output root: split a literal tuple onto its component ports
    if let some (.tuple comps) := target then
      if e.isAppOfArity ``Prod.mk 4 then
        let args := e.getAppArgs
        let st ← walk h args[0]! ctx none st
        let st ← walk h args[1]! ctx none st
        match comps with
        | c :: rest =>
          let st ← walk h args[2]! ctx (c.map fun (n, k) => .one n k false) st
          let restT : Option Target := match rest with
            | [c'] => c'.map fun (n, k) => .one n k false
            | _ => some (.tuple rest)
          walk h args[3]! ctx restT st
        | [] => walk h args[3]! ctx none st
      else
        -- an opaque multi-output producer: the outputs stay unwired
        walkApp h e ctx none st
    else
      walkApp h e ctx (Target.asOne? target) st

/-- The application readings, in order: attested mint, gated ingest, erasure,
consuming application, configuration read, opaque. -/
partial def walkApp (h : HarvestCtx) (e : Expr) (ctx : BinderCtx)
    (t1 : Option (String × String × Bool)) (st : WalkSt) : MetaM WalkSt := do
  let fn := e.getAppFn
  let args := e.getAppArgs
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
      let st := sourceAt h (.attested reason) kind t1 st
      return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- a gated ingest: raw data admitted through a check
  if h.ingestConsts.contains c then
    let kind := (t1.map fun (_, k, _) => k).getD "_"
    let st := sourceAt h .gated kind t1 st
    return ← args.foldlM (fun st a => walk h a ctx none st) st
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
  -- a configuration read: the identity wire from the constant's port node
  if h.configConsts.contains c then
    if let some (n, k, owned) := t1 then
      let st := st.copyTo h.site (← refName ctx e) n k owned
      return ← args.foldlM (fun st a => walk h a ctx none st) st
  -- opaque: no reading applies (a raw mint, a sub-step call, a bare computation)
  let st := opaqueTarget h t1 st
  args.foldlM (fun st a => walk h a ctx none st) st

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

/-- The harvest of one step: the graph's constituents, with the two markers
(`assumed` / `partialIncidence`) the graph value does not carry. `provenance` is the
constructed object; the renderings below are projections of this one producer. -/
structure StepGraph where
  ports : List (Port String String)
  intros : List (Intro String String)
  occs : Array StepOccurrence
  exits : List String

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

/-- The full graph rendering: ports, introductions, wired occurrences (markers kept),
exits, and the evaluated well-formedness verdict. -/
def StepGraph.renderLines (s : StepGraph) : List String :=
  s.ports.map renderPort
    ++ s.intros.map renderIntro
    ++ (s.occs.map (·.renderWired)).toList
    ++ s.exits.map (fun n => s!"exit {n}")
    ++ [s!"well-formed: {s.provenance.wellFormed}"]

/-- Construct the step graph of a declaration: the interface off the signature (inputs
in signature order, configuration reads in body order, outputs in component order —
a binder or component at a non-carrier type is no port, and output node names keep
component positions), then the wiring off the elaborated value. -/
def stepGraphOf (decl : Name) : MetaM StepGraph := do
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
        t.decl == decl && t.tier == .kindConst }
  Meta.forallTelescope info.type fun fvars resultTy => do
    let mut ports : Array (Port String String) := #[]
    for fv in fvars do
      let ty ← fv.fvarId!.getType
      if let some k ← carrierKind? env carriers [] ty then
        ports := ports.push
          { node := toString (← fv.fvarId!.getUserName), kind := k, dir := .input }
    if let some v := info.value? then
      for c in configReads cfgConsts v do
        let some ci := env.find? c | continue
        let node := toString (← Meta.ppExpr (mkConst c (ci.levelParams.map mkLevelParam)))
        let kind ← Meta.forallTelescope ci.type fun _ resTy =>
          return (← carrierKind? env carriers [] resTy).getD "_"
        ports := ports.push { node := node, kind := kind, dir := .config }
    let comps := prodComponents resultTy
    let mut outSlots : Array (Option (String × String)) := #[]
    for i in [0:comps.size] do
      match ← carrierKind? env carriers [] comps[i]! with
      | some k =>
        let node := if comps.size == 1 then "result" else s!"result.{i + 1}"
        ports := ports.push { node := node, kind := k, dir := .output }
        outSlots := outSlots.push (some (node, k))
      | none => outSlots := outSlots.push none
    let st ← match info.value? with
      | none => pure {}
      | some v =>
        Meta.lambdaTelescope v fun _ body => do
          let rootTarget : Option Target :=
            if comps.size == 1 then
              outSlots[0]!.map fun (n, k) => .one n k false
            else if outSlots.any (·.isSome) then
              some (.tuple outSlots.toList)
            else
              none
          walk h body [] rootTarget {}
    return { ports := ports.toList, intros := st.intros.toList, occs := st.occs,
             exits := st.exits.toList }

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
pinning. Assumed occurrences (hypothesis- or instance-binder licenses) and identity
wires are the graph's business, not the enumeration's. -/
elab "#kind_occurrences " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let occs := (← stepGraphOf decl).occs.filter fun o =>
    !o.assumed && !(o.occ.family matches .copy)
  if occs.isEmpty then
    logInfo m!"no inline kind occurrences in '{decl}'"
  else
    let lines := occs.toList.map (·.render)
    logInfo m!"inline kind occurrences in '{decl}':\n{String.intercalate "\n" lines}"

open Elab Command in
/-- `#kind_ports d` prints every port `d`'s kind-typed signature states — inputs,
configuration reads, outputs, each with its stated kind — as a single `info` message
suitable for `#guard_msgs` pinning. -/
elab "#kind_ports " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let ports := (← stepGraphOf decl).ports
  if ports.isEmpty then
    logInfo m!"no kind ports in '{decl}'"
  else
    let lines := ports.map renderPort
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

end PropertyKindCalculus.KindIncidence
