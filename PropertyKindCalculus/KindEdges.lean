/-
# `#kind_edges` — enumerate the authored kind-algebra edges of a kind

The audit command the trust model calls for (`QuantityClassification`, "The trust model —
witnesses are authored, not checked"): a witness is to the kind algebra what an axiom is
to a proof, so soundness is judged by *enumerating* the authored witnesses — and this
command is that enumeration, the kind-algebra analog of `#print axioms`.

    #kind_edges myKind

prints every authored edge mentioning `myKind`, in one sorted `info` message (so a probe
file can pin the complete registry with `#guard_msgs`). Three authoring styles are all
found by two complementary scans:

  * **named witness theorems** (`theorem jacobian_column_kinds : ProductKind … ∧ …`) —
    the edges sit in the theorem's type, conjunctions included; the *type* scan
    (`collectEdges`) sees them;
  * **call-site witnesses** (`Quantity.mul (ProductKind.ofRatio k₁ k₂ k) x y` inside a
    definition body) — found on both of the elaborator's spellings. When the inline
    proof is lifted into an auxiliary theorem (`<def>._proof_N`) its *type is the edge
    itself*, so the type scan sees it. But nothing obliges the elaborator to lift — a
    witness it leaves inline lives only in the body, invisible to any type scan — so the
    *body* scan (`collectProducedEdges`) reads such an edge directly off the
    witness-producer application (`producers`). Either way the line is attributed to the
    authoring definition (internal name components stripped), and the two channels
    render identically, so a pinned report is stable against the lifting heuristic;
  * **operator-table registrations** (`instance : KindMul k₁ k₂ k := …`) — the edge is
    the instance's type, printed with a `[table]` marker (`#instances KindMul` lists the
    same registrations per class; this command lists them per *kind*).

The edge families scanned are the witness `Prop`s of the core calculus: `ProductKind`,
`QuotientKind`, `ReciprocalKind` (`QuantityClassification`), `TranscendentalKind`,
`PowerKind` (`QuantityFunction`), and the table classes `KindMul`/`KindDiv`
(`OperatorTable`).
-/
import Lean
import PropertyKindCalculus.QuantityFunction
import PropertyKindCalculus.OperatorTable

namespace PropertyKindCalculus.KindEdges

open Lean

/-- One scanned edge family: the witness `Prop`'s constant, its full application arity,
and how to render an application's pretty-printed arguments as a kind equation. -/
structure EdgeSpec where
  const : Name
  arity : Nat
  fmt : Array String → String

/-- The witness families of the core calculus. `PowerKind`'s first argument is the
rational exponent (not a kind); the formatters place each family's arguments as the
equation reads. -/
def specs : Array EdgeSpec := #[
  ⟨``PropertyKindCalculus.ProductKind, 3, fun a => s!"{a[0]!} · {a[1]!} → {a[2]!}"⟩,
  ⟨``PropertyKindCalculus.QuotientKind, 3, fun a => s!"{a[0]!} / {a[1]!} → {a[2]!}"⟩,
  ⟨``PropertyKindCalculus.ReciprocalKind, 2, fun a => s!"1 / {a[0]!} → {a[1]!}"⟩,
  ⟨``PropertyKindCalculus.TranscendentalKind, 2, fun a => s!"transcendental : {a[0]!} → {a[1]!}"⟩,
  ⟨``PropertyKindCalculus.PowerKind, 3, fun a => s!"{a[1]!} ^ {a[0]!} → {a[2]!}"⟩,
  ⟨``PropertyKindCalculus.KindMul, 3, fun a => s!"[table] {a[0]!} · {a[1]!} → {a[2]!}"⟩,
  ⟨``PropertyKindCalculus.KindDiv, 3, fun a => s!"[table] {a[0]!} / {a[1]!} → {a[2]!}"⟩]

/-- Collect every fully-applied witness `Prop` occurring anywhere in an expression
(binder types, conjuncts, and nested applications included). -/
partial def collectEdges (e : Expr) (acc : Array (EdgeSpec × Array Expr)) :
    Array (EdgeSpec × Array Expr) :=
  let acc := Id.run do
    for spec in specs do
      if e.isAppOfArity spec.const spec.arity then
        return acc.push (spec, e.getAppArgs)
    return acc
  match e with
  | .app f a => collectEdges a (collectEdges f acc)
  | .lam _ t b _ => collectEdges b (collectEdges t acc)
  | .forallE _ t b _ => collectEdges b (collectEdges t acc)
  | .letE _ t v b _ => collectEdges b (collectEdges v (collectEdges t acc))
  | .mdata _ b => collectEdges b acc
  | .proj _ _ b => collectEdges b acc
  | _ => acc

/-- A witness *producer*: a constructor or smart constructor whose application inside a
definition body builds an edge-family witness inline. The elaborator MAY lift such a proof
into a `._proof_N` auxiliary — whose type `collectEdges` then sees — but it is under no
obligation to, and a witness it leaves inline lives only in the body. `family` names the
scanned family whose formatter renders the edge; `argIdxs` picks the producer's arguments
in that formatter's order. -/
structure ProducerSpec where
  const : Name
  arity : Nat
  family : Name
  argIdxs : Array Nat

/-- The inline producers of the scanned families: each witness `Prop`'s structure
constructor (the anonymous `⟨…⟩`) and its smart constructor where one exists. The table
classes are absent by design — their registrations are instances, which the type scan
owns. -/
def producers : Array ProducerSpec := #[
  ⟨``PropertyKindCalculus.ProductKind.mk, 6, ``PropertyKindCalculus.ProductKind, #[0, 1, 2]⟩,
  ⟨``PropertyKindCalculus.ProductKind.ofRatio, 6, ``PropertyKindCalculus.ProductKind, #[0, 1, 2]⟩,
  ⟨``PropertyKindCalculus.QuotientKind.mk, 6, ``PropertyKindCalculus.QuotientKind, #[0, 1, 2]⟩,
  ⟨``PropertyKindCalculus.QuotientKind.ofRatio, 6, ``PropertyKindCalculus.QuotientKind, #[0, 1, 2]⟩,
  ⟨``PropertyKindCalculus.ReciprocalKind.mk, 4, ``PropertyKindCalculus.ReciprocalKind, #[0, 1]⟩,
  ⟨``PropertyKindCalculus.TranscendentalKind.mk, 4, ``PropertyKindCalculus.TranscendentalKind, #[0, 1]⟩,
  ⟨``PropertyKindCalculus.PowerKind.mk, 5, ``PropertyKindCalculus.PowerKind, #[0, 1, 2]⟩,
  ⟨``PropertyKindCalculus.PowerKind.ofRatio, 5, ``PropertyKindCalculus.PowerKind, #[0, 1, 2]⟩]

/-- Collect every witness-producer application in an expression — the *body* complement of
`collectEdges`' type scan, for inline call-site witnesses the elaborator did not lift.
Same result shape as `collectEdges`, arguments already in the family formatter's order. -/
partial def collectProducedEdges (e : Expr) (acc : Array (EdgeSpec × Array Expr)) :
    Array (EdgeSpec × Array Expr) :=
  let acc := Id.run do
    for p in producers do
      if e.isAppOfArity p.const p.arity then
        let some spec := specs.find? (·.const == p.family) | return acc
        let args := e.getAppArgs
        return acc.push (spec, p.argIdxs.map (fun i => args[i]!))
    return acc
  match e with
  | .app f a => collectProducedEdges a (collectProducedEdges f acc)
  | .lam _ t b _ => collectProducedEdges b (collectProducedEdges t acc)
  | .forallE _ t b _ => collectProducedEdges b (collectProducedEdges t acc)
  | .letE _ t v b _ => collectProducedEdges b (collectProducedEdges v (collectProducedEdges t acc))
  | .mdata _ b => collectProducedEdges b acc
  | .proj _ _ b => collectProducedEdges b acc
  | _ => acc

/-- Does the expression mention a producer constant at all? The value-level pre-filter of
the body scan. -/
def mentionsProducer (e : Expr) : Bool :=
  (e.find? fun s => producers.any (fun p => s.isConstOf p.const)).isSome

/-- The module indices whose import closure contains the module defining the witness
families — the only modules whose definitions can possibly apply a producer. The body
scan skips every other module's constants without touching their values: walking every
value in an `import Lean` environment costs hundreds of millions of allocation
heartbeats, and this filter reduces the walk to the calculus's own downstream. Constants
of the module currently elaborating have no module index and are always scanned. The
header's module arrays are in load order (an import precedes its importer), which is what
makes the single forward pass a fixpoint. -/
def producerModules (env : Environment) : Std.HashSet Nat := Id.run do
  let some target := env.getModuleIdxFor? ``PropertyKindCalculus.ProductKind
    | return {}
  let n := env.header.moduleData.size
  let mut idxOf : Std.HashMap Name Nat := {}
  for i in [0:n] do
    idxOf := idxOf.insert env.header.moduleNames[i]! i
  let mut reaches : Std.HashSet Nat := {}
  for i in [0:n] do
    if i == target.toNat
        || env.header.moduleData[i]!.imports.any
             (fun imp => (idxOf.get? imp.module).map reaches.contains |>.getD false) then
      reaches := reaches.insert i
  return reaches

/-- Is this constant one the body scan should read? Definitions only: a producer inside a
*theorem*'s proof term proves the theorem's stated type, which the type scan already
lists — the body scan is for computations that consume a witness inline. Instances are
skipped for the same reason: an instance's value *builds* its registration, and the
registration — the instance's type — is the authored edge, owned by the type scan (else
every `[table]` row would repeat as a naked edge read off the value). Compiler-generated
machinery (`recOn`/`casesOn`, `._flat_ctor`, matchers) is skipped: the witness structures'
own plumbing applies their constructors without authoring anything, and a matcher's
branches live in its caller's value, not the matcher's. `reachable` is
`producerModules env`, computed once per walk. -/
def bodyScannable (reachable : Std.HashSet Nat) (env : Environment)
    (name : Name) (info : ConstantInfo) : MetaM Bool := do
  unless info matches .defnInfo _ do return false
  if let some idx := env.getModuleIdxFor? name then
    unless reachable.contains idx.toNat do return false
  if name.isInternalDetail || isAuxRecursor env name then return false
  unless (info.value?.map mentionsProducer).getD false do return false
  return !(← Meta.isInstance name)

/-- Strip internal name components (`._proof_N`, numeric suffixes) so a lifted call-site
witness is attributed to the definition that authored it. -/
def parentOf (n : Name) : Name :=
  match n with
  | .str p s => if s.startsWith "_" then parentOf p else n
  | .num p _ => parentOf p
  | _ => n

/-! ## The harvest

`#kind_edges` below is a *renderer* over `edgesMentioning`. The split exists for the same reason
`BoundaryAudit.boundarySites` exists: the enumeration is wanted both as the `info` message an author
reads and as table rows a document renders. Because a kind's authored edges *are* the statement of
what may be done with it algebraically, this is the column that makes a rendered kind index worth
reading — see `PropertyKindCalculus.Index`. -/

/-- One authored kind-algebra edge: the declaration that authored it (a named witness theorem, the
definition a call-site witness was lifted out of, or an operator-table instance) and the edge itself,
already rendered as a kind equation by its family's formatter. -/
structure KindEdge where
  /-- The authoring declaration. -/
  author : Name
  /-- The edge, as `a · b → c`, `1 / a → b`, `[table] a · b → c`, … -/
  edge : String
deriving Repr, Inhabited, BEq, Hashable

/-- Every authored edge in the environment mentioning the kind constant `target`, deduplicated and
sorted by `"author: edge"` — the order the pinned report prints. -/
def edgesMentioning (target : Name) : MetaM (Array KindEdge) := do
  let env ← getEnv
  let reachable := producerModules env
  let mut seen : Std.HashSet String := {}
  let mut out : Array KindEdge := #[]
  for (name, info) in env.constants.toList do
    -- The type scan: named theorems, lifted call-site auxiliaries, instances …
    let mut rendered : Array String := #[]
    for (spec, args) in collectEdges info.type #[] do
      if args.any (·.isConstOf target) then
        let pps ← args.mapM fun a => return toString (← Meta.ppExpr a)
        rendered := rendered.push (spec.fmt pps)
    -- … and the body scan: inline witnesses the elaborator left unlifted. Rendered
    -- inside the value's own telescope so parametric kinds print with their binder
    -- names — the same spelling the type scan gives a lifted auxiliary's telescope,
    -- which is what lets the dedup collapse the two channels.
    if ← bodyScannable reachable env name info then
      let fromBody ← Meta.lambdaTelescope info.value! fun _ body =>
        (collectProducedEdges body #[]).filterMapM fun (spec, args) => do
          if args.any (·.isConstOf target) then
            let pps ← args.mapM fun a => return toString (← Meta.ppExpr a)
            return some (spec.fmt pps)
          else
            return none
      rendered := rendered ++ fromBody
    for edge in rendered do
      let e : KindEdge := { author := parentOf name, edge }
      let key := s!"{e.author}: {e.edge}"
      unless seen.contains key do
        seen := seen.insert key
        out := out.push e
  return out.qsort (fun a b => s!"{a.author}: {a.edge}" < s!"{b.author}: {b.edge}")

/-- The edges mentioning **each** of `targets`, in one environment walk.

The single-target `edgesMentioning` is the right shape for `#kind_edges`, which asks about one kind.
It is the wrong shape for an index over a hundred kinds: that would walk the environment a hundred
times. A rendered kind table wants this one instead. An edge mentioning two kinds is listed under
both, which is what makes the column readable from either end.

Kinds are rendered by their **last name component** here, where `#kind_edges` prints them fully
qualified. That is not an inconsistency to fix: `#kind_edges` is read in a file whose namespace is
open, where the qualified name disambiguates, while a table cell holding four edges of qualified
names is a paragraph of repeated prefixes with the content buried in it. The table is scoped to a
namespace already, so the short name is unambiguous there. -/
def edgesByKind (targets : Array Name) : MetaM (Std.HashMap Name (Array KindEdge)) := do
  let env ← getEnv
  let reachable := producerModules env
  let wanted : Std.HashSet Name := targets.foldl (·.insert ·) {}
  let mut acc : Std.HashMap Name (Array KindEdge) := {}
  for t in targets do acc := acc.insert t #[]
  for (name, info) in env.constants.toList do
    -- Both channels of `edgesMentioning`: the type scan, then the body scan for inline
    -- witnesses the elaborator left unlifted (rendered inside the value's telescope).
    let typeEdges := collectEdges info.type #[]
    let bodyEdges ← do
      if ← bodyScannable reachable env name info then
        Meta.lambdaTelescope info.value! fun _ body => do
          let found := collectProducedEdges body #[]
          found.mapM fun (spec, args) => do
            let mentioned := args.filterMap fun a =>
              match a with
              | .const c _ => if wanted.contains c then some c else none
              | _          => none
            let pps ← if mentioned.isEmpty then pure #[] else args.mapM fun a =>
              match a with
              | .const (.str _ s) _ => return s
              | _                   => return toString (← Meta.ppExpr a)
            return (spec, mentioned, pps)
      else
        pure #[]
    let typeRendered ← typeEdges.mapM fun (spec, args) => do
      -- Which of the targets does this edge mention? Compute the rendering only if at least one.
      let mentioned := args.filterMap fun a =>
        match a with
        | .const c _ => if wanted.contains c then some c else none
        | _          => none
      let pps ← if mentioned.isEmpty then pure #[] else args.mapM fun a =>
        match a with
        | .const (.str _ s) _ => return s
        | _                   => return toString (← Meta.ppExpr a)
      return (spec, mentioned, pps)
    for (spec, mentioned, pps) in typeRendered ++ bodyEdges do
      if mentioned.isEmpty then continue
      let e : KindEdge := { author := parentOf name, edge := spec.fmt pps }
      for c in mentioned.toList.eraseDups do
        acc := acc.insert c ((acc.getD c #[]).push e)
  return acc.fold (init := {}) fun m k v =>
    m.insert k ((v.toList.eraseDups).toArray.qsort
      (fun a b => s!"{a.author}: {a.edge}" < s!"{b.author}: {b.edge}"))

open Elab Command in
/-- `#kind_edges k` prints every authored kind-algebra edge in the environment that
mentions the kind constant `k` — sorted, deduplicated, one line per (author, edge) pair —
as a single `info` message suitable for `#guard_msgs` pinning. -/
elab "#kind_edges " id:ident : command => liftTermElabM do
  let target ← realizeGlobalConstNoOverload id
  let sorted := (← edgesMentioning target).map fun e => s!"{e.author}: {e.edge}"
  if sorted.isEmpty then
    logInfo m!"no authored kind edges mention '{target}'"
  else
    logInfo m!"authored kind edges mentioning '{target}':\n{String.intercalate "\n" sorted.toList}"

end PropertyKindCalculus.KindEdges
