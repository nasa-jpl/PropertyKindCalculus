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
    definition body) — found on every spelling the elaborator produces. It may lift the
    inline proof into an auxiliary theorem (`<def>._proof_N`) whose *type is the edge*
    (the type scan sees it), it may leave it inline, and it may **share** one auxiliary
    across alpha-equivalent witnesses of several definitions — the later definitions'
    values then hold nothing but a reference, and the type scan alone would attribute
    their edges to the first definition. The *body* scan (`collectInlineEdges`) closes
    both gaps: any constant-headed application whose instantiated conclusion is a
    witness-family `Prop` — the direct smart-constructor application, the lifted or
    shared auxiliary reference, the named-theorem reference — is an edge at its use
    site, attributed to the definition being scanned (internal name components
    stripped). The channels render identically, so a pinned report is stable against
    the elaborator's choice. A free-variable-headed witness is a *hypothesis* —
    assumed, not authored — and is not collected;
  * **operator-table registrations** (`instance : KindMul k₁ k₂ k := …`) — the edge is
    the instance's type, printed with a `[table]` marker (`#instances KindMul` lists the
    same registrations per class; this command lists them per *kind*).

The edge families scanned are the witness `Prop`s of the core calculus: `ProductKind`,
`QuotientKind`, `ReciprocalKind` (`QuantityClassification`), `TranscendentalKind`,
`PowerKind`, `ReferenceKind` (`QuantityFunction`), `DifferenceKind` (`Quantity`), and
the table classes `KindMul`/`KindDiv` (`OperatorTable`).

The *occurrence* reading of these same families — which values met at an edge, read per
declaration — lives in `KindIncidence`, together with the port and graph harvests built
on it: those readings are identified against the boundary audit's registries, and
importing the audit would put its meta-heavy bodies into this module's environment walk
in every consumer (`producerModules` below is the cost model). What stays here is what
both sides share: the edge specs and their formatters, and the binder-type
instantiation the per-declaration reading keys on (`instantiatedBinderTypes`, the
twin of `instantiatedConclusion`).
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
  ⟨``PropertyKindCalculus.ReferenceKind, 2, fun a => s!"reference : {a[0]!} → {a[1]!}"⟩,
  ⟨``PropertyKindCalculus.DifferenceKind, 1, fun a => s!"{a[0]!} ± {a[0]!} → {a[0]!}"⟩,
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

/-- The seven witness `Prop` families — the conclusions the inline scan recognizes. The
table classes are deliberately absent: a `KindMul`/`KindDiv` registration is an instance,
owned by the type scan, and an instance *reference* in a value is resolution, not
authorship. -/
def propFamilies : Array Name := #[
  ``PropertyKindCalculus.ProductKind,
  ``PropertyKindCalculus.QuotientKind,
  ``PropertyKindCalculus.ReciprocalKind,
  ``PropertyKindCalculus.TranscendentalKind,
  ``PropertyKindCalculus.PowerKind,
  ``PropertyKindCalculus.ReferenceKind,
  ``PropertyKindCalculus.DifferenceKind]

/-- Does a declaration's type mention a witness family at all? The cheap pre-check that
keeps the inline scan from instantiating every application head's type. -/
def typeMentionsFamily (t : Expr) : Bool :=
  (t.find? fun s => propFamilies.any (fun f => s.isConstOf f)).isSome

/-- Peel `args.size` quantifiers off a declaration's type, substituting the application's
arguments, and expose the conclusion (any leftover quantifiers are stripped, leaving
their variables loose — rendered as parametric). `none` when the type runs out of
quantifiers first. -/
def instantiatedConclusion (declTy : Expr) (args : Array Expr) : Option Expr := Id.run do
  let mut ty := declTy
  for a in args do
    match ty with
    | .forallE _ _ body _ => ty := body.instantiate1 a
    | _ => return none
  return some ty.getForallBody

/-- Collect every **inline edge** of an expression — the *body* complement of
`collectEdges`\' type scan. A constant-headed application whose instantiated conclusion
is a witness-family `Prop` *is* an edge at its use site, whatever spelling the elaborator
chose: the direct smart-constructor application (`ProductKind.ofRatio k₁ k₂ k …`), the
reference to a lifted `._proof_N` auxiliary, the reference to a **shared** auxiliary
(the elaborator dedups alpha-equivalent nested proofs of several definitions into one
auxiliary — the later definitions\' values then hold nothing but this reference, and the
type scan alone would attribute their edges to the first definition), and the reference
to a named witness theorem. A *free-variable*-headed witness is deliberately not
collected: that is a hypothesis — assumed, not authored. Returns the same shape as
`collectEdges`, arguments in the family formatter\'s order. -/
partial def collectInlineEdges (env : Environment) (e : Expr)
    (acc : Array (EdgeSpec × Array Expr)) : Array (EdgeSpec × Array Expr) :=
  let acc := Id.run do
    let fn := e.getAppFn
    let .const n _ := fn | return acc
    let some ci := env.find? n | return acc
    unless typeMentionsFamily ci.type do return acc
    let some concl := instantiatedConclusion ci.type e.getAppArgs | return acc
    for spec in specs do
      if propFamilies.contains spec.const && concl.isAppOfArity spec.const spec.arity then
        return acc.push (spec, concl.getAppArgs)
    return acc
  -- Recurse into the application's arguments (each argument's own spine is processed at
  -- its root — never into this spine's prefixes, which would re-read the edge partially
  -- applied), into a non-constant head, and under binders.
  match e with
  | .app .. =>
    let acc := if e.getAppFn.isConst then acc else collectInlineEdges env e.getAppFn acc
    e.getAppArgs.foldl (fun acc a => collectInlineEdges env a acc) acc
  | .lam _ t b _ => collectInlineEdges env b (collectInlineEdges env t acc)
  | .forallE _ t b _ => collectInlineEdges env b (collectInlineEdges env t acc)
  | .letE _ t v b _ =>
    collectInlineEdges env b (collectInlineEdges env v (collectInlineEdges env t acc))
  | .mdata _ b => collectInlineEdges env b acc
  | .proj _ _ b => collectInlineEdges env b acc
  | _ => acc

/-- The module indices whose import closure contains the module defining the witness
families — the only modules whose declarations can possibly reference them. *Both* scans
skip every other module's constants: a type, like a body, can only mention a family
whose defining module its own module transitively imports, so the walk scales with the
calculus's own downstream, not with the environment (type-scanning every constant of an
`import Lean` environment alone costs a default command's whole heartbeat budget, and
walking every value costs hundreds of millions of allocation heartbeats). Constants
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
  return !(← Meta.isInstance name)

/-- Strip internal name components (`._proof_N`, numeric suffixes) so a lifted call-site
witness is attributed to the definition that authored it. -/
def parentOf (n : Name) : Name :=
  match n with
  | .str p s => if s.startsWith "_" then parentOf p else n
  | .num p _ => parentOf p
  | _ => n

/-- Peel `args.size` quantifiers off a declaration's type as `instantiatedConclusion`
does, but return the *binder types* passed on the way, each instantiated with the
preceding arguments — position `i` is the type the application's `i`-th argument is
checked against. `none` when the type runs out of quantifiers first. This is what the
per-declaration readings in `KindIncidence` key on: a consuming application's edge sits
in its instantiated binder types, whatever the witness argument's own spelling. -/
def instantiatedBinderTypes (declTy : Expr) (args : Array Expr) : Option (Array Expr) :=
  Id.run do
    let mut ty := declTy
    let mut out : Array Expr := #[]
    for a in args do
      match ty with
      | .forallE _ d body _ =>
        out := out.push d
        ty := body.instantiate1 a
      | _ => return none
    return some out

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
    -- Neither scan can find anything outside the family-reaching modules (`producerModules`).
    if let some idx := env.getModuleIdxFor? name then
      unless reachable.contains idx.toNat do continue
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
        (collectInlineEdges env body #[]).filterMapM fun (spec, args) => do
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
    -- Neither scan can find anything outside the family-reaching modules (`producerModules`).
    if let some idx := env.getModuleIdxFor? name then
      unless reachable.contains idx.toNat do continue
    -- Both channels of `edgesMentioning`: the type scan, then the body scan for inline
    -- witnesses the elaborator left unlifted (rendered inside the value's telescope).
    let typeEdges := collectEdges info.type #[]
    let bodyEdges ← do
      if ← bodyScannable reachable env name info then
        Meta.lambdaTelescope info.value! fun _ body => do
          let found := collectInlineEdges env body #[]
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
