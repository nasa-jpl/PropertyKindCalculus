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
    the edges sit in the theorem's conclusion, conjunctions included; the *type* scan
    (`collectEdges` over the conclusion alone — a witness taken as a *hypothesis* is
    assumed, not authored) sees them;
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
both sides share: the edge specs — each family's law, argument roles and formatter, the
one registry every audit layer derives its tables from — the binder-type
instantiation the per-declaration reading keys on (`instantiatedBinderTypes`, the
twin of `instantiatedConclusion`), and the author attribution of the elaborator's
auxiliaries (`parentOf`) every walk credits its rows by.
-/

module

public import Lean
public import PropertyKindCalculus.QuantityFunction
public meta import PropertyKindCalculus.QuantityFunction
public import PropertyKindCalculus.OperatorTable
public meta import PropertyKindCalculus.OperatorTable

-- Same-module helpers serve both the command elaborators below and runtime callers, so the
-- phase check is relaxed for this file (the module system's mixed-use escape; imports are
-- still checked and take `public meta import`).
set_option compiler.relaxedMetaCheck true

public section Interface

namespace PropertyKindCalculus.KindEdges

open Lean

/-- The law a witness family states — the shape of its kind equation. Every reader of
`specs` keys on it (the dimensional rule, the graph roles, the interchange family), so
each is a total match that a family added to the registry cannot silently fall out of. -/
inductive EdgeLaw where
  /-- `k₁ · k₂ → k`. -/
  | product
  /-- `k₁ / k₂ → k`. -/
  | quotient
  /-- `1 / k₁ → k₂`. -/
  | reciprocal
  /-- `transcendental : k₁ → k₂`. -/
  | transcendental
  /-- `k₁ ^ p → k₂`, the exponent `p` a rational, not a kind. -/
  | power
  /-- `reference : k₁ → k₂`: a re-expression relates the value converted; the two
  reference quantities are the edge's configuration, not further operands. -/
  | reference
  /-- `k ± k → k`: the witness names one kind, which is both operands and the result. -/
  | additive
deriving DecidableEq, Repr, Inhabited

/-- One scanned edge family — the registry entry every audit layer reads: the witness
`Prop`'s constant, its full application arity, the law it states, the argument positions
of its operand kinds and result kind, the exponent's position (a `power` family only),
whether it is an operator-table class rather than a witness `Prop`, and how to render an
application's pretty-printed arguments as a kind equation. -/
structure EdgeSpec where
  const : Name
  arity : Nat
  law : EdgeLaw
  operands : Array Nat
  result : Nat
  exponent : Option Nat := none
  isTable : Bool := false
  fmt : Array String → String

/-- The witness families of the core calculus. `PowerKind`'s first argument is the
rational exponent (not a kind); `DifferenceKind`'s one argument fills every role; the
formatters place each family's arguments as the equation reads. -/
def specs : Array EdgeSpec := #[
  { const := ``PropertyKindCalculus.ProductKind, arity := 3, law := .product,
    operands := #[0, 1], result := 2, fmt := fun a => s!"{a[0]!} · {a[1]!} → {a[2]!}" },
  { const := ``PropertyKindCalculus.QuotientKind, arity := 3, law := .quotient,
    operands := #[0, 1], result := 2, fmt := fun a => s!"{a[0]!} / {a[1]!} → {a[2]!}" },
  { const := ``PropertyKindCalculus.ReciprocalKind, arity := 2, law := .reciprocal,
    operands := #[0], result := 1, fmt := fun a => s!"1 / {a[0]!} → {a[1]!}" },
  { const := ``PropertyKindCalculus.TranscendentalKind, arity := 2, law := .transcendental,
    operands := #[0], result := 1, fmt := fun a => s!"transcendental : {a[0]!} → {a[1]!}" },
  { const := ``PropertyKindCalculus.PowerKind, arity := 3, law := .power,
    operands := #[1], result := 2, exponent := some 0,
    fmt := fun a => s!"{a[1]!} ^ {a[0]!} → {a[2]!}" },
  { const := ``PropertyKindCalculus.ReferenceKind, arity := 2, law := .reference,
    operands := #[0], result := 1, fmt := fun a => s!"reference : {a[0]!} → {a[1]!}" },
  { const := ``PropertyKindCalculus.DifferenceKind, arity := 1, law := .additive,
    operands := #[0, 0], result := 0, fmt := fun a => s!"{a[0]!} ± {a[0]!} → {a[0]!}" },
  { const := ``PropertyKindCalculus.KindMul, arity := 3, law := .product, isTable := true,
    operands := #[0, 1], result := 2, fmt := fun a => s!"[table] {a[0]!} · {a[1]!} → {a[2]!}" },
  { const := ``PropertyKindCalculus.KindDiv, arity := 3, law := .quotient, isTable := true,
    operands := #[0, 1], result := 2, fmt := fun a => s!"[table] {a[0]!} / {a[1]!} → {a[2]!}" }]

/-- The registry entry of a witness constant, if it heads a scanned family. -/
def specOf? (c : Name) : Option EdgeSpec := specs.find? (·.const == c)

/-- The registry entry a fully-applied witness application states, if any. -/
def specOfApp? (e : Expr) : Option EdgeSpec :=
  specs.find? fun spec => e.isAppOfArity spec.const spec.arity

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

/-- The witness `Prop` families — the conclusions the inline scan recognizes: every
`specs` entry that is not a table class. The table classes are deliberately absent: a
`KindMul`/`KindDiv` registration is an instance, owned by the type scan, and an instance
*reference* in a value is resolution, not authorship. -/
def propFamilies : Array Name := (specs.filter (!·.isTable)).map (·.const)

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

/-- Is `s` a name component the elaborator appends to a declaration it works on, rather than
one a person wrote? The shapes are Lean's own: a `_`-prefixed component (`_proof_1`,
`_unsafe_rec`, `_cstage1`, …), a `match_` / `eq_` / `proof_` prefix followed by nothing but
digits and underscores (`match_1`, `eq_2`, `proof_1_3` — the `Name.isInternalDetail` test),
and the `eq_def` / `eq_unfold` unfolding lemmas. A user theorem that merely shares the prefix
(`eq_mul_of_isProduct`, `match_on_scale`) is not one. -/
def isAuxComponent (s : String) : Bool :=
  s.startsWith "_"
    || ["match_", "eq_", "proof_"].any fun pre =>
         (s.dropPrefix? pre).any (·.all fun c => c.isDigit || c == '_')
    || s == "eq_def" || s == "eq_unfold"

/-- Strip the elaborator's name components (`isAuxComponent`, plus numeric suffixes) so a
lifted call-site witness or mint is attributed to the definition that authored it. Shared by
every audit walk (`harvest` and its renderers, the boundary audit's `boundarySites`, the
index's `isAuthored`) so they all credit the elaborator's auxiliaries to the same author. -/
def parentOf (n : Name) : Name :=
  match n with
  | .str p s => if isAuxComponent s then parentOf p else n
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

Every edge enumeration is a *renderer* over **one** environment walk, `harvest`: `#kind_edges`
below (through `edgesMentioning`), the kind index's Algebra column (`edgesByKind`), the
dimensional gate (`DimensionalCoverage.coverageRows`), and the kind digraph `#kind_scc` and
`#kind_footprint` read (`Graph.KindGraph.kindGraphOf`). The split exists for the same reason
`BoundaryAudit.boundarySites` exists: the enumeration is wanted both as the `info` message an author
reads and as table rows a document renders. Because a kind's authored edges *are* the statement of
what may be done with it algebraically, this is the column that makes a rendered kind index worth
reading — see `PropertyKindCalculus.Index`. Sharing the walk is what makes the reports agree on
what an authored edge *is*: `collectEdges` and `collectInlineEdges` are called from here alone. -/

/-- Does a declaration's type mention a scanned family at all, table classes included? The
cheap pre-check that keeps the type scan from opening a telescope on every constant. -/
def typeMentionsSpec (t : Expr) : Bool :=
  (t.find? fun s => specs.any (fun spec => s.isConstOf spec.const)).isSome

/-- **The one edge-harvest walk.** For every constant of a family-reaching module
(`producerModules`) whose authoring declaration (`parentOf`) passes `keep`, both channels are
scanned and each `(family, arguments)` pair found is handed to `render`, which runs *inside the
telescope that binds the pair's variables* (so a parametric kind prints as its binder name) and
returns `none` to drop the pair:

  * the **type scan** reads the declaration's **conclusion** only (`forallTelescopeReducing`,
    then `collectEdges`): a named witness theorem, a lifted `._proof_N` auxiliary, an
    operator-table instance. A witness taken as a *hypothesis* (`(h : ProductKind …) → …`) is
    assumed, not authored, and is deliberately not an edge — the same line the body scan
    draws for a free-variable-headed witness;
  * the **body scan** reads the value of every `bodyScannable` definition under its own
    telescope (`collectInlineEdges`): the call-site witnesses the elaborator left inline or
    shared.

The result is in walk order, the type channel before the body channel of each constant,
undeduplicated: each renderer owns its own dedup key (per author, per equation, per kind). -/
def harvest {α : Type} (keep : Name → Bool)
    (render : EdgeSpec → Array Expr → MetaM (Option α)) : MetaM (Array (Name × α)) := do
  let env ← getEnv
  let reachable := producerModules env
  let mut out : Array (Name × α) := #[]
  for (name, info) in env.constants.toList do
    -- Neither scan can find anything outside the family-reaching modules (`producerModules`).
    if let some idx := env.getModuleIdxFor? name then
      unless reachable.contains idx.toNat do continue
    let author := parentOf name
    unless keep author do continue
    let mut found : Array α := #[]
    if typeMentionsSpec info.type then
      found ← Meta.forallTelescopeReducing info.type fun _ concl =>
        (collectEdges concl #[]).filterMapM fun (spec, args) => render spec args
    if ← bodyScannable reachable env name info then
      found := found ++ (← Meta.lambdaTelescope info.value! fun _ body =>
        (collectInlineEdges env body #[]).filterMapM fun (spec, args) => render spec args)
    for r in found do
      out := out.push (author, r)
  return out

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
  let found ← harvest (fun _ => true) fun spec args => do
    unless args.any (·.isConstOf target) do return none
    let pps ← args.mapM fun a => return toString (← Meta.ppExpr a)
    return some (spec.fmt pps)
  let mut seen : Std.HashSet String := {}
  let mut out : Array KindEdge := #[]
  for (author, edge) in found do
    let e : KindEdge := { author, edge }
    let key := s!"{e.author}: {e.edge}"
    unless seen.contains key do
      seen := seen.insert key
      out := out.push e
  return out.qsort (fun a b => s!"{a.author}: {a.edge}" < s!"{b.author}: {b.edge}")

/-! ### Grouping a kind's edges for a rendered cell

`edgesByKind` deduplicates by *(author, edge)* — the right identity for the per-author report,
and the wrong one for a rendered cell, which drops the author and would show one copy of
`a · b → c` per authoring declaration. The renderers therefore share one grouping: deduplicate
by the equation alone, then split by the side the kind stands on — the edges **producing** it
(it is the right-hand side) from the edges **consuming** it (it enters as an operand). -/

/-- The right-hand side of a rendered edge. Every formatter in `specs` ends with `→ <result>`,
so the segment after the last ` → ` is the result kind. -/
def edgeRhs (e : String) : String := ((e.splitOn " → ").getLast?).getD ""

/-- The edges mentioning the kind displayed as `short`, deduplicated by equation and grouped for
rendering: the `produced` group (the kind is the result) and the `consumed` group (the kind is an
operand), each labeled with its count, empty groups omitted. Each equation carries one authoring
declaration — the alphabetically first, when several authored the same equation — so a rendered
cell can link the equation to a declaration that authored it. The consumed group sorts by result
first, so edges yielding a common kind sit together; an edge with the kind on both sides counts
as produced. -/
def groupEdges (short : String) (edges : Array KindEdge) :
    Array (String × Array (String × Name)) :=
  let eqs := (edges.map (·.edge)).toList.eraseDups
  let authorOf (e : String) : Name := Id.run do
    let mut best : Option Name := none
    for k in edges do
      if k.edge == e then
        best := some <| match best with
          | some b => if toString k.author < toString b then k.author else b
          | none => k.author
    return best.getD .anonymous
  let produced := ((eqs.filter (edgeRhs · == short)).toArray.qsort (· < ·)).map
    fun e => (e, authorOf e)
  let consumed := ((eqs.filter (edgeRhs · != short)).toArray.qsort (fun a b =>
      edgeRhs a < edgeRhs b || (edgeRhs a == edgeRhs b && a < b))).map
    fun e => (e, authorOf e)
  (if produced.isEmpty then #[] else #[(s!"produced ({produced.size})", produced)]) ++
  (if consumed.isEmpty then #[] else #[(s!"consumed ({consumed.size})", consumed)])

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
  let wanted : Std.HashSet Name := targets.foldl (·.insert ·) {}
  -- Which of the targets does an edge mention? Rendered only if at least one, by short name.
  let found ← harvest (fun _ => true) fun spec args => do
    let mentioned := args.filterMap fun a =>
      match a with
      | .const c _ => if wanted.contains c then some c else none
      | _          => none
    if mentioned.isEmpty then return none
    let pps ← args.mapM fun a =>
      match a with
      | .const (.str _ s) _ => return s
      | _                   => return toString (← Meta.ppExpr a)
    return some (mentioned, spec.fmt pps)
  let mut acc : Std.HashMap Name (Array KindEdge) := {}
  for t in targets do acc := acc.insert t #[]
  for (author, (mentioned, edge)) in found do
    let e : KindEdge := { author, edge }
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

end Interface
