/-
# `#kind_edges` — enumerate the authored kind-algebra edges of a kind

The audit command the trust model calls for (`QuantityClassification`, "The trust model —
witnesses are authored, not checked"): a witness is to the kind algebra what an axiom is
to a proof, so soundness is judged by *enumerating* the authored witnesses — and this
command is that enumeration, the kind-algebra analog of `#print axioms`.

    #kind_edges myKind

prints every authored edge mentioning `myKind`, in one sorted `info` message (so a probe
file can pin the complete registry with `#guard_msgs`). Three authoring styles are all
found by a single scan over constant *types*:

  * **named witness theorems** (`theorem jacobian_column_kinds : ProductKind … ∧ …`) —
    the edges sit in the theorem's type, conjunctions included;
  * **call-site witnesses** (`Quantity.mul (ProductKind.ofRatio k₁ k₂ k) x y` inside a
    definition body) — Lean lifts each inline proof into an auxiliary theorem
    (`<def>._proof_N`) whose *type is the edge itself*, so the type scan sees it; the
    line is attributed to the authoring definition (internal name components stripped).
    A *body* scan would find nothing: bodies hold only references to those auxiliaries;
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
  let mut seen : Std.HashSet String := {}
  let mut out : Array KindEdge := #[]
  for (name, info) in env.constants.toList do
    for (spec, args) in collectEdges info.type #[] do
      if args.any (·.isConstOf target) then
        let pps ← args.mapM fun a => return toString (← Meta.ppExpr a)
        let e : KindEdge := { author := parentOf name, edge := spec.fmt pps }
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
  let wanted : Std.HashSet Name := targets.foldl (·.insert ·) {}
  let mut acc : Std.HashMap Name (Array KindEdge) := {}
  for t in targets do acc := acc.insert t #[]
  for (name, info) in env.constants.toList do
    for (spec, args) in collectEdges info.type #[] do
      -- Which of the targets does this edge mention? Compute the rendering only if at least one.
      let mentioned := args.filterMap fun a =>
        match a with
        | .const c _ => if wanted.contains c then some c else none
        | _          => none
      if mentioned.isEmpty then continue
      let pps ← args.mapM fun a =>
        match a with
        | .const (.str _ s) _ => return s
        | _                   => return toString (← Meta.ppExpr a)
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
