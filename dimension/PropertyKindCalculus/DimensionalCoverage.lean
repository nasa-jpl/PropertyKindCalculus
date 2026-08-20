/-
# DimensionalCoverage — `#kind_dimensional_coverage`, the dimensional cross-check of the kind algebra

The trust model of the core calculus is that witnesses are *authored, not checked*: a
`ProductKind k₁ k₂ k` is an axiom of the kind algebra, and `#kind_edges` is the audit that
enumerates those axioms. But one layer *can* check them: the `Dimension` functor. A wrong edge
whose kinds carry genuine dimensions is **refutable** — `ω · τ → ω` cannot cohere, because
`T⁻¹ · T ≠ T⁻¹` — and the curated interaction algebras (`InteractionAlgebra`, the
`MironovKMul` pattern) discharge exactly that side-condition for the edges an author chose to
curate. What no curated algebra can promise is *coverage*: an edge nobody mirrored into an
algebra is an edge whose dimensional side-condition nobody discharged.

`#kind_dimensional_coverage ns …` closes that gap mechanically. It walks every authored
kind-algebra edge under the given namespaces — the same seven witness families `#kind_edges`
scans (`ProductKind`, `QuotientKind`, `ReciprocalKind`, `TranscendentalKind`, `PowerKind`, and
the operator-table classes `KindMul`/`KindDiv`) — resolves each participating kind to its
declared `DimensionedKind`, and **evaluates the family's dimensional rule** in the PhysLib
`Dimension` group, exponent by exponent:

  * a product's result adds the operand exponents; a quotient subtracts them;
  * a reciprocal negates them; a power scales them by the rational exponent;
  * a transcendental demands dimension one on both sides (`exp` of a dimensioned quantity is
    dimensionally inhomogeneous).

Each edge reports as one of:

  * `[coherent]` — every kind has a `DimensionedKind` and the rule holds;
  * `[parametric]` — the edge is ∀-quantified generic vocabulary (a kind is a bound variable),
    so it has no fixed dimensional content; its concrete instantiations are audited separately;
  * `⚠ UNDIMENSIONED` — a participating kind has no declared `DimensionedKind`: the missing
    counterpart the coverage check exists to find;
  * `⚠ CONFLICTING` — two `DimensionedKind` declarations assign the same kind different
    dimensions (the dimension assignment itself is inconsistent);
  * `⚠ INCOHERENT` — the dimensional rule fails: the edge is *refuted*, not merely uncovered.

One sorted `info` message, suitable for `#guard_msgs` pinning: a new edge over an undimensioned
kind then fails the build the way a new axiom fails the profile guard, and a dimensionally
wrong edge fails it outright. Like every environment walk, the command is import-closure
sensitive — it sees only what the probe file imports.

**Division of labour with the curated algebras.** This command is the *total* check; an
`InteractionAlgebra` is the *curated story*. The mechanical rule here can only affirm that an
edge's dimensions balance — it cannot say which products are physically sanctioned (every
dimension-one triple balances trivially). The curated algebra says exactly that, for the edges
where the distinction matters, and its capstone theorems (`dim_homomorphism` reads) remain the
human-readable certificate. Coverage is mechanical; curation stays authored.

**Base restriction.** Dimensions are compared at the default five-generator base
(`LTMCTDimensionBase`): the counterpart registry collects the environment's constants of type
`DimensionedKind LTMCTDimensionBase`, and coherence is evaluated per generator by kernel
reduction of the ℚ exponent arithmetic. Kinds dimensioned only over another basis (the angle
reform's `Base`) are outside this walk's registry — a base-parametric walk would generalize the
enumeration, not the notion.

Like `KindEdges`, edges are harvested from constant *types* (a call-site witness is lifted into
a `_proof_N` auxiliary whose type is the edge), but only from the **conclusion** — an edge
taken as a *hypothesis* (`(h : ProductKind …) → …`) is assumed, not authored.

The walk has two surfaces over one row producer (`coverageRows`): the command renders the
pinnable text report, and `coverageTable` renders the same rows as a generated `IndexTable`
so a document can carry the report beside the other indexes — the Mathlib-gated sibling of
`Index.tableById`'s `dimensioned-kinds` route.
-/
import Lean
import PropertyKindCalculus.KindEdges
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Index.Basic

namespace PropertyKindCalculus.DimensionalCoverage

open Lean Meta

/-- The dimensional rule an edge family imposes on its participating kinds' dimensions. -/
inductive EdgeRule where
  /-- `k₁ · k₂ → k`: the result dimension is the product (exponents add). -/
  | product
  /-- `k₁ / k₂ → k`: the result dimension is the quotient (exponents subtract). -/
  | quotient
  /-- `1 / k₁ → k₂`: the result dimension is the inverse (exponents negate). -/
  | reciprocal
  /-- `transcendental : k₁ → k₂`: both sides must be dimension one. -/
  | transcendental
  /-- `k₁ ^ p → k₂`: the result dimension is the `p`-th power (exponents scale by `p`). -/
  | power
deriving DecidableEq, Repr, Inhabited

/-- The rule for each of `KindEdges.specs`' witness families. The operator-table classes carry
the same laws as the witness `Prop`s they bundle (`KindMul.law : ProductKind`,
`KindDiv.law : QuotientKind`). -/
def ruleOf : Name → Option EdgeRule
  | ``PropertyKindCalculus.ProductKind        => some .product
  | ``PropertyKindCalculus.KindMul            => some .product
  | ``PropertyKindCalculus.QuotientKind       => some .quotient
  | ``PropertyKindCalculus.KindDiv            => some .quotient
  | ``PropertyKindCalculus.ReciprocalKind     => some .reciprocal
  | ``PropertyKindCalculus.TranscendentalKind => some .transcendental
  | ``PropertyKindCalculus.PowerKind          => some .power
  | _ => none

/-- Every constant of type `DimensionedKind LTMCTDimensionBase` in the environment — the
counterpart registry the coverage check resolves kinds against. -/
def dimensionedKindDecls : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (name, info) in env.constants.toList do
    let t := info.type
    if t.isAppOfArity ``PropertyKindCalculus.DimensionedKind 1
        && t.appArg!.isConstOf ``LTMCTDimensionBase then
      if info.value?.isSome then
        out := out.push name
  return out

/-- The generators of the default base, enumerated from the inductive (all nullary). -/
def generatorCtors : MetaM (Array Name) := do
  let iv ← getConstInfoInduct ``LTMCTDimensionBase
  return iv.ctors.toArray

/-- How a kind resolved against the counterpart registry. -/
inductive KindRes where
  /-- Exactly one dimension assignment (all matching declarations agree); the exemplar. -/
  | ok (dk : Name)
  /-- No `DimensionedKind` declaration pairs this kind with a dimension. -/
  | missing
  /-- Matching declarations assign disagreeing dimensions. -/
  | conflict
deriving BEq, Repr, Inhabited

/-- `dk.dim.exponent g` for a registry constant `dk` and a generator `g`. -/
def expAt (dk gen : Name) : MetaM Expr := do
  mkAppM ``Dimension.exponent
    #[← mkAppM ``PropertyKindCalculus.DimensionedKind.dim #[mkConst dk], mkConst gen]

/-- Decide a closed ℚ equation by **kernel** reduction: `Kernel.whnf` of its `decide` term.
The elaborator's `whnf` stalls on `Rat` arithmetic (`Rat.sub` will not step until its
arguments are constructor-literal, and the lazy unfolder does not force them); the kernel's
reducer, with its accelerated `Nat` primitives, evaluates the exponent arithmetic completely.
A kernel error (an exponent that does not evaluate) counts as *not equal*, so it surfaces as
a violation rather than passing silently. -/
def kernelDecideEq (lhs rhs : Expr) : MetaM Bool := do
  let d ← mkDecide (← mkEq lhs rhs)
  match Kernel.whnf (← getEnv) (← getLCtx) d with
  | .ok r => return r.isConstOf ``Bool.true
  | .error _ => return false

/-- Do two registry constants carry the same dimension? Evaluated per generator by kernel
reduction of the ℚ exponents. -/
def dimsAgree (gens : Array Name) (a b : Name) : MetaM Bool := do
  for g in gens do
    unless ← kernelDecideEq (← expAt a g) (← expAt b g) do return false
  return true

/-- Resolve a kind expression against the counterpart registry: every `DimensionedKind`
declaration whose `kind` field is definitionally this kind, collapsed to `ok`/`missing`/
`conflict`. Cached by the kind expression's string key (the walk revisits the same kinds
across many edges). -/
def resolveKind (dks gens : Array Name) (cache : IO.Ref (Std.HashMap String KindRes))
    (k : Expr) : MetaM KindRes := do
  let key := toString k
  if let some r := (← cache.get).get? key then return r
  let mut hits : Array Name := #[]
  for dk in dks do
    let dkKind ← mkAppM ``PropertyKindCalculus.DimensionedKind.kind #[mkConst dk]
    if ← withNewMCtxDepth (isDefEq dkKind k) then
      hits := hits.push dk
  let mut res : KindRes := .missing
  if let some first := hits[0]? then
    res := .ok first
    for dk in hits[1:] do
      unless ← dimsAgree gens first dk do
        res := .conflict
        break
  cache.modify (·.insert key res)
  return res

/-- `(0 : ℚ)`, for the transcendental rule's dimension-one demand. -/
def qZero : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]

/-- Does the edge's dimensional rule hold for the resolved registry constants? Evaluated per
generator: the equation between ℚ exponents is closed and literal, so kernel reduction
decides it. `p?` is the rational exponent of a `power` edge. -/
def checkCoherent (gens : Array Name) (rule : EdgeRule) (dks : Array Name)
    (p? : Option Expr) : MetaM Bool := do
  let zero ← qZero
  for g in gens do
    let pairs : Array (Expr × Expr) ← do
      match rule with
      | .product =>
          pure #[(← expAt dks[2]! g, ← mkAppM ``HAdd.hAdd #[← expAt dks[0]! g, ← expAt dks[1]! g])]
      | .quotient =>
          pure #[(← expAt dks[2]! g, ← mkAppM ``HSub.hSub #[← expAt dks[0]! g, ← expAt dks[1]! g])]
      | .reciprocal =>
          pure #[(← expAt dks[1]! g, ← mkAppM ``Neg.neg #[← expAt dks[0]! g])]
      | .transcendental =>
          pure #[(← expAt dks[0]! g, zero), (← expAt dks[1]! g, zero)]
      | .power =>
          pure #[(← expAt dks[1]! g, ← mkAppM ``HMul.hMul #[p?.get!, ← expAt dks[0]! g])]
    for (lhs, rhs) in pairs do
      unless ← kernelDecideEq lhs rhs do return false
  return true

/-- An edge's coverage verdict, in report-group order (the `⚠` groups sort after the brackets). -/
inductive Verdict where
  | coherent | parametric | conflicting | incoherent | undimensioned
deriving DecidableEq, Repr, Inhabited

/-- One audited edge: its verdict, its rendered form, and — for the `⚠` verdicts — the kinds at
issue. The walk produces these rows once; the `#kind_dimensional_coverage` renderer and the
document-facing `coverageTable` are two surfaces over them. -/
structure CoverageRow where
  /-- The edge's verdict. -/
  verdict : Verdict
  /-- The edge as authored, pretty-printed (`k₁ · k₂ → k`). -/
  edge : String
  /-- For the `⚠ UNDIMENSIONED`/`⚠ CONFLICTING` verdicts: the kinds that triggered it,
  comma-separated; empty otherwise. -/
  detail : String := ""
deriving Repr, Inhabited

/-- Walk every authored kind-algebra edge under `scope` and produce one deduplicated
`CoverageRow` per edge. The enumeration, the rules, and the verdicts are documented on the
command below, which renders these rows as its report; `coverageTable` renders the same rows
as a generated table for a document. -/
def coverageRows (scope : Array Name) : MetaM (Array CoverageRow) := do
  let env ← getEnv
  let inScope : Name → Bool := fun d => scope.any (fun ns => ns.isPrefixOf d)
  let dks ← dimensionedKindDecls
  let gens ← generatorCtors
  let cache ← IO.mkRef ({} : Std.HashMap String KindRes)
  let seen ← IO.mkRef ({} : Std.HashSet String)
  let mut out : Array CoverageRow := #[]
  for (name, info) in env.constants.toList do
    unless inScope (KindEdges.parentOf name) do continue
    let found ← forallTelescopeReducing info.type fun _ concl => do
      let mut res : Array CoverageRow := #[]
      for (spec, args) in KindEdges.collectEdges concl #[] do
        let some rule := ruleOf spec.const | continue
        let pps ← args.mapM fun a => return toString (← ppExpr a)
        let edge := spec.fmt pps
        if (← seen.get).contains edge then continue
        seen.modify (·.insert edge)
        let (kindArgs, kindPps, p?) :=
          match rule with
          | .power => (args[1:].toArray, pps[1:].toArray, some args[0]!)
          | _      => (args, pps, none)
        if kindArgs.any (·.hasFVar) || (p?.map (·.hasFVar)).getD false then
          res := res.push ⟨.parametric, edge, ""⟩
          continue
        let ress ← kindArgs.mapM (m := MetaM) (resolveKind dks gens cache)
        let missing := (kindPps.zip ress).filterMap fun (pp, r) =>
          if r matches .missing then some pp else none
        let conflicts := (kindPps.zip ress).filterMap fun (pp, r) =>
          if r matches .conflict then some pp else none
        if !missing.isEmpty then
          res := res.push ⟨.undimensioned, edge, String.intercalate ", " missing.toList.eraseDups⟩
        else if !conflicts.isEmpty then
          res := res.push ⟨.conflicting, edge, String.intercalate ", " conflicts.toList.eraseDups⟩
        else
          let resolved := ress.filterMap fun | .ok dk => some dk | _ => none
          if ← checkCoherent gens rule resolved p? then
            res := res.push ⟨.coherent, edge, ""⟩
          else
            res := res.push ⟨.incoherent, edge, ""⟩
      return res
    out := out ++ found
  return out

/-- A row as the command's report line. -/
def CoverageRow.line : CoverageRow → String
  | ⟨.coherent, e, _⟩   => s!"[coherent] {e}"
  | ⟨.parametric, e, _⟩ => s!"[parametric] {e}"
  | ⟨.incoherent, e, _⟩ => s!"⚠ INCOHERENT {e}"
  | ⟨.undimensioned, e, d⟩ => s!"⚠ UNDIMENSIONED {e} — no DimensionedKind for: {d}"
  | ⟨.conflicting, e, d⟩   => s!"⚠ CONFLICTING {e} — disagreeing DimensionedKinds for: {d}"

/-- The report's summary line: the counts, and `clean` exactly when no verdict is a violation. -/
def coverageSummary (rows : Array CoverageRow) : String :=
  let count : Verdict → Nat := fun v =>
    rows.foldl (fun n r => if r.verdict == v then n + 1 else n) 0
  let (nCoh, nPar) := (count .coherent, count .parametric)
  let (nUnd, nInc, nCon) := (count .undimensioned, count .incoherent, count .conflicting)
  if nUnd + nInc + nCon == 0 then
    if nPar == 0 then
      s!"{rows.size} kind edge(s), all dimensionally coherent — clean"
    else
      s!"{rows.size} kind edge(s): {nCoh} coherent, {nPar} parametric — clean"
  else
    let parts := #[s!"{nCoh} coherent"]
      ++ (if nPar > 0 then #[s!"{nPar} parametric"] else #[])
      ++ (if nUnd > 0 then #[s!"{nUnd} UNDIMENSIONED"] else #[])
      ++ (if nInc > 0 then #[s!"{nInc} INCOHERENT"] else #[])
      ++ (if nCon > 0 then #[s!"{nCon} CONFLICTING"] else #[])
    s!"{rows.size} kind edge(s): {String.intercalate ", " parts.toList} — dimensional-coverage violation"

open Elab Command in
/-- `#kind_dimensional_coverage ns …` walks every authored kind-algebra edge under the given
namespaces, resolves each participating kind to its declared `DimensionedKind`, and evaluates
the family's dimensional rule in the PhysLib `Dimension` group. Edges are deduplicated as
rendered (the same edge authored at many call sites is one row — `#kind_edges` locates the
authors); one sorted `info` message, suitable for `#guard_msgs` pinning. `⚠ UNDIMENSIONED`
(no counterpart), `⚠ CONFLICTING` (disagreeing counterparts), and `⚠ INCOHERENT` (the rule
fails — a refuted edge) are violations; `[parametric]` generic vocabulary is not. -/
elab "#kind_dimensional_coverage" nss:ident+ : command => liftTermElabM do
  let out ← coverageRows (nss.map (·.getId))
  if out.isEmpty then
    logInfo m!"dimensional coverage — no authored kind edges in the given namespaces"
    return
  let sorted := (out.map (·.line)).qsort (· < ·)
  logInfo m!"dimensional coverage:\n{String.intercalate "\n" sorted.toList}\n{coverageSummary out}"

open PropertyKindCalculus.Index in
/-- **The coverage report as a generated table**, for documents — the same rows the command
reports, one edge per row, sorted as the report sorts.

Deliberately not a `tableById` case: that dispatcher lives in the Mathlib-free index library,
and this layer sits behind PhysLib and Mathlib. A document that imports this module calls it
directly and renders the result with its own adapter — the `dimensioned-kinds` route
(`Index.tableById`'s docstring), one audit over. Qualified names are shortened exactly as the
scoped index tables shorten them; the pinned probes keep the full spellings. -/
def coverageTable (scope : Index.Scope := #[]) : MetaM IndexTable := withHarvestBudget do
  let rows ← coverageRows scope
  let sorted := rows.qsort (fun a b => a.line < b.line)
  let cells := sorted.map fun r =>
    #[IndexCell.code (shortenNames r.edge),
      IndexCell.text (match r.verdict with
        | .coherent => "coherent"
        | .parametric => "parametric"
        | .undimensioned => "⚠ undimensioned"
        | .conflicting => "⚠ conflicting"
        | .incoherent => "⚠ incoherent"),
      IndexCell.text (shortenNames r.detail)]
  return { id := "dimensional-coverage", title := "Dimensional coverage",
           headers := #["Edge", "Verdict", "Kinds at issue"], rows := cells }

end PropertyKindCalculus.DimensionalCoverage
