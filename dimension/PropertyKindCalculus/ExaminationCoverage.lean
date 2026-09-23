/-
# ExaminationCoverage — `#kind_examination_coverage`, the census behind M6

The model template's M6 (`PropertyKindCalculus.Rubrics.modelTemplate`) asks that every kind of
dimension one be individuated by its examination principle. The reason is the dimension
functor's blind spot: `toDimension` sends volumetric water content, gravimetric water content,
a reflectivity and a permittivity all to `1`, so inside that fiber the §7.5 examination
principle is the *only* defining aspect that separates two kinds. A dimension-one kind declared
without one has been named, not individuated, and its distinctness from its neighbours is a
bare inequality of `id` strings — true, and unprincipled.

Until this module existed, M6 was discharged by exemplars: a document annotated the two or three
theorems it had proved by `distinct_of_examPrinciple`, and nothing asked about the rest. Read
against soil-moisture-model that "rest" was 75 of 100 kinds (`METHODOLOGY_TEMPLATES.md` §1).

`#kind_examination_coverage ns …` is the census. It walks every **`DimensionedKind`**
declaration under the given namespaces whose dimension is one — decided per generator by
kernel reduction of the ℚ exponents, exactly as `#kind_dimensional_coverage` decides coherence —
and reports each as one of:

  * `[individuated]` — the kind carries an `examPrinciple`, printed;
  * `⊘ exempted` — the declaration carries `@[kindPrincipleFree "reason"]`
    (`KindPrincipleFree.lean`), printed with its reason: a geometry vocabulary, a nominal
    designation, a bookkeeping fraction — dimension one and *correctly* principle-free;
  * `⚠ UNINDIVIDUATED` — dimension one, no principle, no mark: the finding;
  * `⚠ UNDIMENSIONED` — a `KindOfProperty` constant in scope that no `DimensionedKind` in the
    environment wraps. M6 cannot decide it: "dimension one" is a fact about a dimension the
    vocabulary never declared. This row exists because the first real vocabulary the census
    met (soil-moisture-model, 2026-09-07) declares a hundred kinds and no dimension, and the
    census read `no dimension-one kinds` — a gate that passes on an empty population is the
    vacuous universal the test suite's charter warns against. Declaring the dimension (M10)
    is what moves such a kind into the population this census decides.

One sorted `info` message, suitable for `#guard_msgs` pinning; the summary line ends `clean`
exactly when no row is `UNINDIVIDUATED`. `#kind_examination_clean ns …` is the same walk as a
gate: no message, throws while any row is unindividuated, so re-blessing the pinned report
cannot silence it — the discipline every `_clean` command in this library follows, for the
reason `#kind_dimensional_clean`'s docstring gives.

**Why `DimensionedKind` and not `KindOfProperty`.** "Dimension one" is a fact about the
`DimensionedKind`; a `KindOfProperty` with no dimension declared cannot be placed in or out of
the dimension-one fiber, which is why it is reported as `UNDIMENSIONED` rather than decided —
and why the report of it is loud rather than absent. And the population has to be the
declarations a domain actually writes: the ISO 80000 catalogue and most models declare their
kinds *inline* inside a `DimensionedKind` (`{ kind := { id := "length", … }, dim := Dim.length
}`), so a walk over `KindOfProperty` constants would miss most of them. Same base restriction
as the dimensional walk: the registry is the environment's `DimensionedKind LTMCTDimensionBase`
constants.

**Receipts.** Both commands record an `AuditReceipt` at their success point, so a document
whose conformance names this audit for M6 reads green only in a build where the census ran over
a scope covering the document's (`Rubrics.Conformance.status`).

Like every environment walk, the command is import-closure sensitive: it sees the declarations
the probe file imports, and an exemption mark declared in a module the probe does not reach is
not seen — the false alarm is loud (`UNINDIVIDUATED`), the omission is not.
-/

module

public import Lean
public import PropertyKindCalculus.DimensionalCoverage
public import PropertyKindCalculus.KindPrincipleFree
public import PropertyKindCalculus.AuditReceipt

-- Same-module helpers serve both the command elaborators below and runtime callers, so the
-- phase check is relaxed for this file (the module system's mixed-use escape; imports are
-- still checked and take `public meta import`).
set_option compiler.relaxedMetaCheck true

@[expose] public section Blanket

namespace PropertyKindCalculus.ExaminationCoverage

open Lean Meta
open PropertyKindCalculus.DimensionalCoverage (dimensionedKindDecls generatorCtors expAt
  kernelDecideEq qZero)

/-- The verdict on one dimension-one kind. -/
inductive Verdict where
  | individuated | exempted | unindividuated | undimensioned
deriving DecidableEq, Repr, Inhabited

/-- One audited dimension-one kind. -/
structure ExaminationRow where
  /-- The verdict. -/
  verdict : Verdict
  /-- The `DimensionedKind` declaration — or, for `undimensioned`, the bare `KindOfProperty`
  constant. -/
  decl : Name
  /-- The kind's `id` string, as declared. -/
  kindId : String
  /-- The examination principle (`individuated`), the exemption's reason (`exempted`), or
  empty (`unindividuated`). -/
  detail : String := ""
deriving Repr, Inhabited

/-- Is a registry constant's dimension one? Every generator exponent is zero, decided in the
kernel exactly as the coherence rule is. -/
def isDimensionOne (gens : Array Name) (dk : Name) : MetaM Bool := do
  let z ← qZero
  for g in gens do
    unless ← kernelDecideEq (← expAt dk g) z do return false
  return true

private unsafe def evalStringUnsafe (e : Expr) : MetaM String :=
  Meta.evalExpr String (mkConst ``String) e

/-- A closed `String` expression's value. Replaced at run time by the evaluator; the safe
body stands only where no evaluator is available (the `evalRelation` idiom). -/
@[implemented_by evalStringUnsafe]
def evalString (_e : Expr) : MetaM String :=
  throwError "string values cannot be read in this environment"

/-- A closed `String`-valued expression, read back: by reduction when it is a literal, and by
the evaluator when it is not. The second path exists because a principle assembled by `++` —
ISO 80000-11's `context: defining-ratio` — whnf-reduces to `String.append` of literals and
never to a literal, and a census that printed `?` for every characteristic number would be
reporting its reader, not the catalogue. `none` when neither path yields a value. -/
def strOf (e : Expr) : MetaM (Option String) := do
  match ← whnf e with
  | .lit (.strVal s) => return some s
  | _ => try return some (← evalString e) catch _ => return none

/-- A registry constant's kind `id` and `examPrinciple`, read by reduction of the projections.
An `id` that does not reduce prints as `?` rather than failing the walk: one strange
declaration must not hide the census. -/
def kindFields (dk : Name) : MetaM (String × Option String) := do
  let kind ← mkAppM ``PropertyKindCalculus.DimensionedKind.kind #[mkConst dk]
  let id := (← strOf (← mkAppM ``PropertyKindCalculus.KindOfProperty.id #[kind])).getD "?"
  let pr ← whnf (← mkAppM ``PropertyKindCalculus.KindOfProperty.examPrinciple #[kind])
  if pr.getAppFn.isConstOf ``Option.some then
    return (id, some ((← strOf pr.getAppArgs[1]!).getD "?"))
  return (id, none)

/-- Walk every `DimensionedKind` declaration under `scope` (an empty scope is unrestricted,
as the index harvests read it) whose dimension is one, and produce one row per declaration. -/
def examinationRows (scope : Array Name) : MetaM (Array ExaminationRow) := do
  let env ← getEnv
  let inScope : Name → Bool := fun d => scope.isEmpty || scope.any (·.isPrefixOf d)
  let dks := (← dimensionedKindDecls).filter inScope
  let gens ← generatorCtors
  let marks := kindPrincipleFreeMarks env
  let mut out : Array ExaminationRow := #[]
  for dk in dks do
    unless ← isDimensionOne gens dk do continue
    let (kindId, principle?) ← kindFields dk
    match principle? with
    | some p => out := out.push ⟨.individuated, dk, kindId, p⟩
    | none   =>
      match marks.find? (·.decl == dk) with
      | some m => out := out.push ⟨.exempted, dk, kindId, m.reason⟩
      | none   => out := out.push ⟨.unindividuated, dk, kindId, ""⟩
  -- The kinds the census cannot decide: `KindOfProperty` constants in scope that no
  -- `DimensionedKind` anywhere in the environment wraps (the registry is unscoped here, since
  -- a dimension may be declared beside the catalogue rather than beside the kind).
  let allDks ← dimensionedKindDecls
  for (k, info) in env.constants.toList do
    if k.isInternal || !inScope k then continue
    unless info.type.isConstOf ``PropertyKindCalculus.KindOfProperty do continue
    let mut wrapped := false
    for dk in allDks do
      let kind ← mkAppM ``PropertyKindCalculus.DimensionedKind.kind #[mkConst dk]
      if ← isDefEq kind (mkConst k) then wrapped := true; break
    unless wrapped do
      let idE ← mkAppM ``PropertyKindCalculus.KindOfProperty.id #[mkConst k]
      out := out.push ⟨.undimensioned, k, (← strOf idE).getD "?", ""⟩
  return out

/-- A row as the report line. -/
def ExaminationRow.line : ExaminationRow → String
  | ⟨.individuated, d, id, p⟩   => s!"[individuated] {d} ({id}) — principle: {p}"
  | ⟨.exempted, d, id, r⟩       => s!"⊘ exempted {d} ({id}) — {r}"
  | ⟨.unindividuated, d, id, _⟩ => s!"⚠ UNINDIVIDUATED {d} ({id})"
  | ⟨.undimensioned, d, id, _⟩  =>
    s!"⚠ UNDIMENSIONED {d} ({id}) — no DimensionedKind wraps it"

/-- Is a row a violation the gate fires on? -/
def ExaminationRow.violates (r : ExaminationRow) : Bool :=
  r.verdict == .unindividuated || r.verdict == .undimensioned

/-- The summary line: the counts over the dimension-one kinds, the undimensioned kinds beside
them, and `clean` exactly when no row is a violation. -/
def examinationSummary (rows : Array ExaminationRow) : String :=
  let count : Verdict → Nat := fun v =>
    rows.foldl (fun n r => if r.verdict == v then n + 1 else n) 0
  let (nInd, nEx, nUn, nUnd) :=
    (count .individuated, count .exempted, count .unindividuated, count .undimensioned)
  let nDimOne := rows.size - nUnd
  let ex := if nEx > 0 then s!", {nEx} exempted" else ""
  let un := if nUn > 0 then s!", {nUn} UNINDIVIDUATED" else ""
  let und := if nUnd > 0 then s!"; {nUnd} kind(s) UNDIMENSIONED" else ""
  if nUn == 0 && nUnd == 0 then
    s!"{nDimOne} dimension-one kind(s): {nInd} individuated{ex} — clean"
  else
    s!"{nDimOne} dimension-one kind(s): {nInd} individuated{ex}{un}{und} \
      — examination-coverage violation"

open Elab Command in
/-- `#kind_examination_coverage ns …` — the census behind M6: every dimension-one
`DimensionedKind` under the namespaces, each `[individuated]` by its examination principle,
`⊘ exempted` by an `@[kindPrincipleFree]` mark, or `⚠ UNINDIVIDUATED` — and every bare
`KindOfProperty` constant in scope that no `DimensionedKind` wraps as `⚠ UNDIMENSIONED`. One
sorted `info` message to pin. Records an `AuditReceipt` for `kind_examination_coverage`. -/
elab "#kind_examination_coverage" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let rows ← examinationRows scope
  recordAuditReceipt "kind_examination_coverage" scope
  if rows.isEmpty then
    logInfo m!"examination coverage — no dimension-one kinds in the given namespaces"
    return
  let sorted := (rows.map (·.line)).qsort (· < ·)
  logInfo m!"examination coverage:\n{String.intercalate "\n" sorted.toList}\n\
    {examinationSummary rows}"

open Elab Command in
/-- `#kind_examination_clean ns …` — **the invariant, stated apart from the record.** Carries
no message and pins nothing: throws while any dimension-one kind in scope is
`⚠ UNINDIVIDUATED` or any kind in scope is `⚠ UNDIMENSIONED`. The fixes are to give the kind
its examination principle, to mark it `@[kindPrincipleFree "reason"]` where it is correctly
principle-free, or to declare its dimension; the fourth — re-pinning
a `#kind_examination_coverage` report whose summary says `violation` — turns the build green
and the census off, which is why this command exists beside the report. Records an
`AuditReceipt` for `kind_examination_clean` exactly when it does not fire. -/
elab "#kind_examination_clean" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let rows ← examinationRows scope
  let bad := rows.filter (·.violates)
  unless bad.isEmpty do
    let rendered := (bad.map (fun r => s!"  {r.line}")).qsort (· < ·)
    throwError "examination coverage: {bad.size} kind(s) not individuated or not dimensioned \
      — examination-coverage violation\n{String.intercalate "\n" rendered.toList}\n\n\
      Inside the dimension-one fiber the examination principle is the only defining aspect \
      that separates two kinds. Give each UNINDIVIDUATED kind its `examPrinciple`, or — where \
      it is correctly principle-free (a geometry vocabulary, a nominal designation, a \
      bookkeeping fraction) — mark its declaration `@[kindPrincipleFree \"reason\"]` so the \
      exemption is data the sweep can read. Give each UNDIMENSIONED kind a `DimensionedKind` \
      declaring its dimension (M10): until then this census cannot place it in or out of the \
      dimension-one fiber, and a gate that passed over it would pass over nothing. Do NOT \
      re-pin a `#kind_examination_coverage` report whose summary says `violation` — that \
      turns the build green and the census off."
  recordAuditReceipt "kind_examination_clean" scope

open PropertyKindCalculus.Index in
/-- **The census as a generated table**, for documents — the same rows the command reports,
one dimension-one kind per row, sorted by declaration. M6's evidence kind is `generated`, and
this is the view a document renders beside its examination-layer index. Not a `tableById`
case for the reason `coverageTable` is not one: this layer sits behind PhysLib and Mathlib. -/
def examinationTable (scope : Index.Scope := #[]) : MetaM IndexTable := withHarvestBudget do
  let headers := #["Kind", "Declaration", "Verdict", "Principle, or reason"]
  let rows ← examinationRows scope
  if rows.isEmpty then return IndexTable.empty "examination-coverage" "Examination coverage" headers
  let sorted := rows.qsort fun a b => a.decl.toString < b.decl.toString
  let cells := sorted.map fun r =>
    let verdict := match r.verdict with
      | .individuated   => "individuated"
      | .exempted       => "exempted"
      | .unindividuated => "UNINDIVIDUATED"
      | .undimensioned  => "UNDIMENSIONED"
    #[IndexCell.text r.kindId, .decl r.decl (lastComponent r.decl), .text verdict,
      .text r.detail]
  return { id := "examination-coverage", title := "Examination coverage", headers, rows := cells }

end PropertyKindCalculus.ExaminationCoverage

end Blanket
