/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Basic
import PropertyKindCalculus.DocGenMath.Attr

/-!
# The annotation catalogue and where each annotation is used

PropertyKindCalculus asks an author to state three kinds of thing that cannot be inferred:

* **where the calculus is left** — a kind crossing, a carrier-vocabulary exception, an emission.
  These are *checked*: `#kind_boundary_audit` fails on a boundary site that carries no tier, so the
  annotation is not documentation, it is the discharge of a proof obligation about the code.
* **how a definition should read** — the rendering family, which turns a `Quantity` definition into
  typeset mathematics in its own docstring.
* **what an external document says** — the requirement and cross-reference families, which are
  indexed by machinery that already exists (`{traceability}`, `{crossrefs}`).

The catalogue below is the first of those three lists made explicit, and it is curated *text*: what
an annotation means is not derivable from its registration. What is derivable — and therefore
harvested rather than listed — is **where each one is used**, which is what `annotationUses` returns.

The catalogue is the single place a new annotation must be added for the "Using the library" chapter
to describe it. That is a deliberate cost: one edit, in one file, next to the others, rather than a
chapter that silently omits an annotation nobody remembered to document.
-/

namespace PropertyKindCalculus.Index

open Lean Meta

/-! ## The catalogue -/

/-- Is an annotation enforced by a build-time check, or is it advisory metadata? The distinction the
chapter has to make first: `@[kindCrossing]` discharges an obligation the audit would otherwise fail
on, whereas `@[pkc_math_symbol]` changes only how something reads. -/
inductive Enforcement where
  /-- A build-time check fails without it, or rejects a misuse of it. -/
  | checked (by_ : String)
  /-- It changes rendering or records metadata; nothing fails if it is absent. -/
  | advisory
deriving Repr, Inhabited, BEq

/-- How an annotation's enforcement reads in the table. -/
def Enforcement.description : Enforcement → String
  | .checked by_ => s!"checked — {by_}"
  | .advisory    => "advisory"

/-- One annotation of the library's surface. -/
structure Annotation where
  /-- How it is written, as an author writes it. -/
  syntax_ : String
  /-- What it may be attached to. -/
  attachesTo : String
  /-- What it does, in one sentence. -/
  effect : String
  /-- Whether a build-time check depends on it. -/
  enforcement : Enforcement
  /-- The index table listing its occurrences, or `""` when another index already covers it. -/
  table : String
deriving Repr, Inhabited

/-- Every annotation PropertyKindCalculus defines.

Grouped as the chapter presents them: the boundary family (checked), the rendering family
(advisory), and the metadata family (advisory, and indexed by the pre-existing `{traceability}` and
`{crossrefs}` directives rather than duplicated here). -/
def catalogue : Array Annotation := #[
  -- The boundary family — invariants 4, 6 and 7.
  { syntax_ := "@[kindCrossing]", attachesTo := "a definition"
    effect := "Declares the one carrier-level place two kinds genuinely meet. The kinds are stated \
      in the signature; the mint or erasure inside is the crossing's mechanism, reviewed once."
    enforcement := .checked "#kind_boundary_audit reports an untagged boundary site as a violation"
    table := "crossings" },
  { syntax_ := "@[carrierVocab]", attachesTo := "a definition"
    effect := "Registers kind-preserving representation plumbing — an operation the kind algebra \
      does not name (a branchless min, a map over a coefficient table) that must drop to the carrier."
    enforcement := .checked "#kind_boundary_audit reports an untagged boundary site as a violation"
    table := "crossings" },
  { syntax_ := "@[kindEmission]", attachesTo := "a definition"
    effect := "Marks a genuine emission boundary: a kinded value becomes a naked one for a consumer \
      outside the calculus (a deploy driver, a tape recorder)."
    enforcement := .checked "#kind_boundary_audit reports an untagged boundary site as a violation"
    table := "crossings" },
  { syntax_ := "@[kindCarrier]", attachesTo := "a structure"
    effect := "Registers a downstream single-field quantity-like carrier, so the boundary audit \
      recognizes its mints and erasures — and so its records and operations are indexed."
    enforcement := .checked "rejected at elaboration if the declaration is not a structure"
    table := "carriers" },
  -- The rendering family — RENDERING.md.
  { syntax_ := "@[pkc_math]", attachesTo := "a Quantity-valued definition"
    effect := "Renders the definition as typeset LaTeX into its own docstring, so doc-gen4 and the \
      InfoView display the equation. Clauses `keeping` and `substituting` control let-bindings and \
      derivations; a literal string argument overrides the rendering entirely."
    enforcement := .checked "rejected if `keeping` names an unbound let, if `substituting` names a \
      recursive definition, or if a literal override is combined with either clause"
    table := "pkc-math" },
  { syntax_ := "@[pkc_math_symbol \"…\"]", attachesTo := "any declaration"
    effect := "Fixes the LaTeX a token renders as, overriding every naming heuristic. The optional \
      `operator` modifier prints a one-argument application as juxtaposition rather than a call."
    enforcement := .advisory
    table := "pkc-math-symbol" },
  { syntax_ := "@[pkc_math_config]", attachesTo := "a structure"
    effect := "Declares a configuration type: its field projections render as the qualified constant \
      `Struct.field` rather than as a function applied to the configuration value."
    enforcement := .checked "rejected at elaboration if the declaration is not a structure"
    table := "pkc-math-config" },
  { syntax_ := "@[pkc_math_transparent]", attachesTo := "a definition"
    effect := "Marks a notational wrapper the renderer should see through, so the wrapped term is \
      rendered in place of a call to the wrapper."
    enforcement := .advisory
    table := "pkc-math-transparent" },
  -- The metadata family — already indexed by their own directives.
  { syntax_ := "@[requirement \"…\" role]", attachesTo := "any declaration"
    effect := "Records that the declaration specifies, proves, implements or exemplifies a numbered \
      requirement."
    enforcement := .advisory
    table := "" },
  { syntax_ := "@[dybkaer \"…\" \"…\"]", attachesTo := "any declaration"
    effect := "Records the Dybkær *Ontology on Property* section and term this declaration formalizes."
    enforcement := .advisory
    table := "" },
  { syntax_ := "@[vim4 \"…\" \"…\"]", attachesTo := "any declaration"
    effect := "Records the VIM 4 2CD entry and term this declaration corresponds to."
    enforcement := .advisory
    table := "" }]

/-- The annotation reference table. Pure data — it describes the surface, and so needs no
environment. -/
def annotationsTable : IndexTable :=
  { id := "annotations"
    title := "The annotations PropertyKindCalculus defines"
    headers := #["Annotation", "Attaches to", "Effect", "Enforcement"]
    rows := catalogue.map fun a => #[
      .code a.syntax_, .text a.attachesTo, .text a.effect,
      .text a.enforcement.description] }

/-! ## Occurrences

Each harvest below is a one-line read of a registry, except the three that go through
`tagAttrDecls` / `paramAttrEntries` — see the note in `Index.Basic` on why enumerating a
`TagAttribute` needs a module walk while enumerating a `SimplePersistentEnvExtension` does not. -/

/-- Boundary sites in scope, with the tier that sanctions each and the kinds it mints.

This is the table the whole exercise is for. A kind crossing must be *authored*, so this list is the
complete, checkable statement of where the calculus is left and what is re-typed when it is. -/
def crossingsTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Site", "Tier", "Kinds minted", "What it does"]
  let tags := (BoundaryAudit.boundaryTags env).filter (fun t => scope.covers t.decl)
  if tags.isEmpty then
    return IndexTable.empty "crossings" "Authored kind crossings" headers
  -- The mint kinds come from the audit's own walk, so the table cannot disagree with the audit.
  let sites ← BoundaryAudit.boundarySites scope
  let mintsOf : Name → Array String := fun d =>
    match sites.find? (·.decl == d) with
    | some s => s.mints
    | none   => #[]
  let mut rows : Array (Array IndexCell) := #[]
  for t in tags.qsort (fun a b => nameLt a.decl b.decl) do
    rows := rows.push #[
      .decl t.decl (lastComponent t.decl),
      .code t.tier.label,
      .code (String.intercalate ", " ((mintsOf t.decl).toList.map shortenNames)),
      .text (← summaryLine env t.decl)]
  return { id := "crossings", title := "Authored kind crossings", headers, rows }

/-- The registered kind carriers: the two built into the calculus plus every structure a downstream
layer registered with `@[kindCarrier]`. Never scoped — the point of the table is that the registry is
open, so a reader wants to see what downstream layers added. -/
def carriersTable : MetaM IndexTable := do
  let env ← getEnv
  let carriers := BoundaryAudit.kindCarrierNames env
  let builtin : Array Name := #[``PropertyKindCalculus.Quantity, ``PropertyKindCalculus.CertifiedQuantity]
  let mut rows : Array (Array IndexCell) := #[]
  for c in carriers do
    rows := rows.push #[
      .decl c (lastComponent c),
      .text (if builtin.contains c then "built in" else "registered with @[kindCarrier]"),
      .text (← summaryLine env c)]
  return { id := "carriers", title := "Registered kind carriers"
           headers := #["Carrier", "Origin", "What it is"], rows }

/-- `@[pkc_math]`-rendered definitions in scope, with the clauses each one requested. -/
def pkcMathTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Definition", "Rendering mode", "What it is"]
  let uses := (DocGenMath.pkcMathUses env).filter (fun u => scope.covers u.decl)
  if uses.isEmpty then
    return IndexTable.empty "pkc-math" "Rendered definitions" headers
  let mut rows : Array (Array IndexCell) := #[]
  for u in uses.qsort (fun a b => nameLt a.decl b.decl) do
    rows := rows.push #[
      .decl u.decl (lastComponent u.decl),
      .text u.modeDescription,
      .text (← summaryLine env u.decl)]
  return { id := "pkc-math", title := "Rendered definitions", headers, rows }

/-- `@[pkc_math_symbol]` declarations in scope, with the LaTeX each fixes.

The seven `MironovNK` fields are the motivating case: two of them (`nu`, `mvt`) are *load-bearing*
rather than cosmetic, because the rendering heuristic maps a Greek-letter spelling to its letter and
would otherwise print a refractive index as an angular frequency. A table of these is therefore a
table of the places where a heuristic was deliberately overruled. -/
def pkcMathSymbolTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Declaration", "Renders as", "Layout"]
  let entries := (paramAttrEntries DocGenMath.pkcMathSymbolAttr env).filter
    (fun e => scope.covers e.1)
  if entries.isEmpty then
    return IndexTable.empty "pkc-math-symbol" "Fixed notation" headers
  let rows := entries.map fun (n, notation_) => #[
    IndexCell.decl n (lastComponent n),
    .code notation_.latex,
    .text (if notation_.operator then "prefix operator" else "function head")]
  return { id := "pkc-math-symbol", title := "Fixed notation", headers, rows }

/-- The declarations carrying a bare tag attribute (`@[pkc_math_config]`,
`@[pkc_math_transparent]`), with their docstring gloss. -/
def tagTable (id title heading : String) (attr : TagAttribute) (scope : Scope) :
    MetaM IndexTable := do
  let env ← getEnv
  let headers := #[heading, "What it is"]
  let decls := (tagAttrDecls attr env).filter scope.covers
  if decls.isEmpty then return IndexTable.empty id title headers
  let mut rows : Array (Array IndexCell) := #[]
  for d in decls do
    rows := rows.push #[.decl d (lastComponent d), .text (← summaryLine env d)]
  return { id, title, headers, rows }

/-- Configuration types (`@[pkc_math_config]`) in scope. -/
def configTable (scope : Scope) : MetaM IndexTable :=
  tagTable "pkc-math-config" "Configuration types" "Type" DocGenMath.pkcMathConfigAttr scope

/-- Notational wrappers (`@[pkc_math_transparent]`) in scope. -/
def transparentTable (scope : Scope) : MetaM IndexTable :=
  tagTable "pkc-math-transparent" "Notational wrappers" "Wrapper"
    DocGenMath.pkcMathTransparentAttr scope

end PropertyKindCalculus.Index
