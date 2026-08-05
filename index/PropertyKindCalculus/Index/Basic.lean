/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import Lean
import PropertyKindCalculus.BoundaryAudit

/-!
# `PropertyKindCalculus.Index` — harvesting the library's own structure

The calculus already knows how to enumerate itself one question at a time: `#kind_edges` lists the
authored kind-algebra edges mentioning a kind, `#kind_boundary_audit` lists the boundary sites, and
`#print axioms` lists what a proof rests on. Each is a *command* — a one-shot `info` message for an
author sitting in front of an editor.

This library is the same enumerations delivered as **data**, so that a document can render them.
A blueprint chapter and a doc-gen4 page need the rows, not a formatted message; and both live in
packages (Verso-backed) that PropertyKindCalculus must not depend on. So the split is:

* **here** — the harvest: walk the environment, produce `IndexTable`s of `IndexCell`s. No Verso, no
  markup, no layout. Importable by anything that requires PropertyKindCalculus, which is what lets
  soil-moisture-model's technical reference render the same tables as this repo's blueprint
  (it requires PropertyKindCalculus from git and so cannot reach this repo's `blueprint/` package).
* **there** — a thin per-document adapter mapping `IndexCell` onto that document's own table
  machinery (`PropertyKindCalculusBlueprint.ItemIndex.Cell`, and its counterpart downstream).

## What makes an index *derived* rather than curated

Every table below is computed from the environment, so it cannot drift from the source: a renamed
declaration changes the table, and a declaration that stops being (say) a kind crossing leaves it.
Crucially, **none of this requires a new annotation**. The membership tests are either "constant of
type `T`" or a question the existing registries already answer — `BoundaryAudit.kindCarrierNames`
for what counts as a carrier, `boundaryExt` for what counts as a sanctioned crossing. The one place
an annotation *is* the criterion (`@[pkc_math_config]`, `@[requirement]`, …) is an annotation that
already exists for another reason.
-/

namespace PropertyKindCalculus.Index

open Lean

variable {α : Type}

/-! ## Scope — the namespace filter

Every harvest is scoped, following `#kind_boundary_audit ns …`: an index is always *of* some
namespace (the core spine, one ISO 80000 part, a downstream model), never of the whole environment,
which after Mathlib is neither renderable nor meaningful. The empty scope means "no filter" and is
what the commands use when invoked without arguments. -/

/-- A set of namespace prefixes to restrict a harvest to. Empty means unrestricted. -/
abbrev Scope := Array Name

/-- Does `n` fall under one of the scope's namespaces? An empty scope covers everything. -/
def Scope.covers (s : Scope) (n : Name) : Bool :=
  s.isEmpty || s.any (fun ns => ns.isPrefixOf n)

/-! ## Cells and tables — a Verso-free presentation IR

Deliberately the same shape as `PropertyKindCalculusBlueprint.ItemIndex.Cell`, minus the one
constructor that only makes sense inside Verso — `ref`, which names a blueprint tag. Its `md` cell
*does* have a counterpart here, `prose`, because the harvest quotes docstrings and a docstring is
markdown; what stays out of the library is the parsed form's rendering, not the fact of the markup.
A `decl` cell names a *declaration*, and each document decides what to do with it: the blueprint
resolves it to a blueprint node via `Informal.Environment.labelsForLeanDecl`, doc-gen4 resolves it
to a page anchor. The harvest does not know, and must not, which is why it stores the `Name`. -/

/-- One table cell. -/
inductive IndexCell where
  /-- Plain prose, rendered exactly as given. -/
  | text (s : String)
  /-- Inline code — a type, a term, a kind equation. -/
  | code (s : String)
  /-- Prose **quoted from a docstring**, and therefore written in the inline markdown a docstring is
  written in: `` `code` ``, `*emphasis*`, `**strong**`. Distinct from `text` because the two surfaces
  disagree about what to do with it — doc-gen4 renders markdown and wants it untouched, while a Verso
  table sets a string literally and must parse it first. Passing docstring prose as `text` is exactly
  the bug this constructor exists to prevent: the markers reach the page. -/
  | prose (s : String)
  /-- A reference to a declaration, with the text to display for it. -/
  | decl (n : Name) (display : String)
  /-- A comma-separated list of declaration references, each with its display text. -/
  | links (items : Array (Name × String))
deriving Repr, Inhabited, BEq

/-- An empty cell. -/
def IndexCell.blank : IndexCell := .text ""

/-! ### The inline grammar of a `prose` cell

A docstring is markdown and the harvest quotes it verbatim, so a `prose` cell arrives with markers
in it. The two ways to get that wrong are to render it literally — which puts `**` on the page — and
to run a markdown library over a table cell, which is far more machinery than three constructs
deserve. Between them is the grammar below: inline code, emphasis and strong, parsed *once, here*,
so that every document rendering an index agrees about what a docstring cell means rather than each
adapter growing its own dialect.

Two properties are deliberate. Spans **nest**, because a docstring lead-in is routinely
`**… the *branched* principal …**` and flattening it would put the inner markers back on the page.
And an unterminated delimiter is **kept as literal text** rather than swallowing the rest of the
cell: a docstring is written for a human first, and a lone asterisk or backtick in one is a
typographic accident, not a truncation instruction. -/

/-- One inline run of a `prose` cell. Spans nest, so `emph` and `strong` carry runs rather than a
string. -/
inductive ProseRun where
  /-- Literal text. -/
  | text (s : String)
  /-- An inline code span, written `` `…` ``. -/
  | code (s : String)
  /-- Emphasis, written `*…*`. -/
  | emph (content : Array ProseRun)
  /-- Strong emphasis, written `**…**`. -/
  | strong (content : Array ProseRun)
deriving Inhabited, Repr

/-- Split `cs` at the first occurrence of the delimiter `close`, returning what precedes it and what
follows it, or `none` when it does not occur. -/
private def splitAtDelim (close : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if close.isPrefixOf (c :: rest) then some ([], (c :: rest).drop close.length)
    else (splitAtDelim close rest).map fun (pre, post) => (c :: pre, post)

/-- Emit the pending literal text, if any. -/
private def flushText (buf : String) (acc : Array ProseRun) : Array ProseRun :=
  if buf.isEmpty then acc else acc.push (.text buf)

private partial def parseProseAux : List Char → String → Array ProseRun → Array ProseRun
  | [], buf, acc => flushText buf acc
  | '*' :: '*' :: rest, buf, acc =>
    match splitAtDelim ['*', '*'] rest with
    | some (inner, rest') =>
      parseProseAux rest' "" ((flushText buf acc).push (.strong (parseProseAux inner "" #[])))
    | none => parseProseAux rest (buf ++ "**") acc
  | '*' :: rest, buf, acc =>
    match splitAtDelim ['*'] rest with
    | some (inner, rest') =>
      parseProseAux rest' "" ((flushText buf acc).push (.emph (parseProseAux inner "" #[])))
    | none => parseProseAux rest (buf.push '*') acc
  | '`' :: rest, buf, acc =>
    match splitAtDelim ['`'] rest with
    | some (inner, rest') =>
      parseProseAux rest' "" ((flushText buf acc).push (.code (String.ofList inner)))
    | none => parseProseAux rest (buf.push '`') acc
  | c :: rest, buf, acc => parseProseAux rest (buf.push c) acc

/-- Split a `prose` cell into its inline runs. -/
def parseProse (s : String) : Array ProseRun := parseProseAux s.toList "" #[]

/-- A generated table: a stable identifier (what a directive names to select it), a human title,
column headers, and body rows. -/
structure IndexTable where
  /-- The identifier a document's directive uses to request this table (`"kinds"`, `"crossings"`). -/
  id : String
  /-- The table's title, for a caption or a heading. -/
  title : String
  /-- Column headers, one per column. -/
  headers : Array String
  /-- Body rows, each with one cell per header. -/
  rows : Array (Array IndexCell)
deriving Repr, Inhabited

/-- The empty table with the given identity — what a harvest returns when nothing is in scope. -/
def IndexTable.empty (id title : String) (headers : Array String) : IndexTable :=
  { id, title, headers, rows := #[] }

/-! ## Display helpers -/

/-- The last component of a declaration name, for display in a table cell. -/
def lastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- Lexicographic order on names, used everywhere a table is sorted. `Name.quickLt` orders by
internal hash and so produces a *stable but unreadable* order; a rendered index has to be
alphabetical, and a `#guard_msgs`-pinned one has to be reproducible. -/
def nameLt (a b : Name) : Bool := toString a < toString b

/-- Shorten every qualified name in a pretty-printed expression to its last component.

A cell holding sixteen kinds, each spelled `SoilMoisture.Algorithm.Dielectric.Kinds.…`, is a
paragraph of repeated prefixes with the content buried in it. Tokens are shortened individually
rather than the string being truncated, so a compound expression survives: `soilWaterVWC s` stays
`soilWaterVWC s` while `A.B.C.relPermKind` becomes `relPermKind`. The tables that use this are
namespace-scoped, which is what makes the short form unambiguous. -/
def shortenNames (s : String) : String :=
  String.intercalate " " ((s.splitOn " ").map fun tok =>
    match (tok.splitOn ".").getLast? with
    | some last => if last.isEmpty then tok else last
    | none      => tok)

/-- A declaration's docstring reduced to one table cell: its first paragraph, newlines collapsed to
spaces, truncated on a word boundary. Returns `""` for an undocumented declaration.

Not the first *line*: a docstring is hard-wrapped, so the first line ends wherever the author's
column limit fell and cutting there truncates mid-sentence — which is tolerable in `#kind_crossings`'
one-line report and is not in a rendered table. The first paragraph is the unit the author actually
composed.

The result is **markdown**, because a docstring is, and it is returned that way rather than stripped:
the doc-gen4 surface renders it, and stripping would cost that surface both the emphasis and the
code spans doc-gen4 resolves into links. It therefore belongs in an `IndexCell.prose` cell, never an
`IndexCell.text` one — see the grammar note above. -/
def summaryLine (env : Environment) (n : Name) (maxLen : Nat := 160) : IO String := do
  let doc := (← findDocString? env n).getD ""
  let para := (doc.splitOn "\n\n").headD ""
  let lines := (para.splitOn "\n").map (fun l => l.trimAscii.toString)
  let flat := String.intercalate " " (lines.filter (!·.isEmpty))
  if flat.length ≤ maxLen then return flat
  let mut out := ""
  for w in flat.splitOn " " do
    if out.length + w.length + 1 > maxLen then break
    out := if out.isEmpty then w else out ++ " " ++ w
  return out ++ " …"

/-! ## Which declarations are *authored*

An environment walk sees far more than a person wrote: equation lemmas, `match_N` matchers,
`_proof_N` lifted witnesses, structure machinery (`injEq`, `noConfusion`, recursors). None belongs
in an index. `BoundaryAudit` already draws this line for its own walk; the predicate below is the
same line, reused, so the two audits cannot disagree about what counts as a declaration. -/

/-- Is `n` a declaration a person wrote, rather than machinery the elaborator generated? -/
def isAuthored (env : Environment) (n : Name) : Bool :=
  !n.isInternal
  && !(BoundaryAudit.isGeneratedMachinery env #[] n)
  && BoundaryAudit.parentOf n == n

/-! ## Bounded reduction

Reading a field back out of a definition means reducing a projection, and reduction is the one step
here that can run away: a kind whose definition routes through a Mathlib-backed computation can
exhaust the elaborator's whole heartbeat budget on a single cell, taking the surrounding document
build down with it. An index must never do that — a cell it cannot compute should degrade to the
unreduced expression, not fail the build.

So every reduction is given its own allowance, counted from zero, and a failure is a `none`.

**`withOptions` does not work for this**, which is worth stating because it looks as though it
should: `Core.Context.maxHeartbeats` is computed from the options *once*, when the context is built
(`Lean/CoreM.lean`), and `checkMaxHeartbeats` reads that field rather than re-reading the option. So
raising `maxHeartbeats` after entry changes nothing at all, and changes it *silently* — the symptom
is a timeout at exactly the default limit despite an explicit larger setting. The limit has to be
written into the context itself. -/

/-- Run `act` with an explicit heartbeat allowance, counted from zero. `0` means unlimited.
`Core.withCurrHeartbeats` restarts the elapsed count, so the allowance is this call's rather than
whatever share of the enclosing command's budget happens to be left. -/
def withHeartbeats (n : Nat) (act : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := n }) do
    Core.withCurrHeartbeats act

/-- Run `act` under a private heartbeat allowance, returning `none` if it exhausts it or throws.
Used for the individual reductions a table's cells need, so one runaway definition degrades to an
unreduced cell instead of taking the document build down. -/
def bounded (act : MetaM α) (heartbeats : Nat := 20000) : MetaM (Option α) := do
  try withHeartbeats heartbeats (return some (← act))
  catch _ => return none

/-- Reduce `e` to weak head normal form under a private heartbeat allowance, or `none` if it does not
get there in time (or throws). -/
def boundedWhnf (e : Expr) (heartbeats : Nat := 20000) : MetaM (Option Expr) :=
  bounded (Meta.whnf e) heartbeats

/-- Run a whole-environment index harvest without a heartbeat limit.

An ordinary elaboration's budget is the wrong scale for these walks: building one table touches every
constant in the environment — after Mathlib, a few hundred thousand — and pretty-prints every
kind-algebra argument it finds. `#kind_edges` gets away without this because it does almost nothing
per constant; a table that additionally reduces projections to read field values does not, and the
full core-spine index measurably exceeds even a freshly-restarted default allowance.

Granted here, once, so that every caller — the `#pkc_index` command, a Verso directive, the doc-gen4
page generator — inherits it rather than each discovering the limit separately and papering over it
with its own `set_option`. -/
def withHarvestBudget (act : MetaM α) : MetaM α := withHeartbeats 0 act

/-! ## The environment walks

Each of these walks `env.constants` once. With Mathlib imported that is a few hundred thousand
constants, so a table must not walk per-row: the harvests below take *arrays* of targets and return
a map, and a document that renders a dozen tables should call each walk once. -/

/-- Every authored constant in scope whose type is headed by `ty` — the membership test for all of
the ontology tables (`KindOfProperty`, `System`, `Component`, `DedicatedKind`, the examination
layers, `InteractionAlgebra`). Sorted alphabetically.

Headed by, not equal to: `DimensionedKind` takes a base-dimension parameter, so its inhabitants have
type `DimensionedKind LTMCTDimensionBase`, and an equality test would silently find none of them. -/
def constantsOfType (env : Environment) (ty : Name) (scope : Scope) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, info) in env.constants.toList do
    unless scope.covers n do continue
    unless isAuthored env n do continue
    if info.type.getAppFn.isConstOf ty then out := out.push n
  return out.qsort nameLt

/-- The multi-type form of `constantsOfType`: one walk serving every ontology table. Returns a map
from each requested type to its (sorted) inhabitants in scope. -/
def constantsOfTypes (env : Environment) (tys : Array Name) (scope : Scope) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut acc : Std.HashMap Name (Array Name) := {}
  for ty in tys do acc := acc.insert ty #[]
  for (n, info) in env.constants.toList do
    unless scope.covers n do continue
    unless isAuthored env n do continue
    let .const ty _ := info.type.getAppFn | continue
    if let some prev := acc[ty]? then acc := acc.insert ty (prev.push n)
  return acc.fold (init := {}) fun m k v => m.insert k (v.qsort nameLt)

/-- The final name components of theorems the elaborator derives for a structure or inductive.
`BoundaryAudit.generatedSuffixes` covers the *definitions* it generates; these are the `Prop`-valued
ones, which only a theorem scan sees. Without them every kind used in a structure field picks up that
structure's `inj` and `sizeOf_spec` in its "related theorems" column, which is noise that crowds out
the one theorem that matters (`boundRelaxTime_ne_freeRelaxTime`). -/
def generatedTheoremSuffixes : List String :=
  ["inj", "injEq", "sizeOf_spec", "noConfusion", "eq_def", "eq_1", "eq_2", "eq_3", "eq_4",
   "ctorIdx", "toCtorIdx", "below", "ibelow"]

/-- Is `n` a theorem the elaborator derived rather than one a person stated? -/
def isGeneratedTheorem (n : Name) : Bool :=
  match n with
  | .str _ s => generatedTheoremSuffixes.contains s
  | _ => false

/-- For each target constant, the authored theorems whose **statement** mentions it — the "related
theorems" column (`boundRelaxTime_ne_freeRelaxTime` under `boundRelaxTime`).

Scanning *types* rather than bodies is the same choice `#kind_edges` documents and for the same
reason: what a theorem is *about* is its statement. The theorem itself need not be in scope — a
proof about a downstream kind may live anywhere — so only the targets are scoped. -/
def theoremsMentioning (env : Environment) (targets : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let wanted : Std.HashSet Name := targets.foldl (·.insert ·) {}
  let mut acc : Std.HashMap Name (Array Name) := {}
  for t in targets do acc := acc.insert t #[]
  for (n, info) in env.constants.toList do
    unless info matches .thmInfo _ do continue
    unless isAuthored env n do continue
    if isGeneratedTheorem n then continue
    for c in info.type.getUsedConstants do
      if wanted.contains c then
        acc := acc.insert c ((acc.getD c #[]).push n)
  return acc.fold (init := {}) fun m k v => m.insert k (v.toList.eraseDups.toArray.qsort nameLt)

/-! ## Enumerating tag and parametric attributes

**The trap this exists to hide.** `registerTagAttribute` and `registerParametricAttribute` both
build their extension with `addImportedFn := fun _ _ => pure {}` (`Lean/Attributes.lean`), so
`getState` returns the tags of *the current module only*. `TagAttribute.hasTag` works across imports
because it looks the declaration up in its own module's entries — but there is no `getState` that
gives you all of them. Enumerating therefore means walking every imported module's entry array and
adding the current module's state on top.

Nothing warns you: a table over `@[pkc_math_config]` built the obvious way comes back **empty**, and
reads as "there are none" rather than "you asked the wrong way". The `SimplePersistentEnvExtension`s
`BoundaryAudit` uses (`boundaryExt`, `kindCarrierExt`) *do* combine on import, which is why
`boundaryTags` is a one-liner and these are not. -/

/-- Every declaration carrying `attr`, across all imported modules and the current one. -/
def tagAttrDecls (attr : TagAttribute) (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for m in env.allImportedModuleNames do
    if let some idx := env.getModuleIdx? m then
      out := out ++ attr.ext.getModuleEntries env idx
  for n in (attr.ext.getState env).toList do
    out := out.push n
  return out.qsort nameLt

/-- Every `(declaration, parameter)` pair carrying `attr`, across all imported modules and the
current one — the parametric counterpart of `tagAttrDecls`, and subject to the same trap. -/
def paramAttrEntries {α : Type} [Inhabited α] (attr : ParametricAttribute α) (env : Environment) :
    Array (Name × α) := Id.run do
  let mut out : Array (Name × α) := #[]
  for m in env.allImportedModuleNames do
    if let some idx := env.getModuleIdx? m then
      out := out ++ attr.ext.getModuleEntries env idx
  let (_, m) := attr.ext.getState env
  for (n, v) in m.toList do
    out := out.push (n, v)
  return out.qsort (fun a b => nameLt a.1 b.1)

end PropertyKindCalculus.Index
