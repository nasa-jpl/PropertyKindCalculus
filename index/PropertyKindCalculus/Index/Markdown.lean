/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Commands

/-!
# Rendering an index as markdown, for doc-gen4

The blueprint renders an `IndexTable` as a Verso table. doc-gen4 has no such mechanism — what it
renders is **docstrings**, as markdown. That is the surface `@[pkc_math]` already exploits to get
typeset equations onto an API page without doc-gen4 knowing anything about the calculus, and it is
the surface used here: the index page is a module whose *module docstring* is generated, and
doc-gen4 renders a module docstring at the top of that module's page.

`Lean.addMainModuleDoc` is the write, and it works only for the module currently being elaborated —
which is exactly right here, since the page is its own module and writes its own doc.

## Why the per-declaration blocks are not written the same way

The natural companion would be to append "the crossings that mint this kind" to each *kind's* own
docstring, the way `@[pkc_math]` appends to a definition's. That is not possible.
`Lean.addDocStringCore` refuses a declaration that lives in an imported module, and the crossings and
theorems that mention a kind are almost always declared in *later* modules than the kind itself — by
the time the facts are known, the kind is imported. So the per-declaration blocks are spliced into
the generated HTML afterwards, by `scripts/inject-index-docs.py`, from the JSON this module's
`indexJson` produces. The index *page* has no such constraint and stays pure Lean.
-/

namespace PropertyKindCalculus.Index

open Lean Meta Elab

/-! ## Markdown -/

/-- Escape the characters that would break a GitHub-flavoured markdown table cell. A pipe inside a
cell ends the cell, and a newline ends the row; both occur in real content (a kind's Algebra cell
holds `a · b → c` chains, a docstring gloss can hold anything). -/
def mdEscape (s : String) : String :=
  (s.replace "|" "\\|").replace "\n" " "

/-- A cell as markdown. A `decl` reference is written as a code span holding the **fully qualified**
name, because doc-gen4 resolves such a span to a link to that declaration's page — the short display
name would not resolve. -/
def IndexCell.toMarkdown : IndexCell → String
  | .text s      => mdEscape s
  | .code s      => if s.isEmpty then "" else "`" ++ mdEscape s ++ "`"
  | .decl n _    => "`" ++ mdEscape (toString n) ++ "`"
  | .links items =>
    String.intercalate ", " (items.toList.map fun (n, _) => "`" ++ mdEscape (toString n) ++ "`")

/-- A table as a markdown section: a level-2 heading, the row count, and a GFM table. An empty table
renders as a sentence rather than a headerless table, so a reader is told there are none instead of
being shown an empty grid. -/
def IndexTable.toMarkdown (t : IndexTable) : String :=
  let heading := s!"## {t.title}\n"
  if t.rows.isEmpty then
    heading ++ "\nNone in scope.\n"
  else
    let header := "| " ++ String.intercalate " | " t.headers.toList ++ " |"
    let sep := "|" ++ String.intercalate "|" (t.headers.toList.map (fun _ => "---")) ++ "|"
    let body := t.rows.toList.map fun r =>
      "| " ++ String.intercalate " | " (r.toList.map IndexCell.toMarkdown) ++ " |"
    heading ++ s!"\n{t.rows.size} row(s).\n\n" ++ String.intercalate "\n" (header :: sep :: body)
      ++ "\n"

/-- The markdown for a whole index page: an introduction, then one section per requested table. -/
def indexPageMarkdown (intro : String) (tables : Array IndexTable) : String :=
  String.intercalate "\n\n" (intro :: tables.toList.map IndexTable.toMarkdown)

/-! ## The page command -/

open Command in
/-- `#pkc_index_page "<intro>" ["<table>", …] [ns …]` generates this module's own module docstring
from the named indexes, so doc-gen4 renders them as the module's page.

    #pkc_index_page "Every kind, crossing and record in the core spine."
      ["annotations", "carriers", "kinds"] PropertyKindCalculus

Writes with `Lean.addMainModuleDoc`, which is legal only for the module being elaborated — hence a
dedicated module per page. -/
elab "#pkc_index_page " intro:str "[" ids:str,+ "]" nss:ident* : command => do
  let scope := nss.map (·.getId)
  let tables ← liftTermElabM do
    ids.getElems.mapM fun id => tableById id.getString scope
  let md := indexPageMarkdown intro.getString tables
  modifyEnv fun env => addMainModuleDoc env { doc := md, declarationRange := default }

/-! ## Per-declaration blocks, for the HTML injector

What the per-declaration splice needs is, for each kind, the block to append to its own doc-gen4
page. Emitting it here — rather than teaching a Python script the calculus — keeps every question
about *what* a kind's algebra is on the Lean side, and leaves the script with only the mechanical
question of where in the page it goes.

The block is **HTML**, not markdown, for the same reason: converting markdown would be a second
renderer, in another language, that could disagree with this one. -/

/-- Escape text for inclusion in HTML. -/
def htmlEscape (s : String) : String :=
  ((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;"

/-- An HTML list of code items under an italic caption. -/
private def htmlSection (caption : String) (items : List String) : String :=
  s!"<p><em>{caption}</em></p><ul>"
    ++ String.intercalate "" (items.map fun i => s!"<li><code>{htmlEscape i}</code></li>")
    ++ "</ul>"

/-- The per-declaration blocks: `declaration name → HTML`. For each kind in scope, its authored
kind-algebra edges, the crossings that mint it, and the theorems that mention it — the three facts
that answer "what can I do with this kind?", delivered on the kind's own page rather than only in a
table somewhere else. -/
def declarationBlocks (scope : Scope) : MetaM (Array (Name × String)) := withHarvestBudget do
  let env ← getEnv
  let kinds := constantsOfType env ``PropertyKindCalculus.KindOfProperty scope
  if kinds.isEmpty then return #[]
  let edges ← KindEdges.edgesByKind kinds
  let thms := theoremsMentioning env kinds
  let sites ← BoundaryAudit.boundarySites scope
  let mut out : Array (Name × String) := #[]
  for k in kinds do
    let es := (edges.getD k #[]).map (·.edge)
    let ts := thms.getD k #[]
    -- A crossing mints this kind if the audit recorded it among the kinds the site constructs. The
    -- audit renders mints with `ppExpr`, which qualifies or not depending on the ambient namespace,
    -- so both spellings are accepted.
    let crossings := sites.filter fun s =>
      s.tier.isSome && s.mints.any fun m => m == toString k || m == lastComponent k
    let mut parts : Array String := #[]
    unless es.isEmpty do
      parts := parts.push (htmlSection "Authored kind algebra" es.toList)
    unless crossings.isEmpty do
      parts := parts.push (htmlSection "Authored crossings minting this kind"
        (crossings.toList.map fun s => s!"{s.decl} — {s.tier.map (·.label) |>.getD ""}"))
    unless ts.isEmpty do
      parts := parts.push (htmlSection "Theorems about this kind" (ts.toList.map toString))
    unless parts.isEmpty do
      out := out.push (k, String.intercalate "" parts.toList)
  return out

/-- The per-declaration blocks as JSON, for `scripts/inject-index-docs.py`. -/
def indexJson (scope : Scope) : MetaM Json := do
  let blocks ← declarationBlocks scope
  return Json.mkObj (blocks.toList.map fun (n, h) => (toString n, Json.str h))

end PropertyKindCalculus.Index
