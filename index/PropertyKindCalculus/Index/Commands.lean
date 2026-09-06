/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Ontology
import PropertyKindCalculus.Index.Structures
import PropertyKindCalculus.Index.Annotations
import PropertyKindCalculus.Index.Relations
import PropertyKindCalculus.Index.Budgets

/-!
# `#pkc_index` — the index from the InfoView, and the table dispatcher documents call

Two surfaces over the harvests:

* `tableById` — name a table, get it. This is what a Verso directive calls, so a document writes
  `{pkc_index "crossings"}` rather than naming a Lean function, and adding a table here makes it
  available to every document at once.
* `#pkc_index` — the same thing as an `info` message, so an author can read an index without
  building a document, and a probe can pin one with `#guard_msgs` the way
  `tests/…/Core/BoundaryAudit.lean` pins the audit.

The plain-text rendering below is *not* the documents' rendering: a blueprint or doc-gen4 table maps
`IndexCell` onto real links. It exists so the InfoView surface and the pinned probes have something
stable and diffable to show.
-/

namespace PropertyKindCalculus.Index

open Lean Meta Elab

/-- Every table this library can build, by identifier. Unknown identifiers throw, listing what is
available, because a mistyped table name in a document should fail the build rather than render an
empty table that reads as "there are none".

`dimensioned-kinds` is absent by design: that layer's type lives behind PhysLib and Mathlib, which
this library does not import. A document that imports it calls `kindsTable` with its own
`KindLayer` — see `KindLayer.core` for the shape. `dimensional-coverage` is gated the same way:
a document that imports `PropertyKindCalculus.DimensionalCoverage` calls its `coverageTable`
directly. -/
def tableById (id : String) (scope : Scope := #[]) : MetaM IndexTable := withHarvestBudget do
  match id with
  | "annotations"          => return annotationsTable
  | "commands"             => return commandsTable
  | "crossings"            => crossingsTable scope
  | "carriers"             => carriersTable
  | "pkc-math"             => pkcMathTable scope
  | "pkc-math-symbol"      => pkcMathSymbolTable scope
  | "pkc-math-config"      => configTable scope
  | "pkc-math-transparent" => transparentTable scope
  | "kinds"                => kindsTable .core scope
  | "sorts"                => identityTable "sorts" "Sorts of system" "Sort"
                                ``PropertyKindCalculus.SortOfSystem
                                (some ``PropertyKindCalculus.DedicatedKind.sort) scope
  | "systems"              => identityTable "systems" "Systems" "System"
                                ``PropertyKindCalculus.System none scope
  | "components"           => identityTable "components" "Components" "Component"
                                ``PropertyKindCalculus.Component
                                (some ``PropertyKindCalculus.DedicatedKind.component) scope
  | "dedicated-kinds"      => dedicatedKindsTable scope
  | "examinations"         => examinationsTable scope
  | "records"              => recordsTable scope
  | "operations"           => operationsTable scope
  | "relations"            => relationsTable scope
  | "port-budgets"         => portBudgetsTable scope
  | other => throwError "unknown index table '{other}'; available: {tableIds}"
where
  /-- The table identifiers, for the error message and for documents that enumerate them. -/
  tableIds : String :=
    String.intercalate ", "
      ["annotations", "commands", "crossings", "carriers", "pkc-math", "pkc-math-symbol",
       "pkc-math-config", "pkc-math-transparent", "kinds", "sorts", "systems", "components",
       "dedicated-kinds", "examinations", "records", "operations", "relations",
       "port-budgets"]

/-! ## Plain-text rendering, for the InfoView and for pinned probes -/

/-- A cell as plain text: a declaration reference shows its display text, a link list shows them
comma-separated. A `prose` cell keeps its markdown markers, because this surface is a report of what
the docstrings say and showing the author their own text unaltered is the honest rendering — the
surfaces that *typeset* it are the ones that parse. -/
def IndexCell.toText : IndexCell → String
  | .text s      => s
  | .code s      => s
  | .prose s     => s
  | .decl _ d    => d
  | .links items => String.intercalate ", " (items.toList.map (·.2))
  | .tag _ d     => d

/-- A table as a plain-text block: a title line, the headers, and one ` | `-separated line per row.

Deliberately unaligned — a `#guard_msgs` pin should diff on content, not on padding that shifts when
an unrelated row gets longer. Trailing whitespace is stripped for the same reason: a row ending in an
empty cell would otherwise end in `" | "`, and an *invisible* trailing space is the worst possible
thing to have to reproduce by hand in a pin. -/
def IndexTable.toText (t : IndexTable) : String :=
  let header := String.intercalate " | " t.headers.toList
  let body := t.rows.toList.map fun r =>
    String.intercalate " | " (r.toList.map IndexCell.toText)
  let lines := (s!"{t.title} ({t.rows.size} row(s))") :: header :: body
  String.intercalate "\n" (lines.map fun l => l.trimAsciiEnd.toString)

open Command in
/-- `#pkc_index "<table>" [ns …]` prints one generated index as a single `info` message, optionally
restricted to the given namespaces.

    #pkc_index "crossings" PropertyKindCalculus
    #pkc_index "pkc-math-symbol"

The table name is a *string* because the identifiers are hyphenated (`pkc-math-symbol`), which is
also how a document names them (`{pkc_index "crossings"}`) — one spelling for both surfaces. The
names are those of `tableById`. With no namespaces the index is unrestricted, which after Mathlib is
rarely what you want for `kinds` — scope it. -/
elab "#pkc_index " id:str nss:ident* : command => liftTermElabM do
  let tbl ← tableById id.getString (nss.map (·.getId))
  logInfo m!"{tbl.toText}"

open Command in
/-- `#pkc_summary_overflow [ns …]` lists the docstrings an index quotes whose first paragraph is
wider than the column that quotes it, widest first.

    #pkc_summary_overflow SoilMoisture.Algorithm

**A command rather than a build warning**, which is the design point worth stating because a warning
is the obvious thing to want. There is no source position to raise one at: `summaryLine` runs while
the *document* elaborates, so a warning raised where the overflow is detected attaches to the
`:::pkc_index` directive — one diagnostic on a chapter, naming none of the docstrings that caused it,
in a file whose author may not own any of them. Asked as a command, the question is answered where
the docstrings are, over the scope the asker chose.

An over-budget docstring is **not a defect**. It truncates on a run boundary and stays well-formed
markdown at any length; the harvest reads a paragraph rather than a line exactly so that a docstring
can be written for its reader first. What this reports is narrower: these particular paragraphs open
a table column, and the fix where one is wanted is a paragraph break — a first paragraph saying what
the declaration *is*, with the argument below it. -/
elab "#pkc_summary_overflow" nss:ident* : command => liftTermElabM do
  let env ← getEnv
  let scope := nss.map (·.getId)
  let maxLen := 160
  let quoted := quotedDecls env scope
  let over ← summaryOverflows env scope maxLen
  if over.isEmpty then
    logInfo m!"summary overflow — none of {quoted.size} quoted docstring(s) exceed {maxLen} characters"
  else
    let lines := over.toList.map fun o => s!"{o.decl} — {o.width}"
    logInfo m!"summary overflow ({over.size} of {quoted.size} quoted docstring(s) exceed \
      {maxLen} characters):\n{String.intercalate "\n" lines}"

end PropertyKindCalculus.Index
