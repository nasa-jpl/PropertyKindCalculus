/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Ontology
import PropertyKindCalculus.Index.Structures
import PropertyKindCalculus.Index.Annotations

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
`KindLayer` — see `KindLayer.core` for the shape. -/
def tableById (id : String) (scope : Scope := #[]) : MetaM IndexTable := withHarvestBudget do
  match id with
  | "annotations"          => return annotationsTable
  | "crossings"            => crossingsTable scope
  | "carriers"             => carriersTable
  | "pkc-math"             => pkcMathTable scope
  | "pkc-math-symbol"      => pkcMathSymbolTable scope
  | "pkc-math-config"      => configTable scope
  | "pkc-math-transparent" => transparentTable scope
  | "kinds"                => kindsTable .core scope
  | "systems"              => identityTable "systems" "Systems" "System"
                                ``PropertyKindCalculus.System
                                ``PropertyKindCalculus.DedicatedKind.system scope
  | "components"           => identityTable "components" "Components" "Component"
                                ``PropertyKindCalculus.Component
                                ``PropertyKindCalculus.DedicatedKind.component scope
  | "dedicated-kinds"      => dedicatedKindsTable scope
  | "examinations"         => examinationsTable scope
  | "records"              => recordsTable scope
  | "operations"           => operationsTable scope
  | other => throwError "unknown index table '{other}'; available: {tableIds}"
where
  /-- The table identifiers, for the error message and for documents that enumerate them. -/
  tableIds : String :=
    String.intercalate ", "
      ["annotations", "crossings", "carriers", "pkc-math", "pkc-math-symbol", "pkc-math-config",
       "pkc-math-transparent", "kinds", "systems", "components", "dedicated-kinds",
       "examinations", "records", "operations"]

/-! ## Plain-text rendering, for the InfoView and for pinned probes -/

/-- A cell as plain text: a declaration reference shows its display text, a link list shows them
comma-separated. -/
def IndexCell.toText : IndexCell → String
  | .text s      => s
  | .code s      => s
  | .decl _ d    => d
  | .links items => String.intercalate ", " (items.toList.map (·.2))

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

end PropertyKindCalculus.Index
