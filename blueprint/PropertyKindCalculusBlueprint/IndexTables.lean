/-
# The `pkc_index` and `pkc_annotations` directives — the generated self-index, rendered

`{pkc_index "crossings"}` expands into the corresponding table from
`PropertyKindCalculus.Index`, which harvests it from the environment. Same arrangement as
`iso_doc_table`, `traceability` and `crossrefs`: decl-indexed metadata read at elaboration time,
assembled as an `ItemIndex.DocTable`, rendered by the shared `ItemIndex.docTableTerm`. A renamed
declaration is a build error, so an index can never drift from the Lean source.

## Why the harvest lives in the library and only the rendering lives here

The tables are wanted by two documents in two repositories: this blueprint, and
soil-moisture-model's technical reference. That repository requires PropertyKindCalculus **from
git**, so it can import `PropertyKindCalculus.Index` but cannot reach this `blueprint/`
sub-package — and PropertyKindCalculus itself deliberately does not depend on Verso, which is why
this package exists separately in the first place.

So the split is: all of the indexing logic sits in the library, emitting Verso-free `IndexCell`s;
each document supplies the ~30 lines below that map an `IndexCell` onto its own table machinery.
What is duplicated downstream is rendering glue, not indexing.

## Resolving a declaration to a link

An `IndexCell.decl` names a declaration and leaves the rendering open, because each document
resolves it differently. Here it becomes a blueprint cross-reference via
`Informal.Environment.labelsForLeanDecl` — the same resolution `traceability` uses — falling back to
inline code where a declaration has no blueprint node, which most of the indexed declarations do not.
-/

import VersoManual
import VersoBlueprint
import VersoBlueprint.Environment
import VersoBlueprint.TraversalIndex
import PropertyKindCalculus.Index
import PropertyKindCalculus.Dimension
import PropertyKindCalculusBlueprint.ItemIndex

open Lean Elab
open Verso Doc Elab
open Verso.Genre.Manual
open Verso.ArgParse
open PropertyKindCalculusBlueprint.ItemIndex

namespace PropertyKindCalculusBlueprint.IndexTables

open PropertyKindCalculus.Index

/-! ## The dimensioned kind layer

`PropertyKindCalculus.Index` cannot name `DimensionedKind`: that type lives behind PhysLib and
Mathlib, and the whole point of the harvest library is to be importable without them. This package
*does* import the dimensioned layer (the blueprint documents it), so the layer's spec is built here
and handed to the same generic `kindsTable`.

It carries no scale column — a `DimensionedKind` wraps its `KindOfProperty` rather than repeating its
fields, and its own extra datum is the PhysLib `Dimension`, which the ISO 80000 chapters already
render properly through `ItemIndex.renderDimension`. What this table adds over those is the
**Algebra** column: the authored edges, which the item tables do not carry. -/
def dimensionedLayer : KindLayer where
  id := "dimensioned-kinds"
  title := "Dimensioned kinds"
  ty := ``PropertyKindCalculus.DimensionedKind
  identity := #[``PropertyKindCalculus.DimensionedKind.kind,
                ``PropertyKindCalculus.KindOfProperty.id]

/-- Every table available to a directive: the library's, plus the dimensioned kind layer this
package can see and the library cannot. -/
def indexTable (id : String) (scope : Array Name) : MetaM IndexTable :=
  if id == "dimensioned-kinds" then kindsTable dimensionedLayer scope
  else tableById id scope

/-! ## `IndexCell` → `ItemIndex.Cell` -/

/-- The blueprint node label for a declaration, or `""` when it has none. -/
def labelFor (n : Name) : DocElabM String := do
  let labels ← Informal.Environment.labelsForLeanDecl n
  return (labels[0]?.map (·.toString)).getD ""

/-- Map a harvested cell onto the blueprint's own cell type. A declaration with a blueprint node
becomes a hoverable cross-reference; one without becomes inline code — which is the common case, and
is why `ref` is not used unconditionally (an unresolvable tag would render as a dead link).

A `prose` cell is a quoted docstring, so it becomes an `md` cell: the two are the same thing under
two names, and `ItemIndex.parseRuns` is `PropertyKindCalculus.Index.parseProse`. Sending it to `text`
instead is what puts `**` on the page. -/
def toCell : IndexCell → DocElabM Cell
  | .text s => return .text s
  | .prose s => return .md s
  | .code s => return .code s
  | .decl n display => do
    let label ← labelFor n
    return if label.isEmpty then .code display else .ref label display
  | .links items => do
    let resolved ← items.toList.mapM fun (n, display) => do
      return ((← labelFor n), display)
    return .links resolved

/-- Assemble a harvested table as a renderable `DocTable`. -/
def toDocTable (t : IndexTable) : DocElabM DocTable := do
  let rows ← t.rows.toList.mapM fun r => r.toList.mapM toCell
  return { headers := t.headers.toList, rows }

/-! ## The directives -/

/-- `{pkc_index "…"}` takes the table name and an optional namespace to restrict it to. -/
structure Config where
  /-- The table identifier (`"crossings"`, `"kinds"`, `"records"`, …). -/
  table : String
  /-- The namespace to restrict the index to; unrestricted when absent. -/
  scope : Name := .anonymous

section
variable [Monad m] [MonadError m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadFileMap m]

def Config.parse : ArgParse m Config :=
  Config.mk <$> .positional `table ValDesc.string
            <*> .namedD `scope ValDesc.name .anonymous

instance : FromArgs Config m := ⟨Config.parse⟩
end

/--
`:::pkc_index "crossings"` renders the named generated index; `scope := Some.Namespace` restricts it.
Contents are ignored.

    :::pkc_index "kinds" scope := PropertyKindCalculus.Iso80000.Part4
    :::

Scoping matters for the kind tables: the dimensioned layer has several hundred inhabitants across
the ISO 80000 parts, so an unscoped `dimensioned-kinds` is one unreadable table rather than a dozen
useful ones. An unknown table name is a build error, not an empty table — an index that silently
renders nothing reads as "there are none", which is the one thing a generated index must never say
by accident.
-/
@[directive]
def pkc_index : DirectiveExpanderOf Config
  | cfg, _contents => do
    let scope := if cfg.scope.isAnonymous then #[] else #[cfg.scope]
    let tbl ← indexTable cfg.table scope
    docTableTerm (← toDocTable tbl)

/-- The annotation reference takes no arguments. -/
structure NoConfig where
  deriving Inhabited

section
variable [Monad m] [MonadError m]

def NoConfig.parse : ArgParse m NoConfig := pure {}

instance : FromArgs NoConfig m := ⟨NoConfig.parse⟩
end

/--
`:::pkc_annotations` renders the annotation reference table — every annotation the library defines,
what it attaches to, what it does, and whether a build-time check depends on it.

Generated from `PropertyKindCalculus.Index.catalogue`, so the chapter cannot omit an annotation that
someone added to the library and forgot to document here.
-/
@[directive]
def pkc_annotations : DirectiveExpanderOf NoConfig
  | _cfg, _contents => do
    docTableTerm (← toDocTable annotationsTable)

end PropertyKindCalculusBlueprint.IndexTables
