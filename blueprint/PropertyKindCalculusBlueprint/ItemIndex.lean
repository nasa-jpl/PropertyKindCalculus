/-
# Live tables generated from the catalogue (the `iso_doc_table` directive)

The ISO/IEC 80000 item-index tables and the per-part tally are *generated* from
the Lean catalogues (`PropertyKindCalculus.Iso80000.PartN.catalogue`) rather than
maintained by hand, so they cannot drift from the formalized specification. A
chapter builds a `DocTable` value out of its catalogue (item number, quantity,
symbol, unit, and the dimension rendered from the PhysLib `Dimension`) and renders
it with

```
:::iso_doc_table myTableConstant
:::
```

The directive evaluates the named `DocTable` constant at blueprint-build time and
emits an ordinary Verso table (`Block.table`); item cells become the same
hoverable cross-reference links the `{bpref "…"}` role produces, so all existing
table/linking machinery is reused.
-/

import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculus.Iso80000.Catalogue
import PropertyKindCalculus.Index.Basic

open Lean Elab
open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open PropertyKindCalculus.Iso80000 (CataloguedKind StandardRef)

namespace PropertyKindCalculusBlueprint.ItemIndex

/-- A single table cell. `ref` renders a Blueprint cross-reference (the same link
the `{bpref "tag"}[text]` role makes); `code` renders inline code; `text` is
plain text; `md` is a small markdown-ish string (runs of text, inline `` `code` ``,
`*emph*` and `**strong**`) parsed at build time — for prose cells that mix code
and text, and for the docstrings the generated indexes quote. -/
inductive Cell where
  | text (s : String)
  | code (s : String)
  | ref (tag : String) (text : String)
  /-- A cross-reference to a **section of this document**, by the tag its `%%% tag := … %%%` block
  gives it. Distinct from `ref`, which addresses a *blueprint node* (`{bpref "def_…"}`): the two
  resolve in different domains, so a section tag passed to `ref` would be a dead link. This is what
  the catalogue tables use to reach the prose that explains each row. -/
  | secref (tag : String) (text : String)
  | md (s : String)
  /-- A comma-separated list of cross-references, each a `(tag, text)` pair. An
  empty `tag` renders its `text` as inline code (no link); a non-empty `tag`
  renders a Blueprint cross-reference, exactly like `ref`. -/
  | links (items : List (String × String))
  /-- Labeled groups of code lines: each group an emphasized caption over a list with one code
  line per entry — the rendering of `IndexCell.codeGroups`, which the kind tables' Algebra
  column uses for its produced / consumed equation groups. Each line is a `(tag, text)` pair
  like `links`: an empty tag renders plain inline code, a non-empty one a Blueprint
  cross-reference styled as code — for an equation, the declaration that authored it. -/
  | codeGroups (groups : List (String × List (String × String)))
deriving Repr, Inhabited, BEq

/-- A generated table: its header titles and its body rows (each a list of cells,
one per column), plus whether it is centre-aligned. Rendered by the
`iso_doc_table` directive. -/
structure DocTable where
  headers : List String
  rows : List (List Cell)
  center : Bool := false
deriving Repr, Inhabited

/-! ### Inline markup for `md` cells

An `md` cell is parsed into runs and emitted as `Inline.{text,code,emph,bold}`
*terms*. That keeps a prose-rich table term-built (one elaboration) instead of
going through the interpreter cell-by-cell the way a markup `:::table` does,
which is the dominant cost of a cold blueprint build.

The grammar itself is `PropertyKindCalculus.Index.parseProse`, not a copy of it.
The library needs that grammar anyway — its generated indexes quote docstrings,
and a docstring is markdown — and soil-moisture-model's technical reference
renders the same indexes through its own adapter. Three parsers for one dialect
is three chances for a cell to mean something different depending on which
document it lands in, so the dialect is defined once, in the library, and every
renderer consumes runs rather than characters. -/

/-- An inline run within an `md` cell. -/
abbrev Run := PropertyKindCalculus.Index.ProseRun

/-- Split an `md` cell into its inline runs. Backtick spans are code, single-
asterisk spans are emphasis, double-asterisk spans are strong; spans nest, and an
unterminated delimiter stays literal text. -/
def parseRuns (s : String) : List Run := (PropertyKindCalculus.Index.parseProse s).toList

/-! ## Building a `DocTable` from a catalogue

The per-item cross-reference tag is *editorial* data (which proof or definition an
item links to), so it cannot be derived from the catalogue. It is supplied as a
sparse override map keyed by item designation, with a per-part default tag; every
other column is read from the catalogue (the dimension via `renderDimension`). -/

/-- Resolve an item's cross-reference tag from the sparse `refs` map, defaulting
to `dflt`. -/
def refOf (refs : List (String × String)) (dflt item : String) : String :=
  (refs.lookup item).getD dflt

/-- The standard ISO/IEC 80000 item index — Item, Quantity, Symbol, Unit,
Dimension — read entirely from `cat`. The Item cell links to its blueprint node
(`refs`, defaulting to `dflt`); the Dimension cell is computed by
`renderDimension`. -/
def standardIndex (cat : List CataloguedKind) (dflt : String)
    (refs : List (String × String) := []) : DocTable where
  headers := ["Item", "Quantity", "Symbol", "Unit", "Dimension"]
  rows := cat.map fun c =>
    [ .ref (refOf refs dflt c.item) c.item, .text c.qk.kind.id,
      .code c.symbol, .code c.coherentUnit, .code c.dimString ]

/-- The measurement principle of a characteristic number: its examination
principle with the leading transport-context tag (`"momentum: "`, …) removed. -/
def principleText (c : CataloguedKind) : String :=
  match c.qk.kind.examPrinciple with
  | none => ""
  | some s =>
    match s.splitOn ": " with
    | _ :: rest => String.intercalate ": " rest
    | [] => s

/-- The ISO 80000-11 variant index: every characteristic number is dimension one,
so the last column is the measurement principle (from the examination principle)
rather than a unit/dimension. -/
def characteristicNumberIndex (cat : List CataloguedKind) (dflt : String)
    (refs : List (String × String) := []) : DocTable where
  headers := ["Item", "Characteristic number", "Symbol", "Measurement principle (dimension one)"]
  rows := cat.map fun c =>
    [ .ref (refOf refs dflt c.item) c.item, .text c.qk.kind.id,
      .code c.symbol, .text (principleText c) ]

/-- A prose table whose cells are markdown-ish strings (`md` cells). For the
hand-authored comparison tables that are not catalogue-derived but still benefit
from being term-built rather than elaborated cell-by-cell as markup. -/
def mdTable (center : Bool) (headers : List String) (rows : List (List String)) : DocTable where
  headers := headers
  rows := rows.map (·.map Cell.md)
  center := center

/-! ## The per-part tally

A count, computed live from each part's catalogue, of how many quantity kinds the
work specifies from each ISO/IEC 80000 part, with a grand total. -/

/-- A tally of catalogued quantity kinds per part: Part, Title, and count, with a
final Total row. Each entry pairs a part's citation reference with its catalogue,
so the counts are read directly from `catalogue.length` and cannot drift. -/
def tallyTable (entries : List (StandardRef × List CataloguedKind)) : DocTable where
  headers := ["Part", "Title", "Quantity kinds"]
  rows :=
    entries.map (fun (r, cat) =>
      [Cell.text r.designation, Cell.text r.title, Cell.text (toString cat.length)])
    ++ [[Cell.text "Total", Cell.text "",
         Cell.text (toString (entries.foldl (fun n p => n + p.2.length) 0))]]

/-! ## Evaluating a `DocTable` constant at elaboration time -/

unsafe def evalDocTableUnsafe (stx : Syntax) : TermElabM DocTable := do
  let ty ← Term.elabType (← `(PropertyKindCalculusBlueprint.ItemIndex.DocTable))
  Term.evalTerm DocTable ty stx

@[implemented_by evalDocTableUnsafe]
opaque evalDocTable (stx : Syntax) : TermElabM DocTable

/-! ## Building the table term -/

/-- One inline run as a Verso `Inline` term. Recursive, because the runs are: a
docstring lead-in is routinely `**… the *branched* principal …**`, and rendering
only the outer span would put the inner markers back on the page. -/
partial def runInline : Run → DocElabM Term
  | .text t   => `(Verso.Doc.Inline.text $(quote t))
  | .code t   => `(Verso.Doc.Inline.code $(quote t))
  | .emph rs  => do
    let inls ← rs.mapM runInline
    `(Verso.Doc.Inline.emph #[$inls,*])
  | .strong rs => do
    let inls ← rs.mapM runInline
    `(Verso.Doc.Inline.bold #[$inls,*])

/-- A cell becomes a one-paragraph block; `ref` cells become the `Inline.informal`
node that `bpref` produces (the href and hover are resolved from the traversal
state at render time, exactly as for a hand-written `bpref`). -/
def cellBlock : Cell → DocElabM Term
  | .text s => `(Verso.Doc.Block.para #[Verso.Doc.Inline.text $(quote s)])
  | .code s => `(Verso.Doc.Block.para #[Verso.Doc.Inline.code $(quote s)])
  | .ref tag txt => do
    let data : Informal.InlineData :=
      { label := Informal.LabelNameParsing.parse tag }
    `(Verso.Doc.Block.para
        #[Verso.Doc.Inline.other (Informal.Inline.informal $(quote data))
            #[Verso.Doc.Inline.text $(quote txt)]])
  | .secref tag txt =>
    -- The node the `{ref "tag"}[text]` role produces: the domain is left `none` so the traversal
    -- resolves it in the section domain, and the destination is filled in at traversal time.
    `(Verso.Doc.Block.para
        #[Verso.Doc.Inline.other
            (Verso.Genre.Manual.Inline.ref $(quote tag) none none none)
            #[Verso.Doc.Inline.text $(quote txt)]])
  | .md s => do
    let inls ← (parseRuns s).toArray.mapM runInline
    `(Verso.Doc.Block.para #[$inls,*])
  | .links items => do
    let parts ← items.toArray.mapM fun (tag, txt) =>
      if tag.isEmpty then
        `(Verso.Doc.Inline.code $(quote txt))
      else do
        let data : Informal.InlineData :=
          { label := Informal.LabelNameParsing.parse tag }
        `(Verso.Doc.Inline.other (Informal.Inline.informal $(quote data))
            #[Verso.Doc.Inline.text $(quote txt)])
    let sep ← `(Verso.Doc.Inline.text ", ")
    let inls := parts.foldl (init := (#[] : Array Term)) fun acc p =>
      if acc.isEmpty then #[p] else (acc.push sep).push p
    `(Verso.Doc.Block.para #[$inls,*])
  | .codeGroups groups => do
    -- One equation per line: each group is an emphasized caption over a list of code items,
    -- and the cell is their concatenation. A line with a tag links its code to that node.
    let mut blocks : Array Term := #[]
    for (label, lines) in groups do
      blocks := blocks.push (← `(Verso.Doc.Block.para
        #[Verso.Doc.Inline.emph #[Verso.Doc.Inline.text $(quote label)]]))
      let items ← lines.toArray.mapM fun (tag, txt) => do
        let inl ←
          if tag.isEmpty then
            `(Verso.Doc.Inline.code $(quote txt))
          else do
            let data : Informal.InlineData :=
              { label := Informal.LabelNameParsing.parse tag }
            `(Verso.Doc.Inline.other (Informal.Inline.informal $(quote data))
                #[Verso.Doc.Inline.code $(quote txt)])
        `(Verso.Doc.ListItem.mk #[Verso.Doc.Block.para #[$inl]])
      blocks := blocks.push (← `(Verso.Doc.Block.ul #[$items,*]))
    `(Verso.Doc.Block.concat #[$blocks,*])

/-- Build the `Block.table` term from an evaluated `DocTable`. The header row is
prepended and rendered as `<th>` (the table extension treats row 0 as the header
when `header := true`). -/
def docTableTerm (tbl : DocTable) : DocElabM Term := do
  let cols := tbl.headers.length
  let headerRow : List Cell := tbl.headers.map Cell.text
  let allCells : List Cell := headerRow ++ tbl.rows.flatten
  let cellTerms ← allCells.toArray.mapM cellBlock
  let alignStx ←
    if tbl.center then `(some Verso.Genre.Manual.TableConfig.Alignment.center)
    else `(some Verso.Genre.Manual.TableConfig.Alignment.left)
  `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.table $(quote cols) true none $alignStx)
      #[Verso.Doc.Block.ul #[$[Verso.Doc.ListItem.mk #[$cellTerms]],*]])

/-! ## The directive -/

structure Config where
  /-- The name of the `DocTable` constant to render. -/
  table : Ident

section
variable [Monad m] [MonadError m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadFileMap m]

def Config.parse : ArgParse m Config :=
  Config.mk <$> .positional `table ValDesc.ident

instance : FromArgs Config m := ⟨Config.parse⟩
end

/-- `:::iso_doc_table myDocTable` renders the `DocTable` constant `myDocTable` as a
live table. Contents are ignored. -/
@[directive]
def iso_doc_table : DirectiveExpanderOf Config
  | cfg, _contents => do
    let tbl ← evalDocTable cfg.table
    docTableTerm tbl

end PropertyKindCalculusBlueprint.ItemIndex
