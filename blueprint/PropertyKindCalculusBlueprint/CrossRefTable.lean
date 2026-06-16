/-
# The `crossrefs` directive — auto-generated external cross-reference tables

`{crossrefs dybkaer}` / `{crossrefs vim4}` expand into an index table built from
the typed cross-reference annotations harvested by `PropertyKindCalculus.CrossRefs`.
Each row maps an external locus (a Dybkær section or a VIM 4 2CD clause) to the
external term and to this work's declaration, linked to its blueprint node.

The annotations are decl-indexed environment metadata, so the directive reads them
from the environment at elaboration time and resolves each declaration to its
blueprint node label via `Informal.Environment.labelsForLeanDecl`; the node's href
is resolved at render time via `Informal.TraversalIndex.Nodes.href?`. This mirrors
the `Block.bibliography` pattern (collect at elaboration, link at render).
-/

import VersoManual
import VersoBlueprint
import VersoBlueprint.Environment
import VersoBlueprint.TraversalIndex
import PropertyKindCalculus.CrossRefs

open Lean Elab
open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open PropertyKindCalculus.CrossRefs

namespace PropertyKindCalculusBlueprint

/-- One rendered cross-reference row. -/
structure CrossRefRow where
  /-- The external locus (Dybkær section / VIM 4 2CD clause). -/
  locus : String
  /-- The external term. -/
  term : String
  /-- The display name of this work's declaration (its last name component). -/
  shortName : String
  /-- The blueprint node label for the declaration, "" if it has no node. -/
  label : String
  /-- A short note on the correspondence. -/
  note : String
  deriving FromJson, ToJson, Quote, Inhabited

/-- The data backing one cross-reference table. -/
structure CrossRefTableData where
  /-- The citation header for the source. -/
  sourceCite : String
  /-- The rows, already sorted by locus. -/
  rows : Array CrossRefRow
  deriving FromJson, ToJson, Quote, Inhabited

open Verso Doc Elab Genre Manual in
block_extension Block.crossRefTable (tableData : CrossRefTableData) where
  data := toJson tableData
  traverse _id _data _contents := pure none
  toTeX := none
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun _goI _goB _id data _blocks => do
      let .ok tableData := fromJson? (α := CrossRefTableData) data
        | HtmlT.logError "Malformed data in Block.crossRefTable.toHtml"
          pure .empty
      let st ← HtmlT.state
      let bodyRows : Array Verso.Output.Html := tableData.rows.map fun r =>
        let concept : Verso.Output.Html :=
          let href? : Option String :=
            if r.label.isEmpty then Option.none
            else Informal.TraversalIndex.Nodes.href? st r.label.toName
          match href? with
          | some href => {{ <a href={{href}}><code>{{.text true r.shortName}}</code></a> }}
          | Option.none => {{ <code>{{.text true r.shortName}}</code> }}
        {{ <tr>
             <td>{{.text true r.locus}}</td>
             <td>{{.text true r.term}}</td>
             <td>{{concept}}</td>
             <td>{{.text true r.note}}</td>
           </tr> }}
      pure {{
        <div class="bp_crossref_table">
          <p><strong>{{.text true tableData.sourceCite}}</strong></p>
          <table>
            <thead>
              <tr><th>"Locus"</th><th>"Term"</th><th>"This work"</th><th>"Note"</th></tr>
            </thead>
            <tbody>{{bodyRows}}</tbody>
          </table>
        </div>
      }}

/-- Arguments for the `{crossrefs ...}` directive: the source tag,
`dybkaer` or `vim4`. -/
structure CrossRefConfig where
  /-- The source tag, `"dybkaer"` or `"vim4"`. -/
  source : String
  /-- The syntax of the source argument, for error reporting. -/
  sourceSyntax : Syntax := Syntax.missing
  deriving Inhabited

section
variable [Monad m] [MonadError m]

def CrossRefConfig.parse : ArgParse m CrossRefConfig :=
  (fun (a : Verso.ArgParse.WithSyntax String) =>
    { source := a.val, sourceSyntax := a.syntax }) <$>
    .positional `source (.withSyntax .string)

instance : FromArgs CrossRefConfig m where
  fromArgs := CrossRefConfig.parse

end

/-- The last name component of a declaration, for display. -/
private def lastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- The dot-separated numeric components of a locus, for natural sorting:
`"§13.3.5"` ↦ `[13, 3, 5]`, `"1.12"` ↦ `[1, 12]`, `"§7"` ↦ `[7]`. Non-digit
characters (the `§` marker, dots, spaces) are separators. -/
private def numberKey (s : String) : List Nat := Id.run do
  let mut nums : List Nat := []
  let mut cur : Option Nat := none
  for c in s.toList do
    if c.isDigit then
      cur := some ((cur.getD 0) * 10 + (c.toNat - '0'.toNat))
    else
      match cur with
      | some n => nums := nums ++ [n]; cur := none
      | none => pure ()
  match cur with
  | some n => nums := nums ++ [n]
  | none => pure ()
  return nums

/-- Lexicographic order on `List Nat` (a shorter prefix sorts first, so `[7]`
precedes `[7, 5]`). -/
private def listNatLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else listNatLt as bs

/-- Natural numeric order on loci, falling back to string order when the numeric
keys are equal (e.g. two `§7` entries). -/
private def locusLt (a b : String) : Bool :=
  let ka := numberKey a
  let kb := numberKey b
  if ka == kb then a < b else listNatLt ka kb

private def crossrefsImpl : DirectiveExpanderOf CrossRefConfig
  | cfg, _contents => do
    let env ← getEnv
    let (refs, cite) :=
      if cfg.source == "vim4" then (vim4Refs env, vim4Source.cite)
      else if cfg.source == "dybkaer" then (dybkaerRefs env, dybkaerSource.cite)
      else (#[], "")
    if cfg.source ≠ "vim4" && cfg.source ≠ "dybkaer" then
      logErrorAt cfg.sourceSyntax
        m!"unknown cross-reference source '{cfg.source}'; expected 'dybkaer' or 'vim4'"
    let mut rows : Array CrossRefRow := #[]
    for r in refs do
      let labels ← Informal.Environment.labelsForLeanDecl r.decl
      let label := (labels[0]?.map (·.toString)).getD ""
      rows := rows.push
        { locus := r.locus, term := r.term, shortName := lastComponent r.decl,
          label := label, note := r.note }
    let sortedRows := rows.qsort (fun a b => locusLt a.locus b.locus)
    let tableData : CrossRefTableData := { sourceCite := cite, rows := sortedRows }
    ``(Lean.Doc.Block.other (PropertyKindCalculusBlueprint.Block.crossRefTable $(quote tableData)) #[])

@[directive]
def «crossrefs» : DirectiveExpanderOf CrossRefConfig
  | cfg, contents => crossrefsImpl cfg contents

end PropertyKindCalculusBlueprint
