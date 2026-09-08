/-
# The `rubric_template` directive — an application template, rendered from the catalogue

`:::rubric_template model` and `:::rubric_template deployment` expand into the
template's rubrics as a table, read from `PropertyKindCalculus.Rubrics.catalogue`.
The chapters state the *case* for each group in prose; the table is the enumeration,
so a rubric added to the catalogue appears in the chapter without the chapter being
edited, and one removed cannot linger in it.

The `Requires` column is the rubric's evidence kind — what would count as addressing
it: a section, a generated view, a checked declaration, or a labeled measurement.
`The author's part` is the rubric's `obligation`, which is the column a document's
author reads first, because a title says what a conforming document *has* and gives
no instruction for building one.

`:::rubric_closure` renders the other axis — whether anything can check that the
author did it everywhere — as its own table, beside the prose that explains it. It is
separate from the template table because the two answer different questions and a
five-column table answers neither: the template table is read while writing a
document, the closure table while deciding what the template can and cannot promise.
-/

import VersoManual
import VersoBlueprint
import PropertyKindCalculus.Rubrics
import PropertyKindCalculusBlueprint.ItemIndex

open Lean Elab
open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open PropertyKindCalculus.Rubrics
open PropertyKindCalculusBlueprint.ItemIndex

namespace PropertyKindCalculusBlueprint.RubricTemplate

/-- The `rubric_template` directive takes the template's name positionally. -/
structure Config where
  /-- `model` or `deployment`. -/
  template : Template

section
variable [Monad m] [MonadError m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadFileMap m]

/-- Parse the template name, failing loudly on anything else — a mistyped name must
not silently render the other template. -/
def parseTemplate : ValDesc m Template := {
  description := "the template name, `model` or `deployment`"
  signature := .Ident ∪ .String
  get
    | .name x =>
      match x.getId.toString with
      | "model"      => pure .model
      | "deployment" => pure .deployment
      | other        => throwErrorAt x
          "unknown template '{other}'; expected `model` or `deployment`"
    | .str s =>
      match s.getString with
      | "model"      => pure .model
      | "deployment" => pure .deployment
      | other        => throwErrorAt s
          "unknown template '{other}'; expected `model` or `deployment`"
    | other => throwError "expected `model` or `deployment`, got {repr other}"
}

def Config.parse : ArgParse m Config :=
  Config.mk <$> .positional `template parseTemplate

instance : FromArgs Config m := ⟨Config.parse⟩
end

/-- The template as a `DocTable`: a header row per group, then one row per rubric. -/
def buildTable (t : Template) : DocTable :=
  let rows := t.groups.flatMap fun grp =>
    [[ Cell.md s!"*{grp.label}*", .text "", .text "", .text "" ]] ++
    (t.rubrics.filter (·.group == grp)).map fun r =>
      [ Cell.code r.id, .text r.evidence.label, .md r.title, .md r.obligation ]
  { headers := ["", "Requires", "The rubric", "The author's part"], rows := rows }

@[directive]
def rubric_template : DirectiveExpanderOf Config
  | cfg, _contents => do
    docTableTerm (buildTable cfg.template)

/-- The closure axis as a `DocTable`: what holds each rubric's population, or — for a
rubric nothing walks yet — the population a sweep would have to cover, which is the
sentence someone building that sweep starts from. A `prose` rubric's cell is an em dash
rather than an empty cell: there is nothing to build there, and a blank would read as an
omission. -/
def buildClosureTable (t : Template) : DocTable :=
  let rows := t.groups.flatMap fun grp =>
    [[ Cell.md s!"*{grp.label}*", .text "", .text "" ]] ++
    (t.rubrics.filter (·.group == grp)).map fun r =>
      [ Cell.code r.id, .text r.closure.tag,
        .md (if r.closure.detail.isEmpty then "—" else r.closure.detail) ]
  { headers := ["", "Closure", "What holds the population, or what a sweep would walk"],
    rows := rows }

@[directive]
def rubric_closure : DirectiveExpanderOf Config
  | cfg, _contents => do
    docTableTerm (buildClosureTable cfg.template)

/-- The count of rubrics in a template, *computed* — so a sentence in the chapter
that names the number cannot fall out of step with the catalogue. -/
def countSentence (t : Template) : String :=
  let n := t.rubrics.length
  let checked := (t.rubrics.filter (·.evidence == .checked)).length
  let generated := (t.rubrics.filter (·.evidence == .generated)).length
  let measured := (t.rubrics.filter (·.evidence == .measured)).length
  let exposition := (t.rubrics.filter (·.evidence == .exposition)).length
  s!"The template has {n} rubrics: {exposition} discharged by a section that states \
     the answer, {generated} by a view generated from the compiled environment, \
     {checked} by a kernel-checked declaration, and {measured} by a labeled \
     measurement."

@[directive]
def rubric_count : DirectiveExpanderOf Config
  | cfg, _contents => do
    cellBlock (.md (countSentence cfg.template))

/-- The closure profile of a template, *computed* — the sentence that says how much of
the template a machine can hold, and how much rests on the author having remembered.
Counted rather than written because it is the number most likely to change: building one
missing sweep moves a rubric out of `census possible`, and a sentence typed by hand would
go on reporting the old figure. -/
def closureSentence (t : Template) : String :=
  let n := t.rubrics.length
  let prose := (t.rubrics.filter (!·.closure.censusable)).length
  let held := (t.rubrics.filter (·.closure.held)).length
  let gated := (t.rubrics.filter
    (fun r => match r.closure with | .gate .. => true | _ => false)).length
  let pending := n - prose - held
  s!"Of the {n} rubrics, {prose} have no census and can have none — their population is \
     what the document says. Of the other {n - prose}, {held} are walked today ({gated} by \
     an audit that fails the build, the rest by a generated view or a pinned reading), and \
     {pending} have a population a sweep could enumerate and no sweep walking it: for those, \
     the template is reporting exemplars, and is only as complete as the author's memory."

@[directive]
def rubric_closure_count : DirectiveExpanderOf Config
  | cfg, _contents => do
    cellBlock (.md (closureSentence cfg.template))

end PropertyKindCalculusBlueprint.RubricTemplate
