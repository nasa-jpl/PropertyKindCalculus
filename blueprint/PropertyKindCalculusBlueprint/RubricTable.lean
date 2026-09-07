/-
# The `rubric_template` directive — an application template, rendered from the catalogue

`:::rubric_template model` and `:::rubric_template deployment` expand into the
template's rubrics as a table, read from `PropertyKindCalculus.Rubrics.catalogue`.
The chapters state the *case* for each group in prose; the table is the enumeration,
so a rubric added to the catalogue appears in the chapter without the chapter being
edited, and one removed cannot linger in it.

The `Requires` column is the rubric's evidence kind — what would count as addressing
it — which is the column a document's author reads first: it says whether the
obligation is discharged by a section, by a generated view, by a checked
declaration, or by a labeled measurement.
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
    [[ Cell.md s!"*{grp.label}*", .text "", .text "" ]] ++
    (t.rubrics.filter (·.group == grp)).map fun r =>
      [ Cell.code r.id, .text r.evidence.label, .md r.title ]
  { headers := ["", "Requires", "The rubric"], rows := rows }

@[directive]
def rubric_template : DirectiveExpanderOf Config
  | cfg, _contents => do
    docTableTerm (buildTable cfg.template)

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

end PropertyKindCalculusBlueprint.RubricTemplate
