/-
# The `traceability` directive — the requirement-traceability matrix, generated

`{traceability}` expands into the requirement-traceability matrix built from the
typed `@[requirement …]` annotations harvested by `PropertyKindCalculus.Requirements`.
For each requirement in the catalogue (R1 … R27) it lists every declaration that
*specifies*, *proves*, *implements*, or *exemplifies* it, linked to that
declaration's blueprint node.

Like the `iso_doc_table` and `crossrefs` directives, the annotations are
decl-indexed environment metadata read at elaboration time; each declaration is
resolved to its blueprint node label via `Informal.Environment.labelsForLeanDecl`,
and the node's href is resolved at render time. The matrix is assembled as an
`ItemIndex.DocTable` and rendered by the shared `ItemIndex.docTableTerm`, so all of
the existing table/link machinery is reused — a renamed declaration is a build
error, so the matrix can never drift from the Lean source.
-/

import VersoManual
import VersoBlueprint
import VersoBlueprint.Environment
import VersoBlueprint.TraversalIndex
import PropertyKindCalculus.Requirements
import PropertyKindCalculusBlueprint.ItemIndex

open Lean Elab
open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open PropertyKindCalculus.Requirements
open PropertyKindCalculusBlueprint.ItemIndex

namespace PropertyKindCalculusBlueprint.Traceability

/-- The last name component of a declaration, for display. -/
private def lastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- The `traceability` directive takes no arguments. -/
structure Config where
  deriving Inhabited

section
variable [Monad m] [MonadError m]

def Config.parse : ArgParse m Config := pure {}

instance : FromArgs Config m := ⟨Config.parse⟩
end

/-- Build the traceability matrix as a `DocTable`, resolving each annotated
declaration to its blueprint node label. Rows are organized by **requirement
group** (each introduced by a header row), then by requirement (in catalogue
order), and within a requirement ordered specification → proof → implementation →
example. A requirement with no annotation yet still gets a row, so the matrix
always shows the whole catalogue. -/
def buildTable : DocElabM DocTable := do
  let env ← getEnv
  let refs := requirementRefs env
  let mut rows : List (List Cell) := []
  for grp in requirementGroups do
    -- A group-header row: the group label in the first column, the rest blank.
    rows := rows ++ [[ .md s!"*{grp.label}*", .text "", .text "", .text "", .text "" ]]
    for req in catalogue.filter (·.group == grp) do
      let status := requirementStatus env req.id
      let these := (refs.filter (·.req == req.id)).qsort
        (fun a b => a.role.order < b.role.order)
      -- A discharged requirement links its status to the evidence that discharges
      -- it — proofs for a verifiable requirement, the typechecking constructions
      -- for an expressiveness one — rather than printing the bare word.
      let mut dischargeLinks : List (String × String) := []
      for r in these.filter (·.role == req.kind.dischargeRole) do
        let labels ← Informal.Environment.labelsForLeanDecl r.decl
        let label := (labels[0]?.map (·.toString)).getD ""
        dischargeLinks := dischargeLinks ++ [(label, lastComponent r.decl)]
      let statusOf (first : Bool) : Cell :=
        if !first then .text ""
        else if status == "proved" || status == "demonstrated" then .links dischargeLinks
        else .text status
      if these.isEmpty then
        rows := rows ++ [[ .md s!"*{req.id}* — {req.title}", .text status,
                           .text "—", .text "—", .text "" ]]
      else
        let mut first := true
        for r in these do
          let labels ← Informal.Environment.labelsForLeanDecl r.decl
          let label := (labels[0]?.map (·.toString)).getD ""
          let declCell : Cell :=
            if label.isEmpty then .code (lastComponent r.decl)
            else .ref label (lastComponent r.decl)
          let reqCell : Cell := if first then .md s!"*{req.id}* — {req.title}" else .text ""
          -- The note is author-written prose and names Lean constants in it, so it is markdown for
          -- the same reason a docstring is. As `text` its backticks reach the page.
          rows := rows ++ [[ reqCell, statusOf first, .text r.role.label, declCell, .md r.note ]]
          first := false
  return { headers := ["Requirement", "Status", "Role", "This work", "Note"], rows := rows }

@[directive]
def traceability : DirectiveExpanderOf Config
  | _cfg, _contents => do
    let tbl ← buildTable
    docTableTerm tbl

/-- The headline claim, *computed* from the catalogue's kinds and the harvested
annotations: how many verifiable requirements are proved and how many
expressiveness requirements are demonstrated. Because it is derived, the sentence
can never overstate the evidence. -/
def summarySentence (t : RequirementTally) : String :=
  if t.verifiableProved == t.verifiableTotal
      && t.expressivenessDemonstrated == t.expressivenessTotal then
    s!"PropertyKindCalculus *proves all {t.verifiableTotal} verifiable requirements* \
       and *demonstrates all {t.expressivenessTotal} expressiveness requirements* — \
       the capabilities a type system affords by construction rather than by \
       theorem."
  else
    s!"Of the {t.verifiableTotal} verifiable requirements, {t.verifiableProved} are \
       proved; of the {t.expressivenessTotal} expressiveness requirements, \
       {t.expressivenessDemonstrated} are demonstrated."

@[directive]
def traceability_summary : DirectiveExpanderOf Config
  | _cfg, _contents => do
    let t := requirementTally (← getEnv)
    ItemIndex.cellBlock (.md (summarySentence t))

end PropertyKindCalculusBlueprint.Traceability
