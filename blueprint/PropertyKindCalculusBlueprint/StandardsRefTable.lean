/-
# The `standards_ref_table` directive — declarations beside their standards terms

`:::standards_ref_table rows` renders a list of `StandardsRow`s as one table: this work's
declaration, then its locus in Dybkær, ISO 80000-1 and the two VIM editions, side by side.

A row names its declaration as a `Name`, and the directive refuses to elaborate when that
name is not a declaration of the environment, so the table cannot cite a definition that
was renamed or removed. The declaration is linked through its blueprint node, as every
other generated table does (`ItemIndex.declCell`).
-/

import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.ItemIndex

open Lean Elab Term
open Verso Doc Elab
open Verso.ArgParse

namespace PropertyKindCalculusBlueprint.StandardsRef

open PropertyKindCalculusBlueprint.ItemIndex

/-- One row: a declaration and its locus in each source. A locus is a small markdown
string; `"—"` records that the source has no corresponding term. -/
structure StandardsRow where
  decl : Name
  /-- How the declaration is printed; its last name components by default. -/
  display : String
  dybkaer : String
  iso : String
  vim3 : String
  vim4 : String

unsafe def evalRowsUnsafe (stx : Syntax) : TermElabM (List StandardsRow) := do
  let ty ← Term.elabType
    (← `(List PropertyKindCalculusBlueprint.StandardsRef.StandardsRow))
  Term.evalTerm (List StandardsRow) ty stx

@[implemented_by evalRowsUnsafe]
opaque evalRows (stx : Syntax) : TermElabM (List StandardsRow)

def headers : List String :=
  ["This work", "Dybkær (2009)", "ISO 80000-1:2009", "VIM 3 (JCGM 200:2012)", "VIM 4 2CD"]

structure Config where
  /-- The name of the `List StandardsRow` constant to render. -/
  rows : Ident

section
variable [Monad m] [MonadError m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadFileMap m]

def Config.parse : ArgParse m Config :=
  Config.mk <$> .positional `rows ValDesc.ident

instance : FromArgs Config m := ⟨Config.parse⟩
end

/-- `:::standards_ref_table rows` renders the `List StandardsRow` constant `rows`.
Contents are ignored. -/
@[directive]
def standards_ref_table : DirectiveExpanderOf Config
  | cfg, _contents => do
    let rows ← evalRows cfg.rows
    let env ← getEnv
    let mut cells : List (List Cell) := []
    for r in rows do
      unless env.contains r.decl do
        throwErrorAt cfg.rows m!"standards_ref_table: '{r.decl}' is not a declaration"
      let d ← declCell r.decl r.display
      cells := cells ++ [[d, .md r.dybkaer, .md r.iso, .md r.vim3, .md r.vim4]]
    docTableTerm { headers := headers, rows := cells }

end PropertyKindCalculusBlueprint.StandardsRef
