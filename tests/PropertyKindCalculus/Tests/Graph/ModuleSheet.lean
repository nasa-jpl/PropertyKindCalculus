/-
# Validation probes — `ModuleSheet` (the module interface document as tables)

`sheetTablesOf` is a pure function of the same prepared values the D2 card renders, so
its claims are decidable by evaluation on the card test's own probe contract — one
producer of the probe, two surfaces checked against it.

What the guards fix is the **table contract**: which tables appear and in which order,
which columns a boundary earns (a `Supplied by` column only where a supplier clause
exists, a `Cases` column only where a conditional port does), and that every cell that
names a declaration carries its `Lean.Name` for the rendering document to link — the
kind as a `declText`, the configuration port linked to the constant that binds it, the
witness and hypotheses as declaration references.
-/

module

public import PropertyKindCalculus.Graph.ModuleSheet
meta import PropertyKindCalculus.Graph.ModuleSheet
public import PropertyKindCalculus.Tests.Core.ModuleCard
meta import PropertyKindCalculus.Tests.Core.ModuleCard

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.ModuleSheet

open PropertyKindCalculus
open PropertyKindCalculus.Index (IndexCell IndexTable)
open PropertyKindCalculus.Provenance (NodeId)
open PropertyKindCalculus.ModuleSheet
open PropertyKindCalculus.Tests.ModuleCard (probeBoundary)

/-- The probe's tables: one prepared edge row (with the declaration names a table can
link), one prepared cluster row (with its kind references), one documented member. -/
def tables : Array IndexTable :=
  sheetTablesOf probeBoundary
    (rels := [{ claim := "inverts 'probe partner'", witness := "Probe.inv_correct",
                other := `Probe.partner, witnessName := `Probe.inv_correct,
                hypothesisNames := [`Probe.hyp] }])
    (cls := [{ representative := "kz", kinds := ["kx", "kz"],
               refs := [.decl `kx, .decl `kz] }])
    (memberDocs := [(`Probe.A.fwd, "The probe **forward**.")])

/-- The table with the given id, or the empty default (whose id then fails the guard). -/
def tbl (id : String) : IndexTable :=
  (tables.find? (·.id == id)).getD default

/-! ## Which tables, in which order -/

#guard tables.map (·.id) == #["sheet-members", "sheet-inputs", "sheet-parameters",
  "sheet-configuration", "sheet-outputs", "sheet-edges", "sheet-clusters"]

/-! ## The members: linked declaration, docstring kept as markdown -/

#guard (tbl "sheet-members").rows ==
  #[#[.decl `Probe.A.fwd "fwd", .prose "The probe **forward**."]]

/-! ## The interface groups: the card's display rule, the earned columns -/

-- Inputs and parameters earn no extra column on this probe (no supplier clause).
#guard (tbl "sheet-inputs").headers == #["Port", "Kind"]
#guard (tbl "sheet-parameters").headers == #["Port", "Kind"]
-- The kind cell links its rendering to the kind declaration.
#guard (tbl "sheet-inputs").rows.all fun r => r[1]! == .declText `kx "kx"

-- A configuration port links to the constant that binds it; the colliding pair
-- displays the full address while the unique read stays short — `portDisplay`,
-- the same rule the card renders.
#guard (tbl "sheet-configuration").rows ==
  #[#[.declText `Probe.One.dup "Probe.One.dup.q", .declText `kx "kx"],
    #[.declText `Probe.Two.dup "Probe.Two.dup.q", .declText `kx "kx"],
    #[.declText `Probe.table "table.lo", .declText `kx "kx"]]

-- The outputs earn `Cases` (a conditional port exists) and `Aggregation` (a class is
-- declared); the exit port carries the card's mark, and the title explains it.
#guard (tbl "sheet-outputs").headers == #["Port", "Kind", "Cases", "Aggregation"]
#guard ((tbl "sheet-outputs").title.splitOn "⊗ leaves the calculus").length > 1
#guard (tbl "sheet-outputs").rows.any fun r => match r[0]! with
  | .code s => s.endsWith " ⊗"
  | _ => false
-- The conditional port names its decider as a link; the plain output stays blank.
#guard (tbl "sheet-outputs").rows.any fun r =>
  r[2]! == .declText `Probe.decider "decided by decider"
-- The `intensive` class names no evidence declaration, so it renders as text.
#guard (tbl "sheet-outputs").rows.any fun r => r[3]! == .text "intensive"

/-! ## A supplier clause earns the `Supplied by` column -/

#guard ((sheetTablesOf { probeBoundary with
    suppliers := [((NodeId.binder "gain").within `Probe.A.fwd, `Probe.Supplier.mod)] }
    [] [] []).find? (·.id == "sheet-parameters") |>.getD default).headers
  == #["Port", "Kind", "Supplied by"]

/-! ## The theorem edges: every name a link, columns as the survey needs them -/

-- No tolerance on the probe edge, so no `Tolerance` column; one hypothesis, so `Under`.
#guard (tbl "sheet-edges").headers == #["Claim", "Witness", "Under"]
#guard (tbl "sheet-edges").rows ==
  #[#[.declText `Probe.partner "inverts 'probe partner'",
      .decl `Probe.inv_correct "inv_correct",
      .links #[(`Probe.hyp, "hyp")]]]

/-! ## The clusters: each kind linked through its reference -/

#guard (tbl "sheet-clusters").rows ==
  #[#[.code "kz", .links #[(`kx, "kx"), (`kz, "kz")]]]

end PropertyKindCalculus.Tests.ModuleSheet

end -- pkc-blanket-expose
end -- pkc-blanket
