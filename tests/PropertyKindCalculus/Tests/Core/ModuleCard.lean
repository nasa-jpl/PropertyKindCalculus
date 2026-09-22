/-
# Validation probes — `ModuleCard` (the module interface document and its overview)

Both emitters are pure functions of the contract value, so their claims are decidable by
evaluation on a hand-built contract exercising every interface branch: a shortAddr collision
(two binders sharing a short form, forcing the long display), an exit mark, a decider
tooltip on a conditional port, and every port role.

What the pins fix is the **division of labor between the two cards**. The full sheet shows
all four role groups, the clause panel, and the theorem-edge rows it is handed. The overview
shows the per-datum inputs and the produced outputs *only* — its point is a landscape page a
reader takes in whole — with the parameters, configuration, clauses, edges and clusters
reduced to one strip of tally chips deferring to the sheet. A parameters *group* appearing
on the overview, or a tally chip going missing, is exactly the drift these guards refuse.
The two render ports through one `portGroup`, so a port cannot read differently on the
sheet and the overview — the collision and decider guards hold on both.
-/

module

public import PropertyKindCalculus.ModuleCard
meta import PropertyKindCalculus.ModuleCard

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.ModuleCard

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (Contract Port PortDir NodeId KindRef)
open PropertyKindCalculus.ModuleCard

/-- Does `sub` occur in `s`? Evaluation-only probe helper. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The probe module: one member, one parameter, three configuration reads — two of which
collide at the short form (`Probe.One.dup.q` and `Probe.Two.dup.q` both shorten to
`dup.q`, forcing the full address as the display) while the third (`Probe.table.lo`)
stays short with its full address as the tooltip — an output that is also an exit, and a
conditional output with a named decider. -/
def probeBoundary : Contract NodeId KindRef where
  name := "probe module"
  members := [`Probe.A.fwd]
  ports := [⟨(NodeId.binder "x").within `Probe.A.fwd, .decl `kx, .input⟩,
            ⟨(NodeId.binder "gain").within `Probe.A.fwd, .decl `kg, .param⟩,
            ⟨(NodeId.config `Probe.One.dup).field "q", .decl `kx, .config⟩,
            ⟨(NodeId.config `Probe.Two.dup).field "q", .decl `kx, .config⟩,
            ⟨(NodeId.config `Probe.table).field "lo", .decl `kx, .config⟩,
            ⟨NodeId.result.within `Probe.A.fwd, .decl `kz, .output⟩,
            ⟨(NodeId.letBound "cond").within `Probe.A.fwd, .decl `kz, .conditional⟩]
  exits := [NodeId.result.within `Probe.A.fwd]
  deciders := [((NodeId.letBound "cond").within `Probe.A.fwd, `Probe.decider)]
  aggregations := [(NodeId.result.within `Probe.A.fwd, .intensive)]

/-- The full sheet, with one prepared theorem-edge row. -/
def sheet : String :=
  moduleCard probeBoundary
    (relations := [{ claim := "inverts 'probe partner'", witness := "Probe.inv_correct" }])

/-- The overview, with the counts the sheet carries in full and a caller note. -/
def overview : String :=
  moduleOverviewCard probeBoundary (relationCount := 1) (clusterCount := 2)
    (notes := ["two variants bind the module port; the first is the default"])

/-! ## The full sheet: every role group, the clauses, the edge row -/

#guard hasSub sheet "\"inputs\""
#guard hasSub sheet "\"parameters\""
#guard hasSub sheet "\"configuration\""
#guard hasSub sheet "\"outputs\""
#guard hasSub sheet "inverts 'probe partner'"
#guard hasSub sheet "witness: Probe.inv_correct"
#guard hasSub sheet "intensive"

/-! ## The overview: inputs and outputs only, the rest as tally chips -/

#guard hasSub overview "module overview — probe module"
#guard hasSub overview "\"inputs\""
#guard hasSub overview "\"outputs\""
-- No parameters or configuration *group* — those roles appear only as chips.
#guard !hasSub overview "\"parameters\""
#guard !hasSub overview "\"configuration\""
#guard hasSub overview "1 parameter(s)"
#guard hasSub overview "3 configuration binding(s)"
#guard hasSub overview "2 declared clause(s)"   -- one aggregation + one exit
#guard hasSub overview "1 theorem edge(s)"
#guard hasSub overview "2 inter-derivable cluster(s)"
#guard hasSub overview "on the full sheet"
#guard hasSub overview "two variants bind the module port; the first is the default"
-- The edge row itself stays off the overview: only its tally crosses.
#guard !hasSub overview "inverts"

/-! ## One `portGroup`, both cards -/

-- A port label reads identically on the sheet and the overview …
#guard hasSub sheet "\"fwd/x : kx\""
#guard hasSub overview "\"fwd/x : kx\""
-- … the exit port carries its mark on both …
#guard hasSub sheet " ⊗"
#guard hasSub overview " ⊗"
-- … and the conditional port names its decider in the tooltip on both.
#guard hasSub sheet "decided by Probe.decider"
#guard hasSub overview "decided by Probe.decider"

/-! ## The short-address discipline (sheet only — the ports live in its config group) -/

-- The colliding pair displays the full address …
#guard hasSub sheet "\"Probe.One.dup.q : kx\""
#guard hasSub sheet "\"Probe.Two.dup.q : kx\""
-- … the unique read stays short, its full address in the tooltip.
#guard hasSub sheet "\"table.lo : kx\""
#guard hasSub sheet "tooltip: \"Probe.table.lo\""

end PropertyKindCalculus.Tests.ModuleCard

end -- pkc-blanket-expose
end -- pkc-blanket
