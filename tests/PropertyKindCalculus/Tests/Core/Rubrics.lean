/-
# Validation probes — the application-template conformance layer

`Rubrics` computes a document's conformance status from the sites it declares. Every
failure mode of such a layer is silent: a scope filter that matches nothing reports a
conforming document as `unaddressed` across the board, and a channel requirement that is
never enforced reports a hand-maintained table as a generated one. Neither shows up as an
error — both show up as a *plausible* matrix.

So this probe authors a small closed world — one declaration site per evidence kind, one
section-only site, and one rubric left untouched — and pins the derived status of each.
The pins are what turn "the status came back reasonable" into a build failure.

Two of the traps are the reason the layer is shaped the way it is:

  * a rubric requires **both** channels in both directions. A section site alone is what a
    hand-transcribed table also has (`M23` below); a declaration site alone is a theorem no
    chapter cites (`M26` below). Both must read `partial`, and an earlier version of this
    layer reported the second as `proved`;
  * the attribute harvest is environment-wide, so a document that imports another's
    annotations would count them as its own. The out-of-scope pin fixes that `declScope`
    actually excludes.
-/
import PropertyKindCalculus.Rubrics

namespace PropertyKindCalculus.Tests.Rubrics

open Lean Elab Command
open PropertyKindCalculus.Rubrics

/-! ## A closed world to score -/

/-- Stands in for a theorem edge carrying a module's measurement model (M12, `checked`). -/
theorem probeEdge : 1 + 1 = 2 := rfl

/-- Stands in for the generator of a module specification sheet (M16, `generated`). -/
def probeCardGenerator : Nat := 0

/-- Stands in for a recorded measurement (M26, `measured`). -/
def probeSweepRecord : Nat := 1

attribute [rubric "M12" "the probe's measurement-model edge"] probeEdge
attribute [rubric "M16" "the probe's card generator"] probeCardGenerator
attribute [rubric "M26" "the probe's recorded sweep"] probeSweepRecord

/-- The probe document's declared conformance. `M3` is section-only and `exposition`, so it
is discharged. `M23` is section-only and `generated`, and `M26` is declaration-only and
`measured`; neither is. -/
def probeConformance : Conformance where
  template := .model
  declScope := some `PropertyKindCalculus.Tests.Rubrics
  sections :=
    [ { rubric := "M3",  tag := "probe-premise", note := "cites the blueprint" }
    , { rubric := "M12", tag := "probe-modules", note := "where the edge is cited" }
    , { rubric := "M16", tag := "probe-cards",   note := "where the sheets appear" }
    , { rubric := "M23", tag := "probe-status",  note := "section only — no generator" } ]

/-- The same document read with a scope that matches none of its annotations: the case a
mistyped namespace produces, which must lose every declaration site rather than silently
keeping them. -/
def probeMisscoped : Conformance :=
  { probeConformance with declScope := some `PropertyKindCalculus.Tests.NoSuchDocument }

/-- One line per rubric of interest: its id and derived status. -/
def report (c : Conformance) (env : Environment) (ids : List String) : String :=
  String.intercalate ", " <| ids.filterMap fun id =>
    (rubricById? id).map fun r => s!"{id}={c.status env r}"

/-! ## The pins -/

/-- info: M3=stated, M12=proved, M16=generated, M26=partial, M23=partial, M1=unaddressed -/
#guard_msgs in
#eval show CommandElabM Unit from do
  logInfo (report probeConformance (← getEnv) ["M3", "M12", "M16", "M26", "M23", "M1"])

/-- info: M3=stated, M12=partial, M16=partial, M26=unaddressed -/
#guard_msgs in
#eval show CommandElabM Unit from do
  logInfo (report probeMisscoped (← getEnv) ["M3", "M12", "M16", "M26"])

/-- info: total=26 addressed=3 partial=2 unaddressed=21 -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let t := probeConformance.tally (← getEnv)
  logInfo s!"total={t.total} addressed={t.addressed} partial={t.incomplete} \
             unaddressed={t.unaddressed}"

/-! An id outside the catalogue is refused where it is written, not where it is read: a
conformance matrix cannot report a rubric that does not exist, so the only way such a site
could survive is by being silently dropped. -/

/--
error: unknown rubric 'M99'; it is not in `PropertyKindCalculus.Rubrics.catalogue`
-/
#guard_msgs in
attribute [rubric "M99"] probeEdge

end PropertyKindCalculus.Tests.Rubrics
