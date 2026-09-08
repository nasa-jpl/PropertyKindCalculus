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
    actually excludes;
  * a site is never a claim about the rest. A rubric whose closure names audits (`M9`
    below) must read `partial` until **every** named audit has left a receipt over a scope
    covering the document's — a run over some other namespace is not coverage, and one
    of two gates is not both.
-/
import PropertyKindCalculus.Rubrics
import PropertyKindCalculus.BoundaryAudit

namespace PropertyKindCalculus.Tests.Rubrics

open Lean Elab Command
open PropertyKindCalculus.Rubrics

/-! ## A closed world to score -/

/-- Stands in for a named refinement bridge between two carriers (M17, `checked`,
site-discharged: its census is not yet written, so a site is what discharges it). -/
theorem probeEdge : 1 + 1 = 2 := rfl

/-- Stands in for the generator of a module specification sheet (M16, `generated`). -/
def probeCardGenerator : Nat := 0

/-- Stands in for a recorded measurement (M26, `measured`). -/
def probeSweepRecord : Nat := 1

/-- Stands in for an authored crossing (M9, `checked`, gated by two audits). -/
theorem probeCrossing : 2 + 2 = 4 := rfl

attribute [rubric "M17" "the probe's carrier bridge"] probeEdge
attribute [rubric "M16" "the probe's card generator"] probeCardGenerator
attribute [rubric "M26" "the probe's recorded sweep"] probeSweepRecord
attribute [rubric "M9" "the probe's authored crossing"] probeCrossing

/-- The probe document's declared conformance. `M3` is section-only and `exposition`, so it
is discharged. `M23` is section-only and `generated`, and `M26` is declaration-only and
`measured`; neither is. -/
def probeConformance : Conformance where
  template := .model
  declScope := some `PropertyKindCalculus.Tests.Rubrics
  sections :=
    [ { rubric := "M3",  tag := "probe-premise", note := "cites the blueprint" }
    , { rubric := "M17", tag := "probe-bridges", note := "where the bridge is named" }
    , { rubric := "M16", tag := "probe-cards",   note := "where the sheets appear" }
    , { rubric := "M23", tag := "probe-status",  note := "section only — no generator" }
    , { rubric := "M9",  tag := "probe-crossings", note := "both sites, gates not yet run" } ]

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

/-- info: M3=stated, M17=proved, M16=generated, M26=partial, M23=partial, M1=unaddressed -/
#guard_msgs in
#eval show CommandElabM Unit from do
  logInfo (report probeConformance (← getEnv) ["M3", "M17", "M16", "M26", "M23", "M1"])

/-- info: M3=stated, M17=partial, M16=partial, M26=unaddressed -/
#guard_msgs in
#eval show CommandElabM Unit from do
  logInfo (report probeMisscoped (← getEnv) ["M3", "M17", "M16", "M26"])

/-- info: total=26 addressed=3 partial=3 unaddressed=20 -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let t := probeConformance.tally (← getEnv)
  logInfo s!"total={t.total} addressed={t.addressed} partial={t.incomplete} \
             unaddressed={t.unaddressed}"

/-! ## Receipts — a gated rubric is green only when its gates ran over the document's scope

`M9` has both sites from the start and its closure names two audits. Nothing the document
declares can move it: only the audits' own receipts, and only over a covering scope. -/

/-- The audits still missing for one rubric. -/
def missing (c : Conformance) (env : Environment) (id : String) : String :=
  match rubricById? id with
  | some r => s!"{id} missing: {String.intercalate ", " (c.missingAudits env r)}"
  | none   => s!"{id}: no such rubric"

/-- info: M9=partial; M9 missing: kind_boundary_clean, kind_mint_ratchet -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let env ← getEnv
  logInfo s!"{report probeConformance env ["M9"]}; {missing probeConformance env "M9"}"

-- Both gates over a namespace that does not cover the document's scope: not coverage.
#guard_msgs in
#kind_boundary_clean PropertyKindCalculus.Tests.Elsewhere
#guard_msgs in
#kind_mint_ratchet PropertyKindCalculus.Tests.Elsewhere

/-- info: M9=partial; M9 missing: kind_boundary_clean, kind_mint_ratchet -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let env ← getEnv
  logInfo s!"{report probeConformance env ["M9"]}; {missing probeConformance env "M9"}"

-- One of the two gates over the covering scope: still partial, and the report says which.
#guard_msgs in
#kind_boundary_clean PropertyKindCalculus.Tests.Rubrics

/-- info: M9=partial; M9 missing: kind_mint_ratchet -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let env ← getEnv
  logInfo s!"{report probeConformance env ["M9"]}; {missing probeConformance env "M9"}"

-- The second gate: now both receipts cover the scope, and only now is the rubric green.
#guard_msgs in
#kind_mint_ratchet PropertyKindCalculus.Tests.Rubrics

/-- info: M9=proved; M9 missing:  -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let env ← getEnv
  logInfo s!"{report probeConformance env ["M9"]}; {missing probeConformance env "M9"}"

/-- info: total=26 addressed=4 partial=2 unaddressed=20 -/
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
