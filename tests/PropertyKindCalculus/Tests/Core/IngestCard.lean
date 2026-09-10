/-
# Validation probes — `IngestCard` (the system card and the stage overview)

Both emitters are pure functions of the ingest/egress contract values, so their claims
are decidable by evaluation on a hand-built two-stage system. What the pins fix:

* **the division of labor between the two readings** — the system card carries slot
  *names* only (the kind rides the tooltip), the stage card puts the kind on the row
  and the admissibility evidence in the tooltip;
* **condition planes are first-class egress** — the declared condition slot renders in
  its own tint on both cards;
* **the refusals** — a condition name matching no egress slot, a coupling endpoint
  naming no stage, and a coupled plane that is not both an output of its source and an
  input of its destination each refuse with the offending name, never a silently wrong
  figure.
-/
import PropertyKindCalculus.IngestCard

namespace PropertyKindCalculus.Tests.IngestCard

open PropertyKindCalculus
open PropertyKindCalculus.IngestCard

/-- Does `sub` occur in `s`? Evaluation-only probe helper. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- An `Except` rendering for the pins: the diagram, or the refusal. -/
def okOrError : Except String String → String
  | .ok s => s
  | .error e => s!"ERROR: {e}"

def kIn : KindOfProperty := { id := "probe reading", scale := .ratio }
def kOut : KindOfProperty := { id := "probe estimate", scale := .ratio }
def kQ : KindOfProperty := { id := "probe residual", scale := .ratio }

def prepIn : IngestContract where
  interface := "probe.prep.input (2,H,W)"
  slots := [IngestContract.slot kIn "raw" "checked at the gate: finiteness" "raw reading",
            IngestContract.slot kIn "aux" "checked at the gate: [0,1]" "auxiliary plane"]

def prepOut : IngestContract where
  interface := "probe.prep.output (2,H,W)"
  slots := [IngestContract.slot kOut "est" "by construction" "prepared estimate",
            IngestContract.slot kQ "resid" "by construction" "residual plane"]

def mainIn : IngestContract where
  interface := "probe.main.input (2,H,W)"
  slots := [IngestContract.slot kOut "est" "checked at the gate: finiteness" "prepared estimate",
            IngestContract.slot kQ "resid" "adjudicated: QC-only" "residual plane"]

def mainOut : IngestContract where
  interface := "probe.main.output (1,H,W)"
  slots := [IngestContract.slot kOut "final" "by construction" "final estimate"]

def prep : StageSpec :=
  { id := "prep", title := "Stage P — the preparation"
    input := prepIn, output := prepOut, conditions := ["resid"]
    notes := ["two variants; the first is the default"] }

def main : StageSpec :=
  { id := "main", title := "Stage M — the main step"
    input := mainIn, output := mainOut }

def system : String :=
  okOrError (systemCard "probe system — end to end" [prep, main]
    [{ src := "prep", dst := "main", planes := ["est", "resid"] }])

def stagePage : String := okOrError (stageCard prep)

/-! ## The system card: names on the rows, kinds in tooltips, coupling labeled -/

#guard hasSub system "probe system — end to end"
#guard hasSub system "Stage P — the preparation"
#guard hasSub system "Stage M — the main step"
#guard hasSub system "takes — probe.prep.input (2,H,W)"
#guard hasSub system "yields — probe.prep.output (2,H,W)"
-- names only on the rows; the kind rides the tooltip
#guard hasSub system "{label: \"raw\";"
#guard !hasSub system "raw : probe reading"
#guard hasSub system "kind: probe reading"
-- the declared condition plane carries its tint and its tooltip on the system card too
#guard hasSub system "condition plane"
#guard hasSub system "#fef9c3"
-- the coupling arrow, labeled by the flowing planes
#guard hasSub system "\"prep\" -> \"main\": \"est · resid\""
-- the caller's note line renders inside its stage box
#guard hasSub system "two variants; the first is the default"

/-! ## The stage card: kinds on the rows, evidence in tooltips -/

#guard hasSub stagePage "stage overview — Stage P — the preparation"
#guard hasSub stagePage "raw : probe reading"
#guard hasSub stagePage "checked at the gate: finiteness"
#guard hasSub stagePage "resid : probe residual"
#guard hasSub stagePage "#fef9c3"
#guard hasSub stagePage "two variants; the first is the default"

/-! ## The refusals, each with the offending name -/

#guard okOrError (stageCard { prep with conditions := ["ghost"] })
  == "ERROR: stage 'prep' lists condition plane 'ghost', which names no slot of its \
      egress contract 'probe.prep.output (2,H,W)'"

#guard hasSub (okOrError (systemCard "t" [prep]
    [{ src := "prep", dst := "gone", planes := ["est"] }]))
  "names no stage 'gone'"

#guard hasSub (okOrError (systemCard "t" [prep, main]
    [{ src := "prep", dst := "main", planes := ["ghost"] }]))
  "carries 'ghost', which names no slot of 'probe.prep.output (2,H,W)'"

-- a plane the source yields but the destination does not take is refused from the
-- destination's side
#guard hasSub (okOrError (systemCard "t"
    [prep, { main with input := mainOut }]
    [{ src := "prep", dst := "main", planes := ["est"] }]))
  "carries 'est', which names no slot of 'probe.main.output (1,H,W)'"

end PropertyKindCalculus.Tests.IngestCard
