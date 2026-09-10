/-
# IngestCard — system and stage overview cards over declared ingest contracts

A deployed model's outermost interfaces are its `IngestContract`s — the packed planes a
stage reads and writes, each slot carrying its kind, its admissibility evidence, and its
unit note. The module cards (`ModuleCard`) render the *declared boundaries* inside a
stage; what they cannot render is the mission-level reading — what the system as a whole
takes and yields, stage by stage, with the planes that couple one stage to the next. That
reading already exists as data (the ingest/egress contract values), so it is rendered
from them here rather than drawn beside them.

Two emitters, both sized for a landscape page:

* `systemCard` — the whole system at first contact: one box per stage showing the packed
  planes it takes and yields (names only, kinds in tooltips), condition planes tinted as
  first-class egress, one labeled arrow per declared coupling.
* `stageCard` — one stage, one page: the same two plane groups with the kinds on the
  rows and the admissibility evidence in tooltips, under the caller's checked note lines
  (a variant tally, a problem statement read off the contracts).

Both are checked renders, `Except` like `KindGraph.d2ClusterGrouped`: a condition name
that matches no egress slot, a coupling endpoint that names no stage, or a coupled plane
that is not both an output of its source and an input of its destination is a named
refusal, never a silently wrong figure.

The output is D2 text (https://d2lang.com), grid-laid like the module cards, in the same
palette, so a plane reads the same on the system card and on the sheet of the boundary
that computes it.
-/
import PropertyKindCalculus.KindGraphD2
import PropertyKindCalculus.CertifiedIngest

namespace PropertyKindCalculus.IngestCard

open PropertyKindCalculus (IngestContract IngestSlot)
open PropertyKindCalculus.Provenance (PortDir)
open PropertyKindCalculus.KindGraphD2 (q boxStyle portFill portStroke)

/-- One stage of the system: its identifier (the D2 node a coupling names), its display
title, its declared ingest and egress contracts, the egress slot names to draw as
condition planes, and the caller's checked note lines. -/
structure StageSpec where
  /-- The D2 identifier a coupling names. -/
  id : String
  /-- The stage's display title. -/
  title : String
  /-- The declared ingest contract — the packed planes the stage takes. -/
  input : IngestContract
  /-- The declared egress contract — the packed planes the stage yields. -/
  output : IngestContract
  /-- Egress slot names drawn as condition planes — quality and diagnostic egress,
  first-class rather than an afterthought. Each must name a slot of `output`. -/
  conditions : List String := []
  /-- Checked note lines (a variant tally, a problem statement) — derived by the caller
  from the contracts and the relation survey, never free prose. -/
  notes : List String := []

/-- One declared coupling: the planes that flow from one stage's egress into another's
ingress, by slot name. Each named plane must be an output slot of `src` and an input
slot of `dst`. -/
structure Coupling where
  /-- The source stage's `StageSpec.id`. -/
  src : String
  /-- The destination stage's `StageSpec.id`. -/
  dst : String
  /-- The flowing planes, by slot name. -/
  planes : List String

private def conditionFill : String := "#fef9c3"
private def conditionStroke : String := "#ca8a04"

/-- Validate a stage's condition names against its egress slots. -/
private def checkConditions (s : StageSpec) : Except String Unit := do
  for c in s.conditions do
    unless s.output.slots.any (·.name == c) do
      throw s!"stage '{s.id}' lists condition plane '{c}', which names no slot of its \
        egress contract '{s.output.interface}'"

/-- One plane row: the slot name (`stageCard` adds the kind), the role palette, the
condition tint where the caller declared one, and the slot's own evidence as tooltip. -/
private def slotRow (dir : PortDir) (conditions : List String) (withKind : Bool)
    (idx : Nat) (s : IngestSlot) : String :=
  let isCond := conditions.contains s.name
  let label := if withKind then s!"{s.name} : {s.kindId}" else s.name
  let fill := if isCond then conditionFill else portFill dir
  let stroke := if isCond then conditionStroke else portStroke dir
  let tipParts := (if isCond then ["condition plane"] else [])
    ++ (if withKind then [] else [s!"kind: {s.kindId}"])
    ++ (if s.unitNote.isEmpty then [] else [s.unitNote])
    ++ (if withKind && !s.admissibility.isEmpty then [s.admissibility] else [])
  let tip := String.intercalate " — " tipParts
  s!"      {q s!"p{idx}"}: \{label: {q label}; "
    ++ (if tip.isEmpty then "" else s!"tooltip: {q tip}; ")
    ++ s!"style: \{fill: {q fill}; stroke: {q stroke}; \
      border-radius: 6; font-size: 13; bold: false}}\n"

/-- One plane group — a short caption (`takes` / `yields`), the packed interface string
as its own sized text row (a long caption would overflow the container; a row widens
it), then one row per slot in declared (channel) order. -/
private def planeGroup (key : String) (dir : PortDir) (conditions : List String)
    (withKind : Bool) (c : IngestContract) : String := Id.run do
  let mut out := s!"    {q key}: \{\n      label: {q key}\n"
  out := out ++ "      grid-columns: 1\n      grid-gap: 4\n"
  out := out ++ "      style: {stroke: \"#e5e7eb\"; fill: \"#ffffff\"; border-radius: 8; font-size: 13; bold: true}\n"
  -- a borderless box rather than a text shape: grid-laid text shapes clip at their
  -- tails, a box always sizes to its label
  out := out ++ s!"      \"__iface\": \{label: {q c.interface}; style: \{\
    fill: \"#ffffff\"; stroke: \"#ffffff\"; font-size: 12; \
    font-color: \"#6b7280\"; bold: false}}\n"
  let mut i := 0
  for s in c.slots do
    out := out ++ slotRow dir conditions withKind i s
    i := i + 1
  out := out ++ "    }\n"
  return out

/-- One stage box: the given label (the stage's title on the system card, empty on the
stage page whose title node already carries it), the caller's note lines, and the
takes / yields plane groups side by side. `withKind` selects the system reading (names
only, kinds in tooltips) or the stage reading (kinds on the rows, evidence in
tooltips). -/
private def stageBox (s : StageSpec) (withKind : Bool) (boxLabel : String) :
    String := Id.run do
  let mut out := s!"{q s.id}: \{\n  label: {q boxLabel}\n"
  out := out ++ "  grid-columns: 1\n  grid-gap: 8\n"
  out := out ++ "  style: {stroke: \"#d1d5db\"; fill: \"#fafafa\"; border-radius: 10; font-size: 16; bold: true}\n"
  if !s.notes.isEmpty then
    out := out ++ "  \"__notes\": {\n    label: \"\"\n    grid-columns: 1\n    grid-gap: 4\n"
    out := out ++ boxStyle ++ "\n"
    let mut ni := 0
    for n in s.notes do
      out := out ++ s!"    {q s!"n{ni}"}: \{label: {q n}; shape: text; \
        style: \{font-size: 13; font-color: \"#374151\"}}\n"
      ni := ni + 1
    out := out ++ "  }\n"
  out := out ++ "  \"__planes\": {\n    label: \"\"\n    grid-columns: 2\n    grid-gap: 8\n"
  out := out ++ boxStyle ++ "\n"
  out := out ++ planeGroup "takes" .input [] withKind s.input
  out := out ++ planeGroup "yields" .output s.conditions withKind s.output
  out := out ++ "  }\n"
  out := out ++ "}\n"
  return out

/-- **The system card** — every stage side by side, couplings as labeled arrows. Sized
for one landscape page: plane rows carry names only (kind and unit ride the tooltip),
and parameters and configuration do not appear at all — they are the stage boundaries'
business, deferred to the module sheets. Refuses a condition name matching no egress
slot, a coupling endpoint naming no stage, and a coupled plane that is not both an
output of its source and an input of its destination. -/
def systemCard (title : String) (stages : List StageSpec)
    (couplings : List Coupling := []) : Except String String := do
  for s in stages do checkConditions s
  for c in couplings do
    let some src := stages.find? (·.id == c.src)
      | throw s!"coupling '{c.src} → {c.dst}' names no stage '{c.src}'"
    let some dst := stages.find? (·.id == c.dst)
      | throw s!"coupling '{c.src} → {c.dst}' names no stage '{c.dst}'"
    for p in c.planes do
      unless src.output.slots.any (·.name == p) do
        throw s!"coupling '{c.src} → {c.dst}' carries '{p}', which names no slot of \
          '{src.output.interface}'"
      unless dst.input.slots.any (·.name == p) do
        throw s!"coupling '{c.src} → {c.dst}' carries '{p}', which names no slot of \
          '{dst.input.interface}'"
  let mut out := ""
  out := out ++ "vars: {\n  d2-config: {\n    layout-engine: dagre\n  }\n}\n"
  out := out ++ "direction: right\n"
  out := out ++ ("\"__title\": {label: " ++ q title
    ++ "; shape: text; near: top-center; style: {font-size: 20; bold: true}}\n")
  for s in stages do
    out := out ++ stageBox s (withKind := false) (boxLabel := s.title)
  for c in couplings do
    out := out ++ s!"{q c.src} -> {q c.dst}: {q (String.intercalate " · " c.planes)}\n"
  return out

/-- **The stage overview card** — one stage on one landscape page: the caller's note
lines (the variant tally, the problem statement) over the takes / yields plane groups,
kinds on the rows and admissibility evidence in the tooltips. Refuses a condition name
matching no egress slot. -/
def stageCard (s : StageSpec) : Except String String := do
  checkConditions s
  let mut out := ""
  out := out ++ "vars: {\n  d2-config: {\n    layout-engine: dagre\n  }\n}\n"
  out := out ++ "direction: right\n"
  out := out ++ ("\"__title\": {label: " ++ q s!"stage overview — {s.title}"
    ++ "; shape: text; near: top-center; style: {font-size: 20; bold: true}}\n")
  out := out ++ stageBox s (withKind := true) (boxLabel := "")
  return out

end PropertyKindCalculus.IngestCard
