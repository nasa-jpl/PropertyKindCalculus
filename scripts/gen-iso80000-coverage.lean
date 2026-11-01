/-
Regenerate `tests/PropertyKindCalculus/Tests/Iso80000/Coverage.lean` from the censuses (TOOLS.md §5
step 3; replaces `scripts/gen-iso80000-coverage.py`).

That probe pins the two Dimension-library censuses — `#kind_examination_coverage` (the model
template's M6) and `#kind_dimensional_coverage` (M10) — over every part of ISO 80000 as
`#guard_msgs` records, and pins the matching `_clean` gate over a part exactly when the part's own
report says it passes. The pins are the commands' output, not prose about it; this script is how
they are produced, so that a catalogue change is re-pinned by running the census again rather than
by editing a message until the build goes green.

Run from the repository root, after `lake build PropertyKindCalculus.Iso80000
PropertyKindCalculus.ExaminationCoverage`:

    lake env lean --run scripts/gen-iso80000-coverage.lean            # regenerate the probe in place
    lake env lean --run scripts/gen-iso80000-coverage.lean --check    # diff against the probe; 1 on drift

What it does: imports the catalogue and the censuses, calls the census functions the commands
call (`examinationRows`, `coverageRows`) per part under no namespace — the dimensional rows
pretty-print kind names relative to the current namespace, and the probe declares nothing — and
renders the probe: a fixed header, a summary block *derived from the messages* (no dates, no
hand-typed counts, so a regeneration with an unchanged catalogue is byte-identical), then per part
the record and — only where the report ends `clean` or is empty — the gate. No driver file, no
stdout to split: the message is the string the command logs, computed by the same functions.

`--check` is for a human after a catalogue change, not for CI: CI builds `Tests`, and a stale pin
already fails that build. What `--check` adds is the *direction* of the drift — which part's
report moved and how — before anyone decides whether to accept it.

The gate rule is the library's own (`#kind_dimensional_clean`'s docstring): a violation is
recorded, never gated on. `PartBlock.gate_iff_clean` is that rule as a theorem about the emitter:
a part's block carries the gate exactly when its report is clean. Re-pinning a report whose
summary says `violation` is a finding awaiting a maintainer's decision; the generator will not
write a gate over it.
-/
import PropertyKindCalculus.Iso80000
import PropertyKindCalculus.ExaminationCoverage

open Lean Meta

namespace GenIso80000Coverage

/-- One census: its record command, its gate, the first words of its messages, the rubric it
serves, and the comment written above a gate. -/
structure Census where
  record : String
  gate : String
  pre : String
  rubric : String
  gateNote : String

def censuses : List Census :=
  [{ record := "#kind_examination_coverage", gate := "#kind_examination_clean",
     pre := "examination coverage", rubric := "M6",
     gateNote := "the census as an invariant, with no message to re-bless" },
   { record := "#kind_dimensional_coverage", gate := "#kind_dimensional_clean",
     pre := "dimensional coverage", rubric := "M10",
     gateNote := "the coverage invariant, with no message to re-bless" }]

def catalogueRoot : String := "PropertyKindCalculus.Iso80000"
def parts : List String := (List.range 13).map fun i => s!"Part{i + 1}"
def imports : List String := ["PropertyKindCalculus.Iso80000", "PropertyKindCalculus.ExaminationCoverage"]
def probePath : String := "tests/PropertyKindCalculus/Tests/Iso80000/Coverage.lean"

/-! ## The emitter: a pure function of the messages -/

def lastLine (msg : String) : String := (msg.splitOn "\n").getLast!

/-- The report ends `clean`, or is the empty report. -/
def isClean (pre msg : String) : Bool :=
  (lastLine msg).endsWith "— clean" || msg.startsWith s!"{pre} — no "

/-- The report's last line — or, for an empty report, its one line minus the prefix. -/
def summaryLine (pre msg : String) : String :=
  if msg.startsWith s!"{pre} — " then (msg.drop (pre.length + " — ".length)).toString else lastLine msg

/-- The row marker a line starts with: `[word]`, `⚠ WORD` or `⊘ word`. -/
def markerOf (l : String) : Option String :=
  match l.toList with
  | '[' :: rest =>
    let w := rest.takeWhile Char.isLower
    match rest.drop w.length with
    | ']' :: _ => if w.isEmpty then none else some ("[" ++ String.ofList w ++ "]")
    | _ => none
  | '⚠' :: ' ' :: rest =>
    let w := rest.takeWhile Char.isUpper
    if w.isEmpty then none else some ("⚠ " ++ String.ofList w)
  | '⊘' :: ' ' :: rest =>
    let w := rest.takeWhile Char.isLower
    if w.isEmpty then none else some ("⊘ " ++ String.ofList w)
  | _ => none

/-- Marker counts over the messages, sorted by marker. -/
def totals (msgs : List String) : List (String × Nat) :=
  let marks := msgs.flatMap fun m => (m.splitOn "\n").filterMap markerOf
  let keys := (marks.foldl (fun (ks : List String) k => if ks.contains k then ks else ks ++ [k]) []).mergeSort (· ≤ ·)
  keys.map fun k => (k, (marks.filter (· == k)).length)

def padRight (s : String) (n : Nat) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')

def buildSummary (per : List (Census × List String)) : String :=
  let blocks := per.map fun (c, msgs) =>
    let pm := parts.zip msgs
    let gated := (pm.filter fun (_, m) => isClean c.pre m).map (·.1)
    let tot := String.intercalate ", " ((totals msgs).map fun (k, n) => s!"{n} {k}")
    [s!"  * `{c.record}` ({c.rubric}):"]
      ++ pm.map (fun (p, m) => s!"      {padRight p 7}{summaryLine c.pre m}")
      ++ [s!"    totals: {if tot.isEmpty then "no rows" else tot}",
          s!"    gated (`{c.gate}`): {if gated.isEmpty then "no part" else String.intercalate ", " gated}"]
  String.intercalate "\n" (blocks.flatten) ++ "\n"

/-- One part's pins: the record, and the gate only when the report is clean. -/
structure PartBlock where
  record : String
  gate : Option String

def partBlock (c : Census) (p msg : String) : PartBlock :=
  { record := s!"/--\ninfo: {msg}\n-/\n#guard_msgs (whitespace := lax) in\n{c.record} {catalogueRoot}.{p}\n"
    gate := if isClean c.pre msg then
      some s!"-- {p} is clean: {c.gateNote}\n#guard_msgs in\n{c.gate} {catalogueRoot}.{p}\n" else none }

/-- The "never bless a violation" rule as a property of the emitter. -/
theorem PartBlock.gate_iff_clean (c : Census) (p msg : String) :
    (partBlock c p msg).gate.isSome ↔ isClean c.pre msg = true := by
  simp only [partBlock]
  split <;> simp_all

def header (summary : String) : String :=
  "/-\n`Tests.Iso80000.Coverage` — the two Dimension-library censuses over every part of ISO 80000.\n\n\
  **Generated. Do not edit by hand** — regenerate with `scripts/gen-iso80000-coverage.lean`,\n\
  which runs the censuses and writes this file from their output.\n\n\
  **Records, generated from the compiler.** Every pin below is the command's own output — the\n\
  string the census functions return over the catalogue's root import, written here verbatim\n\
  by `lake env lean --run scripts/gen-iso80000-coverage.lean` — not typed. A change in what a part\n\
  individuates, or in how it dimensions a kind, is therefore a visible diff in this file; a part's\n\
  report is re-pinned only when the change it records has been read and accepted.\n\n\
  **Gates, only where they pass.** A `_clean` command is pinned over a part exactly when that\n\
  part's report ends `clean` (or is empty). Where the report records a violation, there is no\n\
  gate, and the record is a *finding awaiting a maintainer's decision*, not a blessing of it —\n\
  pinning a violation and gating on it are different acts, and the second is what the library's\n\
  `_clean` discipline exists to prevent (`#kind_dimensional_clean`'s docstring). What the current\n\
  findings mean, and what decisions they wait on, is `METHODOLOGY_TEMPLATES.md` §5 — not this\n\
  header, which the generator overwrites.\n\n\
  Summary of the records below, derived from them by the generator:\n\n" ++ summary ++
  "\nBoth commands record `AuditReceipt`s (`PropertyKindCalculus.AuditReceipt`) over each part.\n-/\n"

def preamble : String :=
  "\n-- No namespace: the dimensional rows pretty-print kinds relative to the current namespace,\n\
  -- and the generator that produced these pins ran with none. Nothing here is declared.\n"

/-- The probe: header, module header, the two sections of blocks, `end Blanket`. -/
def render (per : List (Census × List String)) : String :=
  let importLines := imports.flatMap fun m => [s!"public import {m}", s!"meta import {m}"]
  let sections := per.zipIdx.map fun ((c, msgs), i) =>
    let blocks := (parts.zip msgs).flatMap fun (p, m) =>
      let b := partBlock c p m
      b.record :: b.gate.toList
    [s!"/-! ## `{c.record}` — {c.rubric}, part by part -/\n"]
      ++ (if i == 0 then ["@[expose] public section Blanket\n"] else [])
      ++ blocks
  String.intercalate "\n" ([header (buildSummary per), "module\n"] ++ [String.intercalate "\n" importLines]
    ++ [preamble] ++ sections.flatten ++ ["end Blanket\n"])

/-! ## The censuses, called as the commands call them -/

open PropertyKindCalculus in
/-- The message `#kind_examination_coverage` logs for `scope`. -/
def examinationReport (scope : Array Name) : MetaM String := do
  let rows ← ExaminationCoverage.examinationRows scope
  if rows.isEmpty then return "examination coverage — no dimension-one kinds in the given namespaces"
  let sorted := (rows.map (·.line)).qsort (· < ·)
  return s!"examination coverage:\n{String.intercalate "\n" sorted.toList}\n{ExaminationCoverage.examinationSummary rows}"

open PropertyKindCalculus in
/-- The message `#kind_dimensional_coverage` logs for `scope`. -/
def dimensionalReport (scope : Array Name) : MetaM String := do
  let out ← DimensionalCoverage.coverageRows scope
  if out.isEmpty then return "dimensional coverage — no authored kind edges in the given namespaces"
  let sorted := (out.map (·.line)).qsort (· < ·)
  return s!"dimensional coverage:\n{String.intercalate "\n" sorted.toList}\n{DimensionalCoverage.coverageSummary out}"

def reports : MetaM (List (Census × List String)) := do
  let scopes := parts.map fun p => #[(catalogueRoot ++ "." ++ p).toName]
  let ex ← scopes.mapM examinationReport
  let dim ← scopes.mapM dimensionalReport
  return censuses.zip [ex, dim]

unsafe def runMetaUnsafe (x : MetaM α) : IO α := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (imports.map fun m => { module := m.toName }).toArray {} (trustLevel := 0)
    (loadExts := true)
  let ctx : Core.Context := { fileName := "<gen-iso80000-coverage>", fileMap := default, maxHeartbeats := 0 }
  let (a, _, _) ← x.toIO ctx { env }
  return a

/-- The census functions run over the imported catalogue (initializers enabled for the
environment extensions the marks live in). -/
@[implemented_by runMetaUnsafe] opaque runMeta (x : MetaM α) : IO α

/-- A line diff for `--check`: the lines that differ, by number, old `-` and new `+`. -/
def lineDiff (old new : List String) : List String :=
  let n := max old.length new.length
  (List.range n).flatMap fun i =>
    match old[i]?, new[i]? with
    | some a, some b => if a == b then [] else [s!"-{i + 1}: {a}", s!"+{i + 1}: {b}"]
    | some a, none => [s!"-{i + 1}: {a}"]
    | none, some b => [s!"+{i + 1}: {b}"]
    | none, none => []

def main (args : List String) : IO UInt32 := do
  let check ← match args with
    | [] => pure false
    | ["--check"] => pure true
    | _ => do IO.eprintln "usage: lake env lean --run scripts/gen-iso80000-coverage.lean [--check]"; return 2
  unless ← System.FilePath.pathExists "lakefile.lean" do
    IO.eprintln "gen-iso80000-coverage: run from the repository root"; return 2
  let per ← runMeta reports
  for (_, msgs) in per do
    for m in msgs do
      if (m.splitOn "-/").length > 1 || (m.splitOn "/-").length > 1 then
        IO.eprintln s!"gen-iso80000-coverage: a message contains a doc-comment delimiter and cannot be pinned:\n{m}"
        return 2
  let text := render per
  if check then
    let current ← if ← System.FilePath.pathExists probePath then IO.FS.readFile probePath else pure ""
    if current == text then IO.println s!"{probePath}: up to date"; return 0
    for l in lineDiff (current.splitOn "\n") (text.splitOn "\n") do IO.println l
    IO.println s!"\n{probePath}: DRIFT — the censuses' output differs from the pins"
    return 1
  IO.FS.writeFile probePath text
  for (c, msgs) in per do
    let gated := (msgs.filter (isClean c.pre)).length
    let tot := String.intercalate ", " ((totals msgs).map fun (k, n) => s!"{n} {k}")
    IO.println s!"{c.record}: {msgs.length} records, {gated} gates; {tot}"
  IO.println s!"wrote {probePath}"
  return 0

end GenIso80000Coverage

def main (args : List String) : IO UInt32 := GenIso80000Coverage.main args
