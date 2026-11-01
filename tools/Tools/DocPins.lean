module
import Lean
public import Lean.Data.Json.Parser
@[expose] public section
open Lean

/-!
# `doc-pins` — the version, status and terminology claims of this package, gated

The bug this exists to catch: an artifact moves and the prose that describes it does not.
`lean-toolchain` moves at a bump; three READMEs and a CI comment once drifted two minor versions
behind the pin before anyone read them side by side. A chapter gets written and proved; the table
that called it "planned" keeps saying so. Nothing in `lake build` notices either — a stale
sentence still compiles.

Eight checks, each a predicate over a `Snapshot` of what was read, decided in `failures`:

1. **Machine pins.** `blueprint/lean-toolchain` equals `lean-toolchain`, and every `inputRev` in
   either `lake-manifest.json` shaped like a release tag (`vX.Y.Z`) names the pinned version.
2. **Curated prose sites.** Each `site` is a file, a sentence with `{VER}` for the pinned version,
   and how many times it must occur. The count is the point: a grep that finds nothing proves
   nothing, so a claim silently deleted or reworded out of the pattern's reach fails as loudly as
   one left stale.
3. **Discovery.** Every other line in a tracked text file naming a `vX.Y.Z` alongside a pin word is
   `note`d when its file is in `exempt` (with the reason its claims may differ) and fails the gate
   otherwise: a claim nobody has classified.
4. **Blueprint status.** `blueprint/README.md` names every chapter, its headline counts equal the
   parsed ones, and — while every node is `proved` — no chapter carries `_planned_` and the README
   no 🚧/⬜ marker; the standards chapter spells the catalogue's size.
5. **Package-version sites.** Every site in `pkgSites` declares the same version exactly once.
   `--bump` writes the same list, so the bumper and the gate cannot disagree about which files
   carry the version: there is one definition.
6. **Plain-terms coverage.** Every requirement id the introduction's bullets cite exists in the
   catalogue, every catalogued id is cited, and the closing sentence spells the catalogue's size.
7. **Rubric chapters.** Each application-template chapter cites every rubric of its template and
   no other.
8. **Terminology.** Every dictionary term has exactly one `{deftech}` in the blueprint, under the
   section the dictionary names, and not inside a `:::group`; every `{deftech}` has an entry; no
   retired phrasing survives in the blueprint or the root documents; in the library its count is
   held by the `libraryRetiredSites` ratchet.

What is proved: `failures s = [] ↔ Ok s`, where `Ok` is the conjunction of the eight checks'
predicates (`Pins`, `Sites`, `Discovery`, `Status`, `PkgVersion`, `PlainTerms`, `Rubrics`,
`Terminology`) stated over the snapshot, not over the failure list — so the gate's exit code is
the decision of those predicates (`instance : Decidable (Ok s)`), and the completeness claims
(`PlainTerms`, `Rubrics`) read as the ∀ they are. Reading the snapshot (`Snapshot.read`) is the
trusted base: `IO.FS` and `Lean.Json`; the chapter titles and node tags are read from the
blueprint's source text because this gate runs before the blueprint is built.

What this does not catch, stated plainly: `exempt` is per *file*, not per line, so a newly stale
claim written into an exempt file is noted, not failed. Check 4 gates the chapter *inventory* and
the counts, not the prose *about* a chapter.

Usage: `lean --run tools/Tools/DocPins.lean [--quiet]` (toolchain only, no Lake), or
`lake exe doc-pins`; `--bump +p|+m|+M` bumps the package version at `pkgSites`, `--version`
prints it. Exits 1 on any failure.
-/

namespace Tools.DocPins

/-! ## Text helpers (no regular expressions) -/

/-- Occurrences of a nonempty `needle` in `hay`. -/
def count (hay needle : String) : Nat := (hay.splitOn needle).length - 1

def lines (s : String) : List String := s.splitOn "\n"

def trim (s : String) : String := s.trimAscii.toString

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Maximal runs of word characters, in order (`\b…\b` tokens). -/
def words (s : String) : List String :=
  let (acc, cur) := s.toList.foldl (init := (([] : List String), ([] : List Char))) fun (acc, cur) c =>
    if isWordChar c then (acc, c :: cur)
    else if cur.isEmpty then (acc, cur) else (String.ofList cur.reverse :: acc, [])
  (if cur.isEmpty then acc else String.ofList cur.reverse :: acc).reverse

/-- `vX.Y.Z` tokens at word boundaries: the version numbers a line names. -/
def versionTokens (line : String) : List String := Id.run do
  let cs := line.toList.toArray
  let mut out : List String := []
  for i in [0:cs.size] do
    if cs[i]! == 'v' && (i == 0 || !isWordChar cs[i-1]!) then
      let mut j := i + 1
      let mut parts : List String := []
      let mut cur : List Char := []
      let mut okTok := true
      for _ in [0:3] do
        cur := []
        while j < cs.size && cs[j]!.isDigit do
          cur := cs[j]! :: cur; j := j + 1
        if cur.isEmpty then okTok := false; break
        parts := String.ofList cur.reverse :: parts
        if parts.length < 3 then
          if j < cs.size && cs[j]! == '.' then j := j + 1 else okTok := false; break
      if okTok && parts.length == 3 && (j ≥ cs.size || !isWordChar cs[j]!) then
        out := (".".intercalate parts.reverse) :: out
  return out.reverse

/-- `\bpin(s|ned|ning)?\b | \btoolchain\b`, case-insensitive. -/
def hasPinWord (line : String) : Bool :=
  (words line).any fun w => ["pin", "pins", "pinned", "pinning", "toolchain"].contains w.toLower

def isReleaseTag (rev : String) : Bool :=
  match rev.toList with
  | 'v' :: rest => (String.ofList rest).splitOn "." |>.all fun p => p.isNat
  | _ => false

def digitsPrefix (s : String) : String := (s.takeWhile Char.isDigit).toString

/-- The text between the first `open` and the next `close` after it, if both occur. -/
def between (s opn cls : String) : Option String :=
  match s.splitOn opn with
  | _ :: tail :: _ => match tail.splitOn cls with
    | inner :: _ :: _ => some inner
    | _ => none
  | _ => none

/-- Every text between an `open` and the next `close`, in order. -/
def betweenAll (s opn cls : String) : List String :=
  (s.splitOn opn).tail.filterMap fun tail =>
    match tail.splitOn cls with
    | inner :: _ :: _ => some inner
    | _ => none

/-- Word tokens of the shape `<prefix><digits>`, as numbers. -/
def refIds (pre : String) (text : String) : List Nat :=
  (words text).filterMap fun w =>
    if w.startsWith pre then
      let rest := (w.drop pre.length).toString
      if rest.isNat then rest.toNat? else none
    else none

def dedupSorted (l : List Nat) : List Nat :=
  (l.foldl (fun acc n => if acc.contains n then acc else n :: acc) []).mergeSort (· ≤ ·)

def numberWords : List String :=
  ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten",
   "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen",
   "nineteen", "twenty"] ++
  (["one", "two", "three", "four", "five", "six", "seven", "eight", "nine"].map
    fun u => s!"twenty-{u}") ++ ["thirty"]

/-- Verso's `deftech`/`tech` key normalization, reproduced: lowercase, a trailing `ies` becomes
`y`, every run of whitespace or hyphens one space. -/
def termNormalize (s : String) : String :=
  let s := (trim s).toLower
  let s := if s.endsWith "ies" then (s.dropEnd 3).toString ++ "y" else s
  let (acc, sp) := s.toList.foldl (init := (([] : List Char), false)) fun (acc, sp) c =>
    if c.isWhitespace || c == '-' then (acc, true)
    else ((c :: (if sp && !acc.isEmpty then ' ' :: acc else acc)), false)
  let _ := sp
  String.ofList acc.reverse

/-- Columns (in characters) at which `pat` starts in `line`. -/
def columnsOf (line pat : String) : List Nat :=
  let ps := line.splitOn pat
  let (cols, _) := ps.dropLast.foldl (init := (([] : List Nat), 0)) fun (cols, pos) piece =>
    let here := pos + piece.length
    (here :: cols, here + pat.length)
  cols.reverse

/-! ## The configuration: what the gate reads and what it requires -/

structure Site where
  file : String
  /-- The sentence with `{VER}` standing for the pinned version. -/
  template : String
  want : Nat
deriving Repr

/-- Check 2: the curated prose sites. -/
def sites : List Site := [
  ⟨"README.md", "`leanprover/lean4:v{VER}`", 1⟩,
  ⟨"UNCERTAINTY.md", "PKC is pinned `v{VER}` (Mathlib v{VER}, TorchLean `combined`)", 1⟩,
  ⟨"lakefile.lean", "Mathlib `v{VER}` pin", 1⟩,
  ⟨"lakefile.lean", "doc-gen4 v{VER}", 1⟩,
  ⟨"blueprint/lakefile.toml", "on the v{VER} toolchain", 1⟩,
  -- Only the branch NAME tracks the pin here: the commit it names declares a release candidate
  -- in its own `lean-toolchain`, so a claim that it "still pins toolchain {VER}" would be false
  -- of the very commit this file pins.
  ⟨"blueprint/lakefile.toml", "is the `v{VER}`-branch commit", 1⟩,
  ⟨"RENDERING.md", "transitively (`v{VER}`, `", 1⟩]

/-- Check 3: files whose version claims are allowed to differ, and why. -/
def exempt : List (String × String) := [
  ("blueprint/README.md", "dates a measurement of the Verso precompilation failure at the toolchain it was taken on; naming the current pin there would claim a run nobody made"),
  ("RENDERING.md", "records the environment of checkouts outside this repository, and a session log whose entries are dated records of what was true when written"),
  ("blueprint/lakefile.toml", "names the toolchain the verso-blueprint branch tip moved onto — the version this package deliberately does not take, which is why the pin is a SHA"),
  ("lakefile.lean", "names the upstream PhysLib toolchain-bump PR by the version it bumped to"),
  ("dimension/PropertyKindCalculus/Dimension.lean", "names the same upstream PhysLib toolchain-bump PR by the version it bumped to"),
  ("MODULARITY.md", "a staged plan whose status ledger records the version each stage landed at — dated records of what was true when a stage shipped, not claims about the current version")]

def scanSuffixes : List String := ["md", "lean", "toml", "yml", "yaml", "sh", "py"]
def skipDirs : List String := [".lake", ".git", "_out", "docs", "Scratch", ".pixi"]

/-- Check 5: a package-version declaration site — the line starts with `before`, then `X.Y.Z`,
then `after`. The one list `--bump` writes and the gate reads. -/
structure PkgSite where
  file : String
  before : String
  after : String
deriving Repr

def pkgSites : List PkgSite := [
  ⟨"lakefile.lean", "  version := v!\"", "\""⟩,
  ⟨"blueprint/PropertyKindCalculusBlueprint/Version.lean", "def versionStr : String := \"", "\""⟩]

def bpChaptersDir := "blueprint/PropertyKindCalculusBlueprint/Chapters"
def bpSourceDir := "blueprint/PropertyKindCalculusBlueprint"
def bpReadme := "blueprint/README.md"
def bpHeadline := "{CHAPTERS} chapters carrying **{NODES} nodes, {CAPSTONES} of them capstones"
def bpCatalogueRefs := "iso80000/PropertyKindCalculus/Iso80000/References.lean"
def bpCatalogueSites : List Site := [
  ⟨"blueprint/PropertyKindCalculusBlueprint/Chapters/Iso80000.lean", "catalogues {NWORD} of its", 1⟩,
  ⟨"blueprint/PropertyKindCalculusBlueprint/Chapters/Iso80000.lean", "the list of the {NWORD} catalogued parts", 1⟩,
  ⟨"blueprint/PropertyKindCalculusBlueprint/Chapters/Iso80000.lean", "the {NWORD} definitions", 1⟩]
def plannedItalic := "_planned_"
def statusGlyphs : List String := ["🚧", "⬜"]

def reqCatalogue := "requirements/PropertyKindCalculus/Requirements/Catalogue.lean"
def plainTermsFile := "blueprint/PropertyKindCalculusBlueprint/Blueprint.lean"
def plainTermsOpen := "In plain terms, _rigorous metrology_ here means:"
def plainTermsClose := "Between them these bullets name all {NWORD} requirements"

def rubricCatalogue := "rubrics/PropertyKindCalculus/Rubrics/Catalogue.lean"
def rubricChapters : List (String × String) := [
  ("M", "blueprint/PropertyKindCalculusBlueprint/Chapters/ModelTemplate.lean"),
  ("D", "blueprint/PropertyKindCalculusBlueprint/Chapters/DeploymentTemplate.lean")]

def termDictionary := "terminology/PropertyKindCalculus/Terminology/Dictionary.lean"
def termGatedDocs : List String := ["README.md", "MODULARITY.md", "UNCERTAINTY.md",
  "METHODOLOGY_TEMPLATES.md", "RENDERING.md", "blueprint/README.md"]
def termLibraryDirs : List String := ["PropertyKindCalculus", "graph", "torch", "dimension",
  "uncertainty", "index", "crossrefs", "iso80000", "ForPhysLib", "examples", "tests",
  "requirements", "rubrics", "docgen", "apps"]

/-! ## The snapshot: everything the checks read, as data -/

/-- What `read` collected; every check is a pure function of it. `files` holds every curated
file by its repository-relative path; `scan` the tracked text files discovery walks;
`bpChapters`/`bpSources`/`libFiles` the globbed sets, sorted by path. -/
structure Snapshot where
  toolchain : String
  bpToolchain : String
  /-- Per manifest: `(package name, inputRev)` for every package. -/
  manifests : List (String × List (String × String))
  files : List (String × String)
  scan : List (String × String)
  bpChapters : List (String × String)
  bpSources : List (String × String)
  libFiles : List (String × String)

namespace Snapshot

def file (s : Snapshot) (rel : String) : String :=
  (s.files.find? (·.1 == rel)).map (·.2) |>.getD ""

/-- The pinned version, `X.Y.Z`, from `leanprover/lean4:vX.Y.Z`. -/
def version (s : Snapshot) : Option String :=
  match s.toolchain.splitOn "leanprover/lean4:v" with
  | ["", v] => if (v.splitOn ".").length == 3 && (v.splitOn ".").all String.isNat then some v else none
  | _ => none

end Snapshot

/-! ## Check 1: machine pins -/

def Pins (s : Snapshot) (ver : String) : Prop :=
  s.bpToolchain = s.toolchain ∧
  ∀ m ∈ s.manifests, ∀ p ∈ m.2, isReleaseTag p.2 = true → p.2 = "v" ++ ver

instance (s : Snapshot) (ver : String) : Decidable (Pins s ver) := by unfold Pins; infer_instance

def pinFails (s : Snapshot) (ver : String) : List String :=
  (if s.bpToolchain == s.toolchain then [] else
    [s!"blueprint/lean-toolchain is '{s.bpToolchain}', root is '{s.toolchain}'"]) ++
  s.manifests.flatMap fun m => m.2.filterMap fun p =>
    if isReleaseTag p.2 && p.2 != "v" ++ ver then
      some s!"{m.1}: {p.1} pins inputRev {p.2}, expected v{ver}" else none

theorem pinFails_nil_iff (s : Snapshot) (ver : String) : pinFails s ver = [] ↔ Pins s ver := by
  unfold pinFails Pins
  rw [List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_cases hb : (s.bpToolchain == s.toolchain) = true
      · exact beq_iff_eq.mp hb
      · simp [hb] at h
    · intro m hm p hp hrel
      have := List.filterMap_eq_nil_iff.mp (h.2 m hm) p hp
      by_cases hne : p.2 = "v" ++ ver
      · exact hne
      · simp [hrel, hne] at this
  · intro h
    refine ⟨by simp [h.1], ?_⟩
    intro m hm
    rw [List.filterMap_eq_nil_iff]
    intro p hp
    by_cases hrel : isReleaseTag p.2 = true
    · simp [h.2 m hm p hp hrel]
    · simp [hrel]

/-! ## Check 2: curated prose sites -/

def Sites (s : Snapshot) (ver : String) : Prop :=
  ∀ site ∈ sites, count (s.file site.file) (site.template.replace "{VER}" ver) = site.want

instance (s : Snapshot) (ver : String) : Decidable (Sites s ver) := by unfold Sites; infer_instance

def siteLines (s : Snapshot) (ver : String) : List (Bool × String) :=
  sites.map fun site =>
    let sentence := site.template.replace "{VER}" ver
    let got := count (s.file site.file) sentence
    if got == site.want then (true, s!"ok    {site.file}: {sentence}")
    else (false, s!"{site.file}: expected {site.want} occurrence(s) of '{sentence}', found {got}")

def siteFails (s : Snapshot) (ver : String) : List String :=
  (siteLines s ver).filterMap fun l => if l.1 then none else some l.2

theorem siteFails_nil_iff (s : Snapshot) (ver : String) : siteFails s ver = [] ↔ Sites s ver := by
  unfold siteFails siteLines Sites
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro h site hs
    have := h _ (List.mem_map_of_mem hs)
    by_cases hne : count (s.file site.file) (site.template.replace "{VER}" ver) = site.want
    · exact hne
    · simp [hne] at this
  · intro h x hx
    obtain ⟨site, hs, rfl⟩ := List.mem_map.mp hx
    simp [h site hs]

/-! ## Check 3: discovery -/

/-- A discovery entry: file, line number, the stale versions, the line. -/
structure Claim where
  file : String
  line : Nat
  stale : List String
  text : String

def claims (s : Snapshot) (ver : String) : List Claim :=
  s.scan.flatMap fun (rel, text) =>
    ((lines text).zipIdx 1).filterMap fun (line, n) =>
      if hasPinWord line then
        let stale := (versionTokens line).filter (· != ver)
        if stale.isEmpty then none else some ⟨rel, n, stale, line⟩
      else none

def Claim.render (c : Claim) : String :=
  s!"{c.file}:{c.line}: names v{", v".intercalate c.stale} — {(trim c.text).take 96 |>.toString}"

def isExempt (rel : String) : Bool := exempt.any (·.1 == rel)

/-- Every claim is in an exempt file. -/
def Discovery (s : Snapshot) (ver : String) : Prop := ∀ c ∈ claims s ver, isExempt c.file = true

instance (s : Snapshot) (ver : String) : Decidable (Discovery s ver) := by
  unfold Discovery; infer_instance

def unclassified (s : Snapshot) (ver : String) : List Claim :=
  (claims s ver).filter fun c => !isExempt c.file

theorem unclassified_nil_iff (s : Snapshot) (ver : String) :
    unclassified s ver = [] ↔ Discovery s ver := by
  unfold unclassified Discovery
  rw [List.filter_eq_nil_iff]
  simp

/-! ## Check 4: blueprint status -/

/-- `#doc (Manual) "<title>" =>`, the first per chapter file. -/
def chapterTitle (text : String) : Option String :=
  match betweenAll text "#doc (Manual) \"" "\"" with
  | t :: _ => if count text s!"#doc (Manual) \"{t}\" =>" ≥ 1 then some t else none
  | [] => none

/-- Every `(tags := "<tags>")`. -/
def nodeTags (text : String) : List String :=
  (text.splitOn "(tags := \"").tail.filterMap fun tail =>
    match tail.splitOn "\"" with
    | tags :: rest :: _ => if rest.startsWith ")" then some tags else none
    | _ => none

def catalogueSize (refs : String) : Option Nat :=
  match refs.splitOn "def catalogue : List StandardRef :=" with
  | _ :: tail :: _ =>
    let tail := (tail.trimAsciiStart).toString
    if tail.startsWith "[" then
      match ((tail.drop 1).toString).splitOn "]" with
      | inner :: _ => some ((inner.splitOn ",").filter fun e => !(trim e).isEmpty).length
      | _ => none
    else none
  | _ => none

structure StatusData where
  titles : List String
  nodes : Nat
  proved : Nat
  capstones : Nat
  headline : String
  readme : String
  planned : List String
  catalogueN : Option Nat

def statusData (s : Snapshot) : StatusData :=
  let titles := s.bpChapters.filterMap fun (_, t) => chapterTitle t
  let tags := s.bpSources.flatMap fun (_, t) => nodeTags t
  let nodes := tags.length
  let proved := (tags.filter fun t => count t "proved" ≥ 1).length
  let capstones := (tags.filter fun t => count t "capstone" ≥ 1).length
  let headline := ((bpHeadline.replace "{CHAPTERS}" (toString titles.length)).replace "{NODES}"
    (toString nodes)).replace "{CAPSTONES}" (toString capstones)
  { titles, nodes, proved, capstones, headline, readme := s.file bpReadme,
    planned := s.bpChapters.filterMap fun (rel, t) => if count t plannedItalic ≥ 1 then some rel else none,
    catalogueN := catalogueSize (s.file bpCatalogueRefs) }

def statusLines (s : Snapshot) : List (Bool × String) :=
  let d := statusData s
  if d.titles.isEmpty then
    [(false, s!"{bpChaptersDir}: parsed no chapter titles — the `#doc (Manual)` pattern no longer matches how chapters are declared")]
  else
    let got := count d.readme d.headline
    [if got == 1 then (true, s!"ok    {bpReadme}: {d.headline}")
     else (false, s!"{bpReadme}: expected 1 occurrence of '{d.headline}', found {got}")] ++
    (let unlisted := d.titles.filter fun t => count d.readme t == 0
     [if unlisted.isEmpty then (true, s!"ok    {bpReadme}: names all {d.titles.length} chapters")
      else (false, s!"{bpReadme}: {unlisted.length} chapter(s) not named in it: {"; ".intercalate unlisted}")]) ++
    (if d.proved == d.nodes then
      (statusGlyphs.filterMap fun g => if count d.readme g ≥ 1 then
        some (false, s!"{bpReadme}: carries the '{g}' status marker while all {d.nodes} nodes parse as proved") else none) ++
      (d.planned.map fun rel => (false, s!"{rel}: calls a node {plannedItalic} while all {d.nodes} nodes parse as proved")) ++
      [(true, s!"ok    blueprint: all {d.nodes} nodes proved, no stale status marker")]
     else
      let claim := s!"{d.nodes - d.proved} not yet proved"
      [if count d.readme claim ≥ 1 then (true, s!"ok    {bpReadme}: {claim}")
       else (false, s!"{bpReadme}: {d.nodes - d.proved} node(s) are not tagged proved, but it does not say so — expected the phrase '{claim}'")]) ++
    (match d.catalogueN with
     | none => [(false, s!"{bpCatalogueRefs}: could not parse `catalogue : List StandardRef`")]
     | some n =>
       match numberWords[n]? with
       | none => [(false, s!"{bpCatalogueRefs}: {n} parts, beyond the spelled-out range")]
       | some word => bpCatalogueSites.map fun site =>
         let sentence := site.template.replace "{NWORD}" word
         let got := count (s.file site.file) sentence
         if got == site.want then (true, s!"ok    {site.file}: {sentence}")
         else (false, s!"{site.file}: expected {site.want} occurrence(s) of '{sentence}' ({n} parts in the catalogue), found {got}"))

def statusFails (s : Snapshot) : List String :=
  (statusLines s).filterMap fun l => if l.1 then none else some l.2

/-- Check 4 as a predicate: every line the status check produces is an `ok` line. -/
def Status (s : Snapshot) : Prop := ∀ l ∈ statusLines s, l.1 = true

instance (s : Snapshot) : Decidable (Status s) := by unfold Status; infer_instance

theorem statusFails_nil_iff (s : Snapshot) : statusFails s = [] ↔ Status s := by
  unfold statusFails Status
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro h l hl
    have := h l hl
    by_cases hne : l.1 = true
    · exact hne
    · simp [hne] at this
  · intro h l hl
    simp [h l hl]

/-! ## Check 5: package-version sites -/

def parseSemver (s : String) : Option (Nat × Nat × Nat) :=
  match s.splitOn "." with
  | [a, b, c] => do pure (← a.toNat?, ← b.toNat?, ← c.toNat?)
  | _ => none

/-- The version a line declares at `site`, if the line is `before ++ X.Y.Z ++ after …`. -/
def PkgSite.readLine (site : PkgSite) (line : String) : Option String :=
  if line.startsWith site.before then
    let rest := (line.drop site.before.length).toString
    let ver := (rest.takeWhile fun c => c.isDigit || c == '.').toString
    if (parseSemver ver).isSome && ((rest.drop ver.length).toString).startsWith site.after then some ver
    else none
  else none

/-- The versions a file declares at `site` (one per declaring line). -/
def PkgSite.read (site : PkgSite) (text : String) : List String :=
  (lines text).filterMap site.readLine

/-- `before ++ v ++ after ++ rest` where the line declared a version; the line otherwise. -/
def PkgSite.bumpLine (site : PkgSite) (v : String) (line : String) : String :=
  match site.readLine line with
  | some old => site.before ++ v ++ ((line.drop (site.before.length + old.length)).toString)
  | none => line

def PkgSite.bump (site : PkgSite) (v : String) (text : String) : String :=
  "\n".intercalate ((lines text).map (site.bumpLine v))

def pkgVersions (s : Snapshot) : List (PkgSite × List String) :=
  pkgSites.map fun site => (site, site.read (s.file site.file))

/-- Every site declares exactly one version and all sites agree. -/
def PkgVersion (s : Snapshot) : Prop :=
  (∀ p ∈ pkgVersions s, p.2.length = 1) ∧
  ∀ p ∈ pkgVersions s, ∀ q ∈ pkgVersions s, p.2 = q.2

instance (s : Snapshot) : Decidable (PkgVersion s) := by unfold PkgVersion; infer_instance

def pkgVersionFails (s : Snapshot) : List String :=
  ((pkgVersions s).filterMap fun p =>
    if p.2.length == 1 then none else
      some s!"{p.1.file}: expected 1 version declaration matching '{p.1.before}X.Y.Z{p.1.after}' at the start of a line, found {p.2.length}") ++
  (if (pkgVersions s).all (fun p => (pkgVersions s).all fun q => p.2 == q.2) then [] else
    [s!"package-version declarations disagree: {"; ".intercalate ((pkgVersions s).map fun (site, vs) => s!"{site.file} says {", ".intercalate vs}")}"])

theorem pkgVersionFails_nil_iff (s : Snapshot) : pkgVersionFails s = [] ↔ PkgVersion s := by
  unfold pkgVersionFails PkgVersion
  rw [List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
    · have := h1 p hp
      by_cases hne : p.2.length = 1
      · exact hne
      · simp [hne] at this
    · by_cases hall : (pkgVersions s).all (fun p => (pkgVersions s).all fun q => p.2 == q.2) = true
      · have := (List.all_eq_true.mp hall p hp)
        exact beq_iff_eq.mp (List.all_eq_true.mp this q hq)
      · simp [hall] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => by simp [h1 p hp], ?_⟩
    have : (pkgVersions s).all (fun p => (pkgVersions s).all fun q => p.2 == q.2) = true :=
      List.all_eq_true.mpr fun p hp => List.all_eq_true.mpr fun q hq => beq_iff_eq.mpr (h2 p hp q hq)
    simp [this]

/-! ## Check 6: the plain-terms gloss of the requirement catalogue -/

def catalogued (s : Snapshot) : List Nat :=
  dedupSorted ((betweenAll (s.file reqCatalogue) "id := \"R" "\"").filterMap fun d =>
    if d.isNat then d.toNat? else none)

/-- The plain-terms list: from its opening sentence to its closing sentence. -/
def plainTermsBody (s : Snapshot) : Option String :=
  let doc := s.file plainTermsFile
  match numberWords[(catalogued s).length]? with
  | none => none
  | some word =>
    let closing := plainTermsClose.replace "{NWORD}" word
    if count doc plainTermsOpen == 1 && count doc closing == 1 then between doc plainTermsOpen closing
    else none

def cited (s : Snapshot) : List Nat :=
  match plainTermsBody s with
  | some body => dedupSorted (refIds "R" body)
  | none => []

/-- The list is delimited and names exactly the catalogued requirements. -/
def PlainTerms (s : Snapshot) : Prop :=
  (catalogued s) ≠ [] ∧ (plainTermsBody s).isSome = true ∧
  (∀ n ∈ cited s, n ∈ catalogued s) ∧ (∀ n ∈ catalogued s, n ∈ cited s)

instance (s : Snapshot) : Decidable (PlainTerms s) := by unfold PlainTerms; infer_instance

def plainTermsFails (s : Snapshot) : List String :=
  if (catalogued s).isEmpty then
    [s!"{reqCatalogue}: parsed no requirement ids — the `id := \"R…\"` pattern no longer matches how requirements are declared"]
  else match plainTermsBody s with
  | none =>
    let doc := s.file plainTermsFile
    if count doc plainTermsOpen != 1 then
      [s!"{plainTermsFile}: expected 1 occurrence of '{plainTermsOpen}', found {count doc plainTermsOpen}"]
    else match numberWords[(catalogued s).length]? with
      | none => [s!"{reqCatalogue}: {(catalogued s).length} requirements, beyond the spelled-out range check 6 can state"]
      | some word =>
        [s!"{plainTermsFile}: expected 1 occurrence of '{plainTermsClose.replace "{NWORD}" word}' ({(catalogued s).length} requirements in the catalogue), found {count doc (plainTermsClose.replace "{NWORD}" word)}"]
  | some _ =>
    let unknown := (cited s).filter fun n => !(catalogued s).contains n
    let missing := (catalogued s).filter fun n => !(cited s).contains n
    (if unknown.isEmpty then [] else
      [s!"{plainTermsFile}: plain-terms bullets cite {", ".intercalate (unknown.map fun n => s!"R{n}")}, which {reqCatalogue} does not define"]) ++
    (if missing.isEmpty then [] else
      [s!"{plainTermsFile}: no plain-terms bullet glosses {", ".intercalate (missing.map fun n => s!"R{n}")} — either add one or drop the list's completeness claim"])

theorem plainTermsFails_nil_iff (s : Snapshot) : plainTermsFails s = [] ↔ PlainTerms s := by
  unfold plainTermsFails PlainTerms
  by_cases hc : (catalogued s).isEmpty = true
  · simp [List.isEmpty_iff.mp hc]
  · have hc' : catalogued s ≠ [] := fun h => hc (by simp [h])
    simp only [hc, Bool.false_eq_true, ↓reduceIte, ne_eq, hc', not_false_eq_true, true_and]
    cases hb : plainTermsBody s with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_and, iff_false]
      split <;> simp
      split <;> simp
    | some body =>
      simp only [Option.isSome_some, true_and, List.append_eq_nil_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun n hn => ?_, fun n hn => ?_⟩
        · by_cases hne : n ∈ catalogued s
          · exact hne
          · exfalso
            by_cases h : (List.filter (fun n => !(catalogued s).contains n) (cited s)).isEmpty = true
            · have := List.filter_eq_nil_iff.mp (List.isEmpty_iff.mp h) n hn
              simp [hne] at this
            · have hf : (List.filter (fun n => !(catalogued s).contains n) (cited s)).isEmpty = false := by
                simpa using h
              simp at h1
              exact hne (h1 n hn)
        · by_cases hne : n ∈ cited s
          · exact hne
          · exfalso
            by_cases h : (List.filter (fun n => !(cited s).contains n) (catalogued s)).isEmpty = true
            · have := List.filter_eq_nil_iff.mp (List.isEmpty_iff.mp h) n hn
              simp [hne] at this
            · have hf : (List.filter (fun n => !(cited s).contains n) (catalogued s)).isEmpty = false := by
                simpa using h
              simp at h2
              exact hne (h2 n hn)
      · rintro ⟨h1, h2⟩
        have e1 : (List.filter (fun n => !(catalogued s).contains n) (cited s)) = [] :=
          List.filter_eq_nil_iff.mpr fun n hn => by simp [h1 n hn]
        have e2 : (List.filter (fun n => !(cited s).contains n) (catalogued s)) = [] :=
          List.filter_eq_nil_iff.mpr fun n hn => by simp [h2 n hn]
        rw [e1, e2]
        simp

/-! ## Check 7: the application-template chapters against the rubric catalogue -/

def rubricIds (s : Snapshot) (pre : String) : List String :=
  (betweenAll (s.file rubricCatalogue) s!"id := \"{pre}" "\"").filterMap fun d =>
    if d.isNat then some (pre ++ d) else none

def rubricCited (s : Snapshot) (pre chapter : String) : List String :=
  dedupSorted (refIds pre (s.file chapter)) |>.map fun n => s!"{pre}{n}"

/-- Each chapter cites exactly its template's rubrics. -/
def Rubrics (s : Snapshot) : Prop :=
  ∀ pc ∈ rubricChapters, rubricIds s pc.1 ≠ [] ∧
    (∀ r ∈ rubricCited s pc.1 pc.2, r ∈ rubricIds s pc.1) ∧
    (∀ r ∈ rubricIds s pc.1, r ∈ rubricCited s pc.1 pc.2)

instance (s : Snapshot) : Decidable (Rubrics s) := by unfold Rubrics; infer_instance

def rubricLinesFor (s : Snapshot) (pc : String × String) : List (Bool × String) :=
  let ids := rubricIds s pc.1
  if ids.isEmpty then
    [(false, s!"{rubricCatalogue}: parsed no {pc.1}-rubric ids — the `id := \"{pc.1}…\"` pattern no longer matches how rubrics are declared")]
  else
    let cited := rubricCited s pc.1 pc.2
    let unknown := cited.filter fun r => !ids.contains r
    let missing := ids.filter fun r => !cited.contains r
    (if unknown.isEmpty then [] else
      [(false, s!"{pc.2}: cites {", ".intercalate unknown}, which {rubricCatalogue} does not define")]) ++
    (if missing.isEmpty then [] else
      [(false, s!"{pc.2}: no paragraph glosses {", ".intercalate missing} — either add one or drop the rubric from the template")]) ++
    (if unknown.isEmpty && missing.isEmpty then
      [(true, s!"ok    {pc.2}: glosses all {ids.length} rubrics of its template")] else [])

def rubricLines (s : Snapshot) : List (Bool × String) := rubricChapters.flatMap (rubricLinesFor s)

def rubricFails (s : Snapshot) : List String :=
  (rubricLines s).filterMap fun l => if l.1 then none else some l.2

theorem rubricLinesFor_ok_iff (s : Snapshot) (pc : String × String) :
    (∀ l ∈ rubricLinesFor s pc, l.1 = true) ↔
      rubricIds s pc.1 ≠ [] ∧ (∀ r ∈ rubricCited s pc.1 pc.2, r ∈ rubricIds s pc.1) ∧
        (∀ r ∈ rubricIds s pc.1, r ∈ rubricCited s pc.1 pc.2) := by
  unfold rubricLinesFor
  by_cases hids : (rubricIds s pc.1).isEmpty = true
  · simp [List.isEmpty_iff.mp hids]
  · have hne : rubricIds s pc.1 ≠ [] := fun h => hids (by simp [h])
    simp only [hids, Bool.false_eq_true, ↓reduceIte, ne_eq, hne, not_false_eq_true, true_and]
    constructor
    · intro key
      refine ⟨fun r hr => ?_, fun r hr => ?_⟩
      · by_cases hr' : r ∈ rubricIds s pc.1
        · exact hr'
        · have hu : ((rubricCited s pc.1 pc.2).filter fun r => !(rubricIds s pc.1).contains r).isEmpty = false := by
            rw [Bool.eq_false_iff, Ne, List.isEmpty_iff, List.filter_eq_nil_iff]
            intro hall; have := hall r hr; simp [hr'] at this
          have := key (false, s!"{pc.2}: cites {", ".intercalate ((rubricCited s pc.1 pc.2).filter fun r => !(rubricIds s pc.1).contains r)}, which {rubricCatalogue} does not define")
            (by simp; first | exact Or.inl ⟨r, hr, hr'⟩ | exact Or.inr (Or.inl ⟨r, hr, hr'⟩) | exact Or.inr ⟨r, hr, hr'⟩)
          simp at this
      · by_cases hr' : r ∈ rubricCited s pc.1 pc.2
        · exact hr'
        · have hm : ((rubricIds s pc.1).filter fun r => !(rubricCited s pc.1 pc.2).contains r).isEmpty = false := by
            rw [Bool.eq_false_iff, Ne, List.isEmpty_iff, List.filter_eq_nil_iff]
            intro hall; have := hall r hr; simp [hr'] at this
          have := key (false, s!"{pc.2}: no paragraph glosses {", ".intercalate ((rubricIds s pc.1).filter fun r => !(rubricCited s pc.1 pc.2).contains r)} — either add one or drop the rubric from the template")
            (by simp; first | exact Or.inl ⟨r, hr, hr'⟩ | exact Or.inr (Or.inl ⟨r, hr, hr'⟩) | exact Or.inr ⟨r, hr, hr'⟩)
          simp at this
    · rintro ⟨h1, h2⟩ l hl
      have e1 : ((rubricCited s pc.1 pc.2).filter fun r => !(rubricIds s pc.1).contains r) = [] :=
        List.filter_eq_nil_iff.mpr fun r hr => by simp [h1 r hr]
      have e2 : ((rubricIds s pc.1).filter fun r => !(rubricCited s pc.1 pc.2).contains r) = [] :=
        List.filter_eq_nil_iff.mpr fun r hr => by simp [h2 r hr]
      simp only [e1, e2, List.isEmpty_nil, Bool.and_self, ↓reduceIte, List.nil_append,
        List.mem_singleton] at hl
      subst hl; rfl

theorem rubricFails_nil_iff (s : Snapshot) : rubricFails s = [] ↔ Rubrics s := by
  unfold rubricFails rubricLines Rubrics
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro h pc hpc
    rw [← rubricLinesFor_ok_iff]
    intro l hl
    have := h l (List.mem_flatMap.mpr ⟨pc, hpc, hl⟩)
    by_cases hne : l.1 = true
    · exact hne
    · simp [hne] at this
  · intro h l hl
    obtain ⟨pc, hpc, hl⟩ := List.mem_flatMap.mp hl
    simp [(rubricLinesFor_ok_iff s pc).mpr (h pc hpc) l hl]

/-! ## Check 8: the terminological dictionary -/

structure Term where
  key : String
  definedIn : String
  avoid : List String
deriving Repr

/-- The dictionary entries, read the way a reader would: one `{ key := … }` per entry inside
`def dictionary`, with the fields the gate needs. -/
def parseDictionary (text : String) : List Term :=
  match text.splitOn "def dictionary : List Term :=\n" with
  | _ :: tail :: _ =>
    match tail.splitOn "\n  ]\n" with
    | block :: _ :: _ =>
      let chunks := (("\n" ++ block).replace "\n  [ {" "\n  , {").splitOn "\n  , {" |>.tail
      chunks.filterMap fun chunk =>
        match between chunk "key := \"" "\"" with
        | none => none
        | some key => some
          { key, definedIn := (between chunk "definedIn := \"" "\"").getD "",
            avoid := match between chunk "avoid := [" "]" with
              | some inner => ((inner.splitOn "\"").zipIdx).filterMap fun (q, i) =>
                  if i % 2 == 1 then some q else none
              | none => [] }
    | _ => []
  | _ => []

/-- A `{deftech}[…]` in the blueprint: its file, line, key, the enclosing section tag, and
whether it sits inside a `:::group` block. -/
structure Deftech where
  file : String
  line : Nat
  key : String
  enclosing : Option String
  inGroup : Bool

def deftechsOf (rel text : String) : List Deftech × List String := Id.run do
  let mut out : List Deftech := []
  let mut tags : List String := []
  let mut enclosing : Option String := none
  let mut inGroup := false
  for (line, n) in (lines text).zipIdx 1 do
    if line.startsWith ":::group" then inGroup := true
    else if inGroup && trim line == ":::" then inGroup := false
    let tagCols := (columnsOf line "tag := \"").map fun c => (c, true)
    let defCols := (columnsOf line "{deftech}[").map fun c => (c, false)
    let events := (tagCols ++ defCols).mergeSort fun a b => a.1 ≤ b.1
    for (col, isTag) in events do
      let after := ((line.drop col).toString)
      if isTag then
        if let some t := between after "tag := \"" "\"" then
          tags := t :: tags; enclosing := some t
      else if let some k := between after "{deftech}[" "]" then
        out := ⟨rel, n, k, enclosing, inGroup⟩ :: out
  return (out.reverse, tags.reverse)

def termFiles (s : Snapshot) : List (String × String) :=
  s.bpSources.filter fun (rel, _) =>
    rel.startsWith (bpChaptersDir ++ "/") || rel == bpSourceDir ++ "/Blueprint.lean"

def terminologyLines (s : Snapshot) : List (Bool × String) :=
  let entries := parseDictionary (s.file termDictionary)
  if entries.isEmpty then
    [(false, s!"{termDictionary}: parsed no dictionary entries — the `def dictionary` layout no longer matches what this gate reads")]
  else
    let scanned := (termFiles s).map fun (rel, text) => deftechsOf rel text
    let deftechs := scanned.flatMap (·.1)
    let tagsAll := scanned.flatMap (·.2)
    let groupFails := deftechs.filterMap fun d => if d.inGroup then
      some (false, s!"{d.file}:{d.line}: \{deftech} for '{d.key}' sits inside a `:::group` block, which Verso does not traverse for term definitions — define it in prose or in a definition or theorem node")
      else none
    let known := entries.map fun e => termNormalize e.key
    let entryFails := entries.flatMap fun e =>
      let k := termNormalize e.key
      let at_ := deftechs.filter fun d => termNormalize d.key == k
      (match at_ with
       | [d] => if d.enclosing == some e.definedIn then [] else
         [(false, s!"{d.file}:{d.line}: \{deftech} for '{e.key}' sits under tag {repr d.enclosing}; the dictionary says '{e.definedIn}'")]
       | _ =>
         let where_ := "; ".intercalate (at_.map fun d => s!"{d.file}:{d.line}")
         [(false, s!"{termDictionary}: term '{e.key}' needs exactly one \{deftech} in the blueprint, found {at_.length}{if where_.isEmpty then "" else s!" ({where_})"}")]) ++
      (if tagsAll.contains e.definedIn then [] else
        [(false, s!"{termDictionary}: term '{e.key}' names section tag '{e.definedIn}', which no blueprint section carries")])
    let unknownFails := deftechs.filterMap fun d =>
      if known.contains (termNormalize d.key) then none else
        some (false, s!"{d.file}:{d.line}: \{deftech} defines '{termNormalize d.key}', which the dictionary does not carry — add the entry first")
    let retired := entries.flatMap fun e => e.avoid.map fun a => (a, e.key)
    let gated := ((termFiles s).filter fun (rel, _) => !rel.endsWith "Terminology.lean") ++
      (termGatedDocs.filterMap fun rel => if s.files.any (·.1 == rel) then some (rel, s.file rel) else none)
    let retiredFails := gated.flatMap fun (rel, text) =>
      ((lines text).zipIdx 1).flatMap fun (line, n) =>
        retired.filterMap fun (phrase, canonical) =>
          if count line.toLower phrase.toLower ≥ 1 then
            some (false, s!"{rel}:{n}: retired phrasing '{phrase}' — the dictionary's term is '{canonical}'")
          else none
    let hits := s.libFiles.filterMap fun (rel, text) =>
      let low := text.toLower
      let n := retired.foldl (fun acc (phrase, _) => acc + count low phrase.toLower) 0
      if n == 0 then none else some (rel, n)
    let total := hits.foldl (fun acc (_, n) => acc + n) 0
    let ratchetLines : List (Bool × String) :=
      match (between (s.file termDictionary) "def libraryRetiredSites : Nat := " "\n").map digitsPrefix with
      | none => [(false, s!"{termDictionary}: could not parse `libraryRetiredSites`")]
      | some d => match d.toNat? with
        | none => [(false, s!"{termDictionary}: could not parse `libraryRetiredSites`")]
        | some pin =>
          if total == pin then [(true, s!"ok    {termDictionary}: library retired-phrasing sites = {total}, at the ratchet pin")]
          else
            let top := ", ".intercalate (((hits.mergeSort fun a b => a.2 ≥ b.2).take 6).map fun (r, c) => s!"{r} ({c})")
            let verdict := if total > pin then "a regression" else "lower the pin to match"
            [(false, s!"{termDictionary}: `libraryRetiredSites := {pin}`, but the library carries {total} retired-phrasing site(s) — {verdict}; top files: {top}")]
    let fails := groupFails ++ entryFails ++ unknownFails ++ retiredFails ++ ratchetLines
    fails ++ (if fails.all (·.1) then
      [(true, s!"ok    {termDictionary}: {entries.length} terms, each defined once under its section; no retired phrasing in the blueprint or the root documents")] else [])

def terminologyFails (s : Snapshot) : List String :=
  (terminologyLines s).filterMap fun l => if l.1 then none else some l.2

def Terminology (s : Snapshot) : Prop := ∀ l ∈ terminologyLines s, l.1 = true

instance (s : Snapshot) : Decidable (Terminology s) := by unfold Terminology; infer_instance

theorem terminologyFails_nil_iff (s : Snapshot) : terminologyFails s = [] ↔ Terminology s := by
  unfold terminologyFails Terminology
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro h l hl
    have := h l hl
    by_cases hne : l.1 = true
    · exact hne
    · simp [hne] at this
  · intro h l hl
    simp [h l hl]

/-! ## The gate -/

/-- The eight checks, over a snapshot whose toolchain names the version `ver`. -/
def Ok (s : Snapshot) (ver : String) : Prop :=
  Pins s ver ∧ Sites s ver ∧ Discovery s ver ∧ Status s ∧ PkgVersion s ∧ PlainTerms s ∧
  Rubrics s ∧ Terminology s

instance (s : Snapshot) (ver : String) : Decidable (Ok s ver) := by unfold Ok; infer_instance

def failures (s : Snapshot) (ver : String) : List String :=
  pinFails s ver ++ siteFails s ver ++
  (if unclassified s ver = [] then [] else [s!"{(unclassified s ver).length} unclassified version claim(s)"]) ++
  statusFails s ++ pkgVersionFails s ++ plainTermsFails s ++ rubricFails s ++ terminologyFails s

/-- The gate's decision is the conjunction of the eight predicates: it exits 0 exactly when every
pin, site, claim, status, version, gloss, rubric and term holds as stated above. -/
theorem failures_nil_iff (s : Snapshot) (ver : String) : failures s ver = [] ↔ Ok s ver := by
  unfold failures Ok
  simp only [List.append_eq_nil_iff, pinFails_nil_iff, siteFails_nil_iff, statusFails_nil_iff,
    pkgVersionFails_nil_iff, plainTermsFails_nil_iff, rubricFails_nil_iff, terminologyFails_nil_iff,
    ← unclassified_nil_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    refine ⟨h1, h2, ?_, h4, h5, h6, h7, h8⟩
    by_cases h : unclassified s ver = []
    · exact h
    · simp [h] at h3
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, by simp [h3]⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩

/-! ## Reading the snapshot (the trusted base) -/

def readText (p : System.FilePath) : IO (Option String) := do
  let bytes ← IO.FS.readBinFile p
  return String.fromUTF8? bytes

def readReq (root : System.FilePath) (rel : String) : IO String := do
  match ← readText (root / rel) with
  | some t => pure t
  | none => throw <| IO.userError s!"{rel}: not found or not UTF-8"

def hasSkipPart (root p : System.FilePath) : Bool :=
  let rel := p.toString.drop (root.toString.length + 1) |>.toString
  (rel.splitOn "/").any skipDirs.contains

/-- Files under `dir` (recursively unless `direct`) with extension `lean`, sorted by path, with
their text. -/
def leanFiles (root : System.FilePath) (dir : String) (direct := false) :
    IO (List (String × String)) := do
  if !(← (root / dir).isDir) then return []
  let all ← if direct then (root / dir).readDir <&> (·.map (·.path))
    else (root / dir).walkDir fun d => pure (!hasSkipPart root d)
  let rels := (all.filter fun p => p.extension == some "lean").map fun p =>
    (p.toString.drop (root.toString.length + 1)).toString
  let rels := rels.qsort (· < ·)
  rels.toList.filterMapM fun (rel : String) => do
    return (← readText (root / rel)).map (rel, ·)

def manifestRevs (text : String) : Except String (List (String × String)) := do
  let j ← Json.parse text
  let pkgs ← (j.getObjVal? "packages").toOption.getD (Json.arr #[]) |>.getArr?
  pkgs.toList.mapM fun p => do
    let name := ((p.getObjVal? "name").bind Json.getStr?).toOption.getD "?"
    let rev := ((p.getObjVal? "inputRev").bind Json.getStr?).toOption.getD ""
    pure (name, rev)

def Snapshot.read (root : System.FilePath) : IO Snapshot := do
  let toolchain := trim (← readReq root "lean-toolchain")
  let bpToolchain := trim (← readReq root "blueprint/lean-toolchain")
  let manifests ← ["lake-manifest.json", "blueprint/lake-manifest.json"].mapM fun m => do
    match manifestRevs (← readReq root m) with
    | .ok revs => pure (m, revs)
    | .error e => throw <| IO.userError s!"{m}: {e}"
  let curated := (sites.map (·.file)) ++ [bpReadme, bpCatalogueRefs, reqCatalogue, plainTermsFile,
    rubricCatalogue, termDictionary] ++ (bpCatalogueSites.map (·.file)) ++ (pkgSites.map (·.file)) ++
    (rubricChapters.map (·.2)) ++ termGatedDocs
  let curated := curated.foldl (fun acc f => if acc.contains f then acc else acc ++ [f]) []
  let files ← curated.filterMapM fun (rel : String) => do
    return (← readText (root / rel)).map (rel, ·)
  let all ← root.walkDir fun d => pure (!hasSkipPart root d)
  let scanRels := (all.filter fun p => !hasSkipPart root p &&
      (p.extension.map scanSuffixes.contains).getD false).map fun p =>
    (p.toString.drop (root.toString.length + 1)).toString
  let scan ← (scanRels.qsort (· < ·)).toList.filterMapM fun (rel : String) => do
    if !(← (root / rel).isDir) then return (← readText (root / rel)).map (rel, ·) else return none
  let bpChapters ← leanFiles root bpChaptersDir (direct := true)
  let bpSources ← leanFiles root bpSourceDir
  let libFiles ← termLibraryDirs.flatMapM (leanFiles root)
  return { toolchain, bpToolchain, manifests, files, scan, bpChapters, bpSources, libFiles }

/-! ## The command line -/

def bumpTo (root : System.FilePath) (arg : String) : IO UInt32 := do
  let versions ← pkgSites.mapM fun site => do
    let text ← readReq root site.file
    match site.read text with
    | [v] => pure (site, text, v)
    | vs => throw <| IO.userError s!"{site.file}: expected 1 version declaration matching '{site.before}X.Y.Z{site.after}', found {vs.length}"
  let current := versions.head?.map (·.2.2) |>.getD ""
  if versions.any (·.2.2 != current) then
    IO.eprintln "error: version declarations disagree -- reconcile before bumping:"
    for (site, _, v) in versions do IO.eprintln s!"  {v}  {site.file}"
    return 1
  if arg == "" then IO.println current; return 0
  let some (ma, mi, pa) := parseSemver current
    | throw <| IO.userError s!"not a version: {current}"
  let new := match arg with
    | "+M" => s!"{ma + 1}.0.0"
    | "+m" => s!"{ma}.{mi + 1}.0"
    | "+p" => s!"{ma}.{mi}.{pa + 1}"
    | _ => ""
  if new.isEmpty then
    IO.eprintln s!"error: unknown bump '{arg}' (use +p, +m or +M)"; return 2
  for (site, text, _) in versions do
    let bumped := site.bump new text
    IO.FS.writeFile (root / site.file) bumped
    match site.read bumped with
    | [v] => if v != new then throw <| IO.userError s!"failed to update {site.file} (reads '{v}')"
    | _ => throw <| IO.userError s!"failed to update {site.file}"
  IO.println s!"bumped {current} -> {new} in:"
  for site in pkgSites do IO.println s!"  {site.file}"
  IO.println ""
  IO.println s!"next:  git commit -am \"chore: bump version to {new}\" && git tag v{new}"
  IO.println "       (the blueprint's literal is a tracked source input, so its next"
  IO.println s!"        incremental build re-elaborates the document with {new})"
  return 0

def gate (root : System.FilePath) (quiet : Bool) : IO UInt32 := do
  let s ← Snapshot.read root
  let some ver := s.version
    | IO.println s!"FAIL  lean-toolchain is not a pinned release: '{s.toolchain}'"; return 1
  IO.println s!"lean-toolchain: {s.toolchain}  (version {ver})"
  let say (l : String) : IO Unit := if quiet then pure () else IO.println l
  for (ok, l) in siteLines s ver do if ok then say l
  for c in claims s ver do if isExempt c.file then say s!"note  {c.render}"
  let uncl := unclassified s ver
  if !uncl.isEmpty then
    IO.println "\nUnclassified version claims (add to `sites` if they must track the pin,"
    IO.println "or to `exempt` with the reason they are allowed to differ):"
    for c in uncl do IO.println s!"  {c.render}"
  for (ok, l) in statusLines s do if ok then say l
  for (site, vs) in (pkgVersions s).mergeSort (fun a b => a.1.file ≤ b.1.file) do
    if vs.length == 1 then say s!"ok    {site.file}: package version {vs.head!}"
  if plainTermsFails s = [] then
    say s!"ok    {plainTermsFile}: plain-terms bullets name all {(catalogued s).length} catalogued requirements"
  for (ok, l) in rubricLines s do if ok then say l
  for (ok, l) in terminologyLines s do if ok then say l
  for (rel, reason) in exempt do say s!"exempt {rel}: {reason}"
  let fails := failures s ver
  if !fails.isEmpty then
    IO.println "\nFAILED:"
    for f in fails do IO.println s!"  {f}"
    return 1
  IO.println "\nAll version claims agree with lean-toolchain; all blueprint status"
  IO.println "claims agree with the chapter sources; all package-version sites agree;"
  IO.println "the plain-terms bullets name every catalogued requirement; the"
  IO.println "application-template chapters gloss every catalogued rubric; every"
  IO.println "dictionary term is defined once and no retired phrasing survives where"
  IO.println "the gate reads."
  return 0

/-- The package root: `PKC_ROOT`, else the current directory. -/
def findRoot : IO System.FilePath := do
  if let some r ← IO.getEnv "PKC_ROOT" then return r
  return ← IO.currentDir

end Tools.DocPins

open Tools.DocPins in
def main (args : List String) : IO UInt32 := do
  let root ← findRoot
  match args with
  | ["--bump", arg] => bumpTo root arg
  | ["--version"] => bumpTo root ""
  | [] => gate root false
  | ["--quiet"] => gate root true
  | _ =>
    IO.eprintln "usage: doc-pins [--quiet] | --version | --bump +p|+m|+M"
    return 2
