module

public import Lean

/-!
# `module-census` — the module-system censuses (TOOLS.md §5 step 4)

Replaces `scripts/import-layers.py` and `scripts/module-census.py`: one program, three
instruments over this package's `.lean` files, each attributed to the `lean_lib`/`lean_exe` of
`lakefile.lean` whose `srcDir` and globs cover it.

    lean --run tools/Tools/ModuleCensus.lean --tree [DIR …]        # comment-aware `module` header count per root
    lean --run tools/Tools/ModuleCensus.lean --layers [--tsv PATH] [--max-depth N]
                                                                  # intra-package import graph: depth, dependents, frontier
    lake exe module-census --closure [--names]                    # `isModule` of every olean the sinks load

The bug this exists to catch: the module system is adopted strictly bottom-up (a `module` file
cannot import a non-`module` one), and `grep '^module'` over-reports adoption (23 prose lines in a
package whose true count was 0) while a per-lib view under-reports the frontier. The header is
read with comments and string literals stripped (`stripComments`); a file is a module exactly
when the first token is `module` (`isModule`). Every file under a non-root `srcDir` is attributed
to a lib or reported as an orphan (`place_total`: the attributed and the orphans together are
all the files). The closure census imports every sink module (nothing in the package imports it)
in process and reads `ModuleData.isModule` from each olean of the resulting environment — the
dependency modules it reports block every package module above them.
-/

namespace Tools.ModuleCensus

/-! ## Headers -/

/-- Drop block and line comments; a string literal becomes one space, so a comment opener inside a
string cannot open a phantom comment. -/
partial def stripComments (s : String) : String :=
  go s.toList 0 [] |> List.reverse |> String.ofList
where
  go : List Char → Nat → List Char → List Char
    | [], _, acc => acc
    | '"' :: rest, 0, acc => inString rest acc
    | '/' :: '-' :: rest, d, acc => go rest (d + 1) acc
    | '-' :: '-' :: rest, 0, acc => go (rest.dropWhile (· != '\n')) 0 acc
    | '-' :: '/' :: rest, d + 1, acc => go rest d acc
    | c :: rest, 0, acc => go rest 0 (c :: acc)
    | _ :: rest, d + 1, acc => go rest (d + 1) acc
  inString : List Char → List Char → List Char
    | [], acc => acc
    | '\\' :: _ :: rest, acc => inString rest acc
    | '"' :: rest, acc => go rest 0 (' ' :: acc)
    | _ :: rest, acc => inString rest acc

def tokens (s : String) : List String :=
  ((s.splitOn " ").flatMap fun t => (t.splitOn "\n").flatMap fun u => (u.splitOn "\t").flatMap (·.splitOn "\r"))
    |>.filter (· ≠ "")

/-- A file is a `module` file exactly when the first token outside comments is `module`. -/
def isModule (toks : List String) : Bool := toks.head? == some "module"

/-- The imports of the header: after an optional `module`, `(public|meta|private)* import (all)? NAME`
until the first other token. -/
def imports (toks : List String) : List String :=
  go (if isModule toks then toks.tail else toks) []
where
  go : List String → List String → List String
    | [], acc => acc.reverse
    | t :: rest, acc =>
      if t == "public" || t == "meta" || t == "private" then go rest acc
      else if t == "import" then
        match rest with
        | "all" :: n :: rest' => go rest' (strip n :: acc)
        | n :: rest' => go rest' (strip n :: acc)
        | [] => acc.reverse
      else acc.reverse
  strip (n : String) : String := String.ofList ((n.toList.dropWhile (· == '«')).reverse.dropWhile (· == '»') |>.reverse)

structure Header where
  imports : List String
  isModule : Bool

def header (text : String) : Header :=
  let toks := tokens (stripComments text)
  { imports := imports toks, isModule := isModule toks }

/-! ## The libs of `lakefile.lean` -/

inductive Pat where
  | sub (prefix_ : String)
  | one (name : String)
  deriving Repr, BEq

structure Lib where
  name : String
  srcDir : String
  pats : List Pat
  isExe : Bool
  deriving Repr

def Pat.covers : Pat → String → Bool
  | .sub p, n => n == p || n.startsWith (p ++ ".")
  | .one p, n => n == p

def covered (name : String) (pats : List Pat) : Bool := pats.any (·.covers name)

def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'

/-- The identifier after `key` in `text` (`` `Name `` after `.andSubmodules`, `.one`, `root :=`). -/
def backtickedAfter (text key : String) : List String :=
  ((text.splitOn key).tail).filterMap fun t =>
    let t := (t.dropWhile Char.isWhitespace).toString
    if t.startsWith "`" then
      let n := ((t.drop 1).takeWhile isNameChar).toString
      if n.isEmpty then none else some n
    else none

/-- `lakefile.lean` as the Python read it: blocks starting at `lean_lib`/`lean_exe` lines, the body
up to the first blank line; `srcDir := "…"` (default `.`); globs from `.andSubmodules` and `.one`,
else `roots := #[…]`'s first, else the lib's name; an exe's one root. -/
def libsOf (lakefile : String) : List Lib :=
  let ls := lakefile.splitOn "\n"
  let starts := ls.zipIdx.filterMap fun (l, i) =>
    if l.startsWith "lean_lib " || l.startsWith "lean_exe " then some i else none
  starts.filterMap fun i =>
    let block := (ls.drop i)
    let body := block.takeWhile (· != "")
    let text := String.intercalate "\n" body
    let first := ls[i]!
    let isExe := first.startsWith "lean_exe "
    let rest := (first.drop 9).toString |> fun s => (s.dropWhile Char.isWhitespace).toString
    let rest := (rest.dropWhile (· == '«')).toString
    let name := (rest.takeWhile fun c => c.isAlphanum || c == '_' || c == '.' || c == '-').toString
    if name.isEmpty then none else
    let srcDir := match (text.splitOn "srcDir").tail.head? with
      | some t =>
        match (t.splitOn "\"") with
        | _ :: d :: _ => d
        | _ => "."
      | none => "."
    let pats := (backtickedAfter text ".andSubmodules").map Pat.sub ++ (backtickedAfter text ".one").map Pat.one
    let pats := if pats.isEmpty then
        match (text.splitOn "roots").tail.head? with
        | some t =>
          match (t.splitOn "`").tail.head? with
          | some n => [Pat.sub ((n.takeWhile isNameChar).toString)]
          | none => [Pat.sub name]
        | none => [Pat.sub name]
      else pats
    let pats := if isExe then
        match backtickedAfter text "root :=" with
        | r :: _ => [Pat.one r]
        | [] => [Pat.one name]
      else pats
    some { name, srcDir, pats, isExe }

def skipDirs : List String := [".lake", "blueprint", "Scratch", "scripts", "docs", "References", "__pycache__"]


/-! ## Files and their libs -/

structure Mod where
  name : String
  lib : String
  path : String  -- root-relative
  deriving Repr, Inhabited

/-- Every `.lean` file under `dir` (root-relative paths), `skipDirs` pruned, `lakefile.lean` left out,
sorted. -/
partial def leanFiles (root : System.FilePath) (dir : String) : IO (List String) := do
  let d := if dir == "." then root else root / dir
  if !(← d.isDir) then return []
  let files ← d.walkDir fun p => pure !(skipDirs.contains (p.fileName.getD ""))
  let rel := files.filterMap fun p =>
    if p.extension == some "lean" && p.fileName != some "lakefile.lean" then
      let s := p.toString
      let r := root.toString
      some (if s.startsWith (r ++ "/") then (s.drop (r.length + 1)).toString else s)
    else none
  return (rel.qsort (· < ·)).toList

def moduleName (srcDir rel : String) : String :=
  let inner := if srcDir == "." then rel else (rel.drop (srcDir.length + 1)).toString
  String.intercalate "." (((inner.take (inner.length - 5)).toString).splitOn "/")

/-- Where one file goes: to the first lib whose `srcDir` and globs cover it, else an orphan — or,
under the root `srcDir` (which holds every other `srcDir` too), silently dropped. -/
inductive Placed where
  | lib (m : Mod) (exeOnly : Bool)
  | orphan (rel : String)
  | rootDropped
  deriving Repr

def place (libs : List Lib) (src rel : String) : Placed :=
  let name := moduleName src rel
  match libs.filter fun l => l.srcDir == src && covered name l.pats with
  | [] => if src == "." then .rootDropped else .orphan rel
  | o :: rest => .lib { name, lib := o.name, path := rel } ((o :: rest).all (·.isExe))

/-- Every file of a non-root `srcDir` is attributed to a lib or reported as an orphan: none is
dropped, so a path that drifted out of every lib's glob is named. -/
theorem place_total (libs : List Lib) (src rel : String) (hs : src ≠ ".") :
    (∃ m e, place libs src rel = .lib m e ∧ m.path = rel) ∨ place libs src rel = .orphan rel := by
  unfold place
  rcases hf : libs.filter (fun l => l.srcDir == src && covered (moduleName src rel) l.pats)
    with _ | ⟨o, rest⟩
  · right; simp [hf, hs]
  · left; exact ⟨{ name := moduleName src rel, lib := o.name, path := rel },
      o.isExe && rest.all (·.isExe), by simp [hf], rfl⟩

/-- Attribute every file of every `srcDir`: `(modules, orphans, exe-only names, duplicate
warnings)`; a later file of an already-seen module name replaces it, and is warned about. -/
def attributeFiles (libs : List Lib) (files : List (String × List String)) :
    List Mod × List String × List String × List String :=
  files.foldl (init := ([], [], [], [])) fun acc (src, rels) =>
    rels.foldl (init := acc) fun (mods, orphans, exeOnly, dups) rel =>
      match place libs src rel with
      | .rootDropped => (mods, orphans, exeOnly, dups)
      | .orphan r => (mods, orphans ++ [r], exeOnly, dups)
      | .lib m e =>
        let dups := match mods.find? (·.name == m.name) with
          | some m' => if m'.path != rel then dups ++ [s!"DUPLICATE module name {m.name}: {m'.path} and {rel}"] else dups
          | none => dups
        ((mods.filter (·.name != m.name)) ++ [m], orphans, if e then exeOnly ++ [m.name] else exeOnly, dups)

/-! ## The layers -/

structure Graph where
  mods : List Mod
  edges : List (String × List String)   -- intra-package imports
  isMod : List (String × Bool)

def Graph.imports (g : Graph) (n : String) : List String := ((g.edges.find? (·.1 == n)).map (·.2)).getD []
def Graph.isModule (g : Graph) (n : String) : Bool := ((g.isMod.find? (·.1 == n)).map (·.2)).getD false

def readGraph (root : System.FilePath) (mods : List Mod) : IO Graph := do
  let names := mods.map (·.name)
  let mut edges := []
  let mut isMod := []
  for m in mods do
    let h := header (← IO.FS.readFile (root / m.path))
    edges := edges ++ [(m.name, h.imports.filter names.contains)]
    isMod := isMod ++ [(m.name, h.isModule)]
  return { mods, edges, isMod }

/-- Longest import path below each module (`0` imports nothing of the package); `none` on a cycle. -/
partial def depths (g : Graph) : Except String (List (String × Nat)) := do
  let mut memo : List (String × Nat) := []
  let rec go (n : String) (stack : List String) (memo : List (String × Nat)) : Except String (Nat × List (String × Nat)) := do
    match memo.find? (·.1 == n) with
    | some (_, d) => return (d, memo)
    | none =>
      if stack.contains n then throw s!"import cycle through {n}"
      let mut best := 0
      let mut memo := memo
      for m in g.imports n do
        let (d, memo') ← go m (n :: stack) memo
        memo := memo'
        best := max best (d + 1)
      return (best, memo ++ [(n, best)])
  for m in g.mods do
    let (_, memo') ← go m.name [] memo
    memo := memo'
  return memo

/-- The modules that import `n`, transitively. -/
partial def dependents (g : Graph) : List (String × Nat) :=
  let rev := g.mods.map fun m => (m.name, (g.edges.filter fun (_, imps) => imps.contains m.name).map (·.1))
  let revOf (n : String) : List String := ((rev.find? (·.1 == n)).map (·.2)).getD []
  let rec td (n : String) (memo : List (String × List String)) : List String × List (String × List String) :=
    match memo.find? (·.1 == n) with
    | some (_, s) => (s, memo)
    | none =>
      let (acc, memo) := (revOf n).foldl (init := ([], memo)) fun (acc, memo) k =>
        let (s, memo) := td k memo
        ((acc ++ [k] ++ s).eraseDups, memo)
      (acc, memo ++ [(n, acc)])
  let (_, memo) := g.mods.foldl (init := ((), [])) fun (_, memo) m => ((), (td m.name memo).2)
  g.mods.map fun m => (m.name, (((memo.find? (·.1 == m.name)).map (·.2)).getD []).length)

/-! ## IO -/

def usage : String :=
  "usage: module-census --tree [DIR …] | --layers [--tsv PATH] [--max-depth N] | --closure [--names]"

def rootDir : IO System.FilePath := do
  let cwd ← IO.currentDir
  unless ← (cwd / "lakefile.lean").pathExists do
    throw <| IO.userError "module-census: run from the repository root"
  return cwd

/-- `--tree`: files whose first token outside comments is `module`, per root. -/
def tree (roots : List String) : IO Unit := do
  for r in roots do
    let rp : System.FilePath := r
    let files ← leanFiles rp "."
    let mut mod := 0
    for f in files do
      if (header (← IO.FS.readFile (rp / f))).isModule then mod := mod + 1
    IO.println s!"{← IO.FS.realPath rp}: {mod}/{files.length} module files"

def loadModules (root : System.FilePath) : IO (List Lib × List Mod × List String × List String) := do
  let libs := libsOf (← IO.FS.readFile (root / "lakefile.lean"))
  let srcs := (libs.map (·.srcDir)).eraseDups.mergeSort (· ≤ ·)
  let files ← srcs.mapM fun src => do pure (src, ← leanFiles root src)
  let (mods, orphans, exeOnly, dups) := attributeFiles libs files
  for d in dups do IO.eprintln d
  return (libs, mods, orphans, exeOnly)

def layers (tsv : Option String) (maxDepth : Option Nat) : IO UInt32 := do
  let root ← rootDir
  let (_, mods, orphans, _) ← loadModules root
  let g ← readGraph root mods
  let ds ← match depths g with
    | .ok d => pure d
    | .error e => do IO.eprintln e; return 1
  let depthOf (n : String) : Nat := ((ds.find? (·.1 == n)).map (·.2)).getD 0
  let tds := dependents g
  let tdOf (n : String) : Nat := ((tds.find? (·.1 == n)).map (·.2)).getD 0
  let frontier := g.mods.filter fun m => !g.isModule m.name && (g.imports m.name).all g.isModule
  let maxD := (g.mods.map fun m => depthOf m.name).foldl max 0
  let withHeader := (g.mods.filter fun m => g.isModule m.name).length
  IO.println s!"modules {g.mods.length}  with module header {withHeader}  max depth {maxD}  orphans (no lib covers) {orphans.length}  migratable-now frontier {frontier.length}"
  let hist := (List.range (maxD + 1)).filterMap fun k =>
    let c := (g.mods.filter fun m => depthOf m.name == k).length
    if c == 0 then none else some s!"{k}:{c}"
  IO.println s!"layer histogram: {String.intercalate " " hist}"
  let libNames := ((g.mods.map (·.lib)).eraseDups).mergeSort (· ≤ ·)
  let per := libNames.map fun l =>
    let ms := g.mods.filter (·.lib == l)
    s!"{l}={(ms.filter fun m => g.isModule m.name).length}/{ms.length}"
  IO.println s!"per lib (files/module): {String.intercalate " " per}"
  for o in orphans do IO.println s!"ORPHAN {o}"
  let sorted := g.mods.mergeSort fun a b => depthOf a.name < depthOf b.name || (depthOf a.name == depthOf b.name && a.name ≤ b.name)
  if let some path := tsv then
    let rows := sorted.map fun m =>
      s!"{depthOf m.name}\t{m.name}\t{m.lib}\t{m.path}\t{if g.isModule m.name then 1 else 0}\t{(g.imports m.name).length}\t{tdOf m.name}"
    IO.FS.writeFile path ("depth\tmodule\tlib\tpath\tmodule_header\tintra_imports\tdependents\n" ++ String.intercalate "\n" rows ++ "\n")
  if let some k := maxDepth then
    for m in sorted do
      if depthOf m.name ≤ k then IO.println s!"{depthOf m.name}\t{m.name}\t{m.path}"
  return 0

open Lean in
unsafe def closureUnsafe (sinks : List String) : IO (Nat × List String) := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (sinks.map fun n => { module := n.toName }).toArray {} (trustLevel := 0) (loadExts := true)
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  let mut non := []
  for i in [0:names.size] do
    if !datas[i]!.isModule then non := non ++ [names[i]!.toString]
  return (names.size, non)

/-- The environment the sinks load: its module count and the modules without the `module` flag. -/
@[implemented_by closureUnsafe] opaque closureData (sinks : List String) : IO (Nat × List String)

/-- `--closure`: import every sink of the package in process; `1` when a dependency module is not a
`module` (it blocks every package module above it). -/
def closure (names : Bool) : IO UInt32 := do
  let root ← rootDir
  let (_, mods, _, exeOnly) ← loadModules root
  let g ← readGraph root mods
  let imported := (g.edges.flatMap (·.2)).eraseDups
  let sinks := (g.mods.filter fun m => !imported.contains m.name && !exeOnly.contains m.name).map (·.name)
  let sinks := sinks.mergeSort (· ≤ ·)
  let (total, non) ← closureData sinks
  let own := non.filter fun n => g.mods.any (·.name == n)
  let dep := non.filter fun n => !g.mods.any (·.name == n)
  IO.println s!"sinks imported {sinks.length}; closure {total} modules; without module flag {non.length} (this package {own.length}, dependencies {dep.length})"
  for n in dep do IO.println s!"DEPENDENCY NON-MODULE {n}"
  if names then
    for n in own.mergeSort (· ≤ ·) do IO.println s!"OWN NON-MODULE {n}"
  return if dep.isEmpty then 0 else 1

structure Opts where
  tree := false
  roots : List String := []
  layers := false
  tsv : Option String := none
  maxDepth : Option Nat := none
  closure := false
  names := false

/-- Mode switches and their options, in any order; a bare word is a `--tree` root. -/
def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--tree" :: r, o => parseArgs r { o with tree := true }
  | "--layers" :: r, o => parseArgs r { o with layers := true }
  | "--closure" :: r, o => parseArgs r { o with closure := true }
  | "--names" :: r, o => parseArgs r { o with names := true }
  | "--tsv" :: p :: r, o => parseArgs r { o with tsv := some p }
  | "--max-depth" :: n :: r, o => match n.toNat? with
    | some k => parseArgs r { o with maxDepth := some k }
    | none => .error s!"--max-depth needs a number, got '{n}'"
  | a :: r, o =>
    if a.startsWith "-" then .error s!"unknown argument '{a}'"
    else parseArgs r { o with roots := o.roots ++ [a] }

/-- The selected instruments run in order (tree, layers, closure); the exit status is the
first nonzero one, so `--tree --closure` still fails on a dependency without the flag. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e => IO.eprintln s!"{usage}\n{e}"; return 2
  | .ok o =>
    if !(o.tree || o.layers || o.closure) then IO.eprintln usage; return 2
    if !o.roots.isEmpty && !o.tree then IO.eprintln s!"{usage}\nroots need --tree"; return 2
    let mut status : UInt32 := 0
    if o.tree then tree (if o.roots.isEmpty then ["."] else o.roots)
    if o.layers then
      let s ← layers o.tsv o.maxDepth
      if status == 0 then status := s
    if o.closure then
      let s ← closure o.names
      if status == 0 then status := s
    return status

end Tools.ModuleCensus

public def main (args : List String) : IO UInt32 := Tools.ModuleCensus.main args
