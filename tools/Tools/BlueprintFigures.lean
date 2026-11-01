module

public import Tools.Figures.Lowe
public import Tools.Figures.ThreeLayers
public import Tools.Figures.Cake

/-!
# `blueprint-figures`: the blueprint's three schematics, generated

    lake exe blueprint-figures [--check] [--out DIR] [--logos DIR] [--audience blueprint|deck]

Writes `architecture-cake.svg`, `lowe-square-pkc.svg` and `three-layers-pkc.svg` into `DIR`
(default: `blueprint/figures` of the enclosing checkout), or with `--check` compares what it
would write with what is there, byte for byte, and exits 1 naming each figure that differs.
`--audience deck` writes the deck's cake alone and needs `--out` (the deck's copy lives in its
own repository). Each figure is a pure `String`; `--check` is `decEq` on bytes.
-/

namespace Tools.BlueprintFigures

open Tools.Figures

structure Opts where
  check := false
  out : Option String := none
  logos : Option String := none
  audience := "blueprint"

def parse : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--check" :: r, o => parse r { o with check := true }
  | "--out" :: d :: r, o => parse r { o with out := some d }
  | "--logos" :: d :: r, o => parse r { o with logos := some d }
  | "--audience" :: a :: r, o =>
    if a == "blueprint" || a == "deck" then parse r { o with audience := a }
    else .error s!"--audience: blueprint or deck, not {a}"
  | a :: _, _ => .error s!"unexpected argument {a}"

/-- The enclosing checkout: the nearest ancestor of the working directory with `blueprint/figures/logos`. -/
partial def findRoot (d : System.FilePath) : IO (Option System.FilePath) := do
  if ← (d / "blueprint" / "figures" / "logos").isDir then return some d
  match d.parent with
  | some p => if p == d then return none else findRoot p
  | none => return none

def figures (audience : String) (logos : Cake.Logos) : List (String × String) :=
  if audience == "deck" then [("architecture-cake.svg", Cake.build "deck" logos)]
  else [("architecture-cake.svg", Cake.build "blueprint" logos),
        ("lowe-square-pkc.svg", Lowe.build), ("three-layers-pkc.svg", ThreeLayers.build)]

def main (args : List String) : IO UInt32 := do
  let o ← match parse args {} with
    | .ok o => pure o
    | .error e => do
      IO.eprintln s!"{e}\nusage: blueprint-figures [--check] [--out DIR] [--logos DIR] [--audience blueprint|deck]"
      return 2
  let root ← findRoot (← IO.currentDir)
  let out : System.FilePath ← match o.out with
    | some d => pure d
    | none =>
      if o.audience == "deck" then do
        IO.eprintln "--audience deck needs --out: the deck's copy lives in its own repository"; return 2
      match root with
      | some r => pure (r / "blueprint" / "figures")
      | none => do
        IO.eprintln "not inside a checkout (no blueprint/figures/logos above the working directory); pass --out DIR"
        return 2
  let logosDir : System.FilePath := match o.logos, root with
    | some d, _ => d
    | none, some r => r / "blueprint" / "figures" / "logos"
    | none, none => out / "logos"
  let mut files : List (String × ByteArray) := []
  if ← logosDir.isDir then
    for e in ← logosDir.readDir do
      if ← e.path.isDir then continue
      files := (e.fileName, ← IO.FS.readBinFile e.path) :: files
  let missing := Cake.requiredLogos.filter fun n => files.all (·.1 != n)
  if !missing.isEmpty then
    IO.eprintln s!"missing logo sources in {logosDir}: {", ".intercalate missing}"; return 1
  let logos : Cake.Logos := fun n => (files.find? (·.1 == n)).map (·.2)
  let figs := figures o.audience logos
  let mut changed := 0
  IO.FS.createDirAll out
  for (name, svg) in figs do
    let p := out / name
    let same ← do
      if ← p.pathExists then pure ((← IO.FS.readFile p) == svg) else pure false
    if same then IO.println s!"  unchanged  figures/{name}"; continue
    changed := changed + 1
    if o.check then
      IO.println s!"  DIFFERS    figures/{name}  (run scripts/make-figures.sh and commit the result)"
    else
      IO.FS.writeFile p svg
      IO.println s!"  rewritten  figures/{name}  ({svg.utf8ByteSize} bytes)"
  if o.check then
    if changed > 0 then
      IO.eprintln s!"error: {changed} figure(s) differ from their generators"; return 1
    IO.println s!"figures: all {figs.length} match their generators"
  else if changed > 0 then
    IO.println s!"{changed} figure(s) rewritten"
  return 0

end Tools.BlueprintFigures

public def main (args : List String) : IO UInt32 := Tools.BlueprintFigures.main args
