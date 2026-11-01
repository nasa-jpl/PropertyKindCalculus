module

/-!
# `file-links`: make Verso `html-multi` output navigable over `file://`

    lean --run tools/Tools/FileLinks.lean HTML_MULTI_DIR [--strict]
    lake exe file-links HTML_MULTI_DIR [--strict]

Verso writes every internal link as a *directory* URL with a trailing slash
(`Chapter/#anchor`), resolved through a per-page `<base href>` naming the site root. A web
server maps `Chapter/` to `Chapter/index.html`; a browser opening a `file://` directory URL
shows the folder instead. This pass rewrites the link *targets* to spell out `index.html`:

    Chapter/#anchor            -> Chapter/index.html#anchor
    Chapter/Section/#anchor     -> Chapter/Section/index.html#anchor
    find/?domain=...            -> find/index.html?domain=...
    ./   ./../   ""             -> index.html            (home links: the base is the root)
    #anchor                     -> index.html#anchor     (a root-page anchor)

Left alone: the `<base href>` tag, external and non-navigational schemes (`://`, `mailto:`,
`data:`, `javascript:`), the bare `#` (a script hook), a bare `?query`, and every href that
already names a file (assets, `.html`). Over HTTP `Chapter/index.html` resolves as `Chapter/`
did, so the pass is safe for the served site too.

The path component is handled as a list of `/`-separated segments by `fixSegs`;
`fixSegs_idem` is the idempotence a rerun relies on, and the run also decides it on every
href it rewrites (`fixHref (fixHref h) == fixHref h`), failing loudly if that ever broke.
Every rewritten target is then looked up under `HTML_MULTI_DIR`; a missing one is reported,
and fails the run under `--strict`. The tool imports nothing beyond the core toolchain, so it
runs before anything is built.
-/

namespace Tools.FileLinks

/-- A path segment that only climbs or stays: `.` or `..`. -/
def isDots (s : String) : Bool := s == "." || s == ".."

/-- The rewrite on a path's `/`-separated segments. A directory path ends in the empty
segment; one made only of dots is a home link. Anything else is a file and stays. -/
def fixSegs (segs : List String) : List String :=
  match segs.getLast? with
  | some "" =>
      let dir := segs.dropLast
      if dir ≠ [] ∧ dir.all isDots then ["index.html"] else dir ++ ["index.html"]
  | _ => segs

theorem fixSegs_idem (s : List String) : fixSegs (fixSegs s) = fixSegs s := by
  by_cases h : s.getLast? = some ""
  · have hs : fixSegs s =
        (if s.dropLast ≠ [] ∧ s.dropLast.all isDots then ["index.html"]
         else s.dropLast ++ ["index.html"]) := by
      simp [fixSegs, h]
    rw [hs]; split <;> simp [fixSegs]
  · have hs : fixSegs s = s := by
      unfold fixSegs; split <;> simp_all
    rw [hs, hs]

/-- `(path, suffix)`: the href up to its first `#` or `?`, and the rest. -/
def splitSuffix (v : String) : String × String :=
  let cs := v.toList
  let path := cs.takeWhile fun c => c != '#' && c != '?'
  (String.ofList path, String.ofList (cs.drop path.length))

/-- An external or non-navigational href. -/
def hasScheme (v : String) : Bool :=
  (v.splitOn "://").length > 1 ||
    ["mailto", "data", "javascript"].contains ((v.splitOn ":").headD v)

/-- The rewrite of one href value (`fix_href` of the Python pass, rule for rule). -/
def fixHref (v : String) : String :=
  if v.isEmpty then "index.html"
  else if v == "#" then v
  else if v.startsWith "#" then "index.html" ++ v
  else if hasScheme v then v
  else
    let (path, suffix) := splitSuffix v
    if path.isEmpty then v
    else String.intercalate "/" (fixSegs (path.splitOn "/")) ++ suffix

/-- The rewritten page and the hrefs it rewrote (old, new). `href="…"` not preceded by
`<base ` is a link; the `<base>` itself must stay a directory. -/
def rewriteHtml (html : String) : String × List (String × String) :=
  match html.splitOn "href=\"" with
  | [] => (html, [])
  | first :: pieces =>
    let step (acc : String × List (String × String) × String) (piece : String) :=
      let (out, done, prev) := acc
      match piece.splitOn "\"" with
      | value :: rest =>
        if prev.endsWith "<base " then (out ++ "href=\"" ++ piece, done, piece)
        else
          let new := fixHref value
          let done := if new == value then done else (value, new) :: done
          (out ++ "href=\"" ++ new ++ "\"" ++ String.intercalate "\"" rest, done, piece)
      | [] => (out ++ "href=\"" ++ piece, done, piece)
    let (out, done, _) := pieces.foldl step (first, [], first)
    (out, done.reverse)

partial def htmlFiles (dir : System.FilePath) (rel : String) : IO (List String) := do
  let mut out := []
  for e in ← (dir / rel).readDir do
    let r := if rel == "." then e.fileName else rel ++ "/" ++ e.fileName
    if (← (dir / r).isDir) then out := out ++ (← htmlFiles dir r)
    else if e.fileName.endsWith ".html" then out := r :: out
  return out

/-- Where a rewritten target lives under the site root (the `<base>` is the root). -/
def targetFile (new : String) : String :=
  let (path, _) := splitSuffix new
  String.intercalate "/" ((path.splitOn "/").filter fun s => !s.isEmpty && !isDots s)

def main (args : List String) : IO UInt32 := do
  let strict := args.contains "--strict"
  match args.filter (· != "--strict") with
  | [root] =>
    let dir : System.FilePath := root
    if !(← dir.isDir) then
      IO.eprintln s!"not a directory: {root}"; return 1
    let mut changed := 0
    let mut missing : List (String × String) := []
    for f in (← htmlFiles dir ".").mergeSort (· ≤ ·) do
      let text ← IO.FS.readFile (dir / f)
      let (new, done) := rewriteHtml text
      for (old, n) in done do
        if fixHref n != n then
          IO.eprintln s!"file-links: rewrite not idempotent on {f}: {old} -> {n} -> {fixHref n}"
          return 1
        if !(← (dir / targetFile n).pathExists) then missing := (f, n) :: missing
      if new != text then
        IO.FS.writeFile (dir / f) new; changed := changed + 1
    IO.println s!"file-links: rewrote directory links in {changed} html file(s) under {root}"
    if !missing.isEmpty then
      IO.eprintln s!"file-links: {missing.length} rewritten target(s) name no file under {root}:"
      for (f, n) in missing.reverse.take 20 do IO.eprintln s!"  {f}: {n}"
      if strict then return 1
    return 0
  | _ =>
    IO.eprintln "usage: file-links HTML_MULTI_DIR [--strict]"; return 2

end Tools.FileLinks

public def main (args : List String) : IO UInt32 := Tools.FileLinks.main args
