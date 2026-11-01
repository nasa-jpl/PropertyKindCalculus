module

public import Lean.Data.Json.Parser

/-!
# `inject-index-docs` — the API-site post-pass (TOOLS.md §5 step 3)

Replaces `scripts/inject-index-docs.py`. `scripts/emit-index-json.lean` writes one HTML block per
declaration (`.lake/build/pkc-index.json`, name → block); doc-gen4 writes the API pages; this pass
splices each block into the page of the declaration it names, at the end of that declaration's
`<div class="decl" id="<name>" …>`, and adds the blocks' stylesheet to each page it changed.

    lean --run tools/Tools/InjectIndexDocs.lean <site-dir> <blocks.json>

Why a post-pass and not a docstring: `addDocStringCore` refuses an imported declaration, and the
facts a block reports (which crossings mint a kind, which theorems mention it) are declared in
modules later than the kind. The pass knows nothing of the calculus; it knows where a declaration's
div ends (`endOfDecl`, depth-counted, since the div nests arbitrarily).

A declaration without a page is reported, not an error: the API site publishes the Mathlib-free
tier only, so a kind outside it has no page (`unresolved`, printed as a count and the first names).

Idempotence is the property the pass rests on: a block carries `class="pkc-index"`, and a
declaration whose div already holds one is skipped — `inject_twice`: injecting a block into a
page that already carries it changes nothing, so a rerun over pages doc-gen4 left in place (its
`*_built` markers current) is safe. Imports only `Lean`, so it runs on the bare toolchain.
-/

namespace Tools.InjectIndexDocs

def marker : String := "class=\"pkc-index\""

def style : String :=
  "<style id=\"pkc-index-style\">" ++
  ".pkc-index{margin-top:.75em;padding:.4em .75em;border-left:3px solid #999}" ++
  ".pkc-index p{margin:.3em 0}" ++
  ".pkc-index ul{margin:.2em 0 .5em 1.3em}" ++
  "</style>"

def count (hay needle : String) : Nat := (hay.splitOn needle).length - 1

/-- `(before, after)` around the first `needle`. -/
def splitOnce (s needle : String) : Option (String × String) :=
  match s.splitOn needle with
  | [_] => none
  | a :: rest => some (a, String.intercalate needle rest)
  | [] => none

/-- The opening tag `<div class="decl" id="<name>"…>` of a declaration: `(before, tag, after)`. -/
def declOpen (html name : String) : Option (String × String × String) := do
  let (before, rest) ← splitOnce html s!"<div class=\"decl\" id=\"{name}\""
  let (attrs, after) ← splitOnce rest ">"
  if attrs.contains '<' then none
  return (before, s!"<div class=\"decl\" id=\"{name}\"{attrs}>", after)

/-- The text of the declaration's div after its opening tag, up to (not including) the `</div>`
that closes it, and the rest from that `</div>`: depth-counted over `<div` and `</div>`. -/
partial def endOfDecl (after : String) : Option (String × String) :=
  go after 1 ""
where
  go (s : String) (depth : Nat) (acc : String) : Option (String × String) :=
    -- the next `<div` or `</div>`, whichever comes first
    let o := (splitOnce s "<div").map fun (a, b) => (a.length, a, b, true)
    let c := (splitOnce s "</div>").map fun (a, b) => (a.length, a, b, false)
    let next := match o, c with
      | some x, some y => some (if x.1 ≤ y.1 then x else y)
      | some x, none => some x
      | none, some y => some y
      | none, none => none
    match next with
    | none => none
    | some (_, a, b, true) => go b (depth + 1) (acc ++ a ++ "<div")
    | some (_, a, b, false) =>
      if depth == 1 then some (acc ++ a, "</div>" ++ b)
      else go b (depth - 1) (acc ++ a ++ "</div>")

/-- Insert `block` at the end of `name`'s declaration div; `(html, injected)`. Not injected when
the page has no such div, the div is unterminated, or it already carries a block. -/
def inject (html name block : String) : String × Bool :=
  match declOpen html name with
  | none => (html, false)
  | some (before, tag, after) =>
    match endOfDecl after with
    | none => (html, false)
    | some (body, rest) =>
      if (count body marker) > 0 then (html, false)
      else (before ++ tag ++ body ++ s!"<div {marker}>{block}</div>" ++ rest, true)

/-- Injecting into a page that already carries the block changes nothing. -/
theorem inject_marked (html name block : String) (hb : ∀ before tag after, declOpen html name = some (before, tag, after) →
    ∀ body rest, endOfDecl after = some (body, rest) → count body marker > 0) :
    inject html name block = (html, false) := by
  unfold inject
  split
  · rfl
  · rename_i before tag after h
    split
    · rfl
    · rename_i body rest h'
      have := hb before tag after h body rest h'
      simp [this]

/-! ## IO -/

open Lean in
/-- `declaration-data.bmp`: declaration name → page (the `docLink` before `#`, without `./`). -/
def pagesOf (data : String) : Except String (List (String × String)) := do
  let j ← Json.parse data
  let decls ← j.getObjVal? "declarations"
  match decls with
  | .obj kvs => kvs.foldl (init := .ok []) fun acc name entry => do
      let acc ← acc
      let link : String ← match ← entry.getObjVal? "docLink" with
        | .str l => pure l
        | _ => throw s!"docLink of {name} is not a string"
      let page : String := (link.splitOn "#").headD link
      let page : String := (page.dropWhile fun c => c == '.' || c == '/').toString
      return acc ++ [(name, page)]
  | _ => throw "declarations is not an object"

open Lean in
def blocksOf (data : String) : Except String (List (String × String)) := do
  match ← Json.parse data with
  | .obj kvs => kvs.foldl (init := .ok []) fun acc name block => do
      let acc ← acc
      match block with
      | .str s => return acc ++ [(name, s)]
      | _ => throw s!"block of {name} is not a string"
  | _ => throw "blocks file is not an object"

def main (args : List String) : IO UInt32 := do
  let [site, blocksPath] := args
    | IO.eprintln "usage: lean --run tools/Tools/InjectIndexDocs.lean <site-dir> <blocks.json>"; return 2
  let site : System.FilePath := site
  let dataPath := site / "declarations" / "declaration-data.bmp"
  unless ← dataPath.pathExists do
    IO.eprintln s!"error: {dataPath} not found — was the doc-gen4 site generated?"; return 1
  let blocks ← match blocksOf (← IO.FS.readFile blocksPath) with
    | .ok b => pure b
    | .error e => do IO.eprintln s!"error: {blocksPath}: {e}"; return 1
  let pages ← match pagesOf (← IO.FS.readFile dataPath) with
    | .ok p => pure p
    | .error e => do IO.eprintln s!"error: {dataPath}: {e}"; return 1
  -- group by page, so each file is read and written once however many declarations it holds
  let mut byPage : List (String × List String) := []
  let mut unresolved : List String := []
  for (name, _) in blocks do
    match pages.find? (·.1 == name) with
    | none => unresolved := unresolved ++ [name]
    | some (_, page) =>
      byPage := match byPage.find? (·.1 == page) with
        | some _ => byPage.map fun (p, ns) => if p == page then (p, ns ++ [name]) else (p, ns)
        | none => byPage ++ [(page, [name])]
  let mut injected := 0
  let mut skipped := 0
  for (page, names) in byPage.mergeSort (·.1 ≤ ·.1) do
    let path := site / page
    unless ← path.pathExists do
      unresolved := unresolved ++ names
      continue
    let mut html ← IO.FS.readFile path
    let mut changed := false
    for name in names do
      let block := ((blocks.find? (·.1 == name)).map (·.2)).getD ""
      let (h, did) := inject html name block
      html := h
      if did then injected := injected + 1; changed := true else skipped := skipped + 1
    if changed then
      if count html "id=\"pkc-index-style\"" == 0 then
        html := match splitOnce html "</head>" with
          | some (a, b) => a ++ style ++ "</head>" ++ b
          | none => html
      IO.FS.writeFile path html
  IO.println s!"index blocks: {injected} injected, {skipped} already present or not found on page, {unresolved.length} unresolved"
  unless unresolved.isEmpty do
    -- not an error: the API site is a subset of the environment (the Mathlib-free tier), so a
    -- kind outside it has no page to inject into
    let sorted := unresolved.mergeSort (· ≤ ·)
    IO.println s!"  not on this site: {String.intercalate ", " (sorted.take 8)}{if sorted.length > 8 then " …" else ""}"
  return 0

end Tools.InjectIndexDocs

public def main (args : List String) : IO UInt32 := Tools.InjectIndexDocs.main args
