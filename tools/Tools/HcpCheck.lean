module

public import Lean

/-!
# `hcp-check` — the HCP ladder's checker (TOOLS.md §5 step 2)

Replaces `HCP/check-hcp.py`. Every chapter of the ladder
(`blueprint/PropertyKindCalculusBlueprint/Chapters/HCP/L<k>_*.lean`) is read with its lesson
(`HCP/L<k>_*.lean`), worksheet (`HCP/Worksheets/L<k>_*.lean`) and SBVR rendering
(`HCP/sbvr/rendered/L<k>.md`), and the checks are decided over that data:

1. front matter: a strict mapping with the required keys, `id` the chapter's `%%% tag`,
   `hcp` the lesson number + 1, `concepts` a list of `{informal, formal, where}`, `state.completed`
   a list, `exercises` the Learning-path table's row count;
2. the chapter's top-level sections, in order; the Synopsis first after the metadata, its four
   subsections in order and non-empty, each vocabulary name in it found in the lesson, each
   Verifiable-properties bullet tagged and anchored, each Errors-prevented bullet anchored;
3. every `Module#anchor` reference resolves to an `-- ANCHOR:` of that module;
4. the chapter's ```` ```anchor name ```` excerpts equal the lesson's anchor blocks on their
   nonblank lines, every source anchor excerpted once (`--fix-excerpts` rewrites them);
5. the worksheet: EXERCISE names the solution's ANCHOR names in order, each closed, with a
   `TODO:`, each guarded error command of the solution present as a commented probe, no
   `#guard_msgs`, every `example` preceded by a comment, the chapter naming both files;
6. the SBVR rendering: every name new at the step is a designation there, or a member or
   reference a definition source cites;
7. with `--sbvr SBVR_CHECK`: the chain checks clean and each rendering is byte-identical to
   `sbvr-check render` (`--fix-sbvr` rewrites them). sbvr-check's output is data; the verdict is
   decided here.

Imports only `Lean`, so `lean --run tools/Tools/HcpCheck.lean` runs on a bare toolchain;
`lake exe hcp-check` is the same program. `errors_nil_iff` is the exit code's theorem.
-/

namespace Tools.HcpCheck

/-! ## Strings -/

def trim (s : String) : String := s.trimAscii.toString
def lines (s : String) : List String := s.splitOn "\n"
def count (hay needle : String) : Nat := (hay.splitOn needle).length - 1
def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'
def isIdentChar (c : Char) : Bool := isWordChar c || c == '\''
def isBlank (s : String) : Bool := s.all fun c => c == ' ' || c == '\t' || c == '\r'
def dropRight (s : String) (n : Nat) : String := (s.take (s.length - n)).toString
def stripCR (s : String) : String := if s.endsWith "\r" then dropRight s 1 else s
def indentOf (s : String) : Nat := (s.takeWhile fun c => c == ' ' || c == '\t').toString.length
def lstrip (s : String) : String := (s.dropWhile fun c => c == ' ' || c == '\t').toString
def rstrip (s : String) : String := s.trimAsciiEnd.toString

/-- `(before, after)` around the first `needle` in `s`. -/
def splitOnce (s needle : String) : Option (String × String) :=
  match s.splitOn needle with
  | [_] => none
  | a :: rest => some (a, String.intercalate needle rest)
  | [] => none

/-- `(?<!\w)name(?!\w)`: `name` occurs in `s` with no word character on either side. -/
def containsIdentifier (s name : String) : Bool :=
  name ≠ "" && go (s.splitOn name)
where
  go : List String → Bool
    | a :: (b :: rest) =>
      ((a.isEmpty || !isWordChar a.back) && (b.isEmpty || !isWordChar b.front)) || go (b :: rest)
    | _ => false

/-- `(?<![\w#])name(?!\w)`: a `#command` occurrence (the `#` is part of `name`). -/
def containsCommand (s name : String) : Bool :=
  name ≠ "" && go (s.splitOn name)
where
  go : List String → Bool
    | a :: (b :: rest) =>
      ((a.isEmpty || (!isWordChar a.back && a.back != '#')) && (b.isEmpty || !isWordChar b.front))
        || go (b :: rest)
    | _ => false

/-- The pieces of `s` between each ``` ` ``` pair, in order. -/
def backticked (s : String) : List String :=
  go (s.splitOn "`").tail
where
  go : List String → List String
    | a :: _ :: rest => a :: go rest
    | _ => []

/-- `` `Mod.ule#anchor` `` as a reference: the module and anchor names. -/
def anchorRefOf (piece : String) : Option (String × String) :=
  match piece.splitOn "#" with
  | [m, a] =>
    if m ≠ "" && a ≠ "" && m.all (fun c => c.isAlphanum || c == '_' || c == '.')
        && a.all (fun c => c.isAlphanum || c == '_' || c == '-') then some (m, a) else none
  | _ => none

/-- The `Mod.ule#anchor` references of `s` with the index of their opening backtick, scanned left
to right as `re.findall` does (a failed candidate advances one character). -/
def anchorRefsAt (s : String) : List (Nat × String × String) :=
  go s.toList 0 (s.length + 1)
where
  go : List Char → Nat → Nat → List (Nat × String × String)
    | _, _, 0 => []
    | [], _, _ => []
    | '`' :: rest, i, fuel + 1 =>
      let piece := rest.takeWhile (· != '`')
      match rest.drop piece.length with
      | '`' :: rest' =>
        match anchorRefOf (String.ofList piece) with
        | some (m, a) => (i, m, a) :: go rest' (i + piece.length + 2) fuel
        | none => go rest (i + 1) fuel
      | _ => go rest (i + 1) fuel
    | _ :: rest, i, fuel + 1 => go rest (i + 1) fuel

def anchorRefs (s : String) : List (String × String) := (anchorRefsAt s).map (·.2)

/-- Python's `repr` of a string: single-quoted unless it holds a `'` and no `"`. -/
def pyRepr (x : String) : String :=
  if x.contains '\'' && !x.contains '"' then "\"" ++ x ++ "\"" else "'" ++ x ++ "'"

def pyList (xs : List String) : String := "[" ++ String.intercalate ", " (xs.map pyRepr) ++ "]"

/-! ## Front matter: the strict mini-YAML of the chapter header -/

inductive Value where
  | str (s : String)
  | nat (n : Nat)
  | list (xs : List String)
  | map (m : List (String × Value))
  | maps (ms : List (List (String × Value)))
  deriving Repr, BEq, Inhabited

abbrev Mapping := List (String × Value)

structure FrontMatterError where
  line : Nat
  message : String
  deriving Repr

abbrev FM := Except FrontMatterError

def fmFail {α : Type} (line : Nat) (msg : String) : FM α := .error ⟨line, msg⟩

def isKeyStart (c : Char) : Bool := c.isAlpha || c == '_'
def isKeyChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-'

/-- `key:` or `key: value`. -/
def parseKeyValue (text : String) (line : Nat) : FM (String × String) := do
  let key := (text.takeWhile isKeyChar).toString
  if key.isEmpty || !isKeyStart key.front then fmFail line "unrecognised key-value entry"
  let rest := (text.drop key.length).toString
  if !rest.startsWith ":" then fmFail line "unrecognised key-value entry"
  let rest := (rest.drop 1).toString
  if rest.isEmpty then return (key, "")
  if !(rest.front == ' ' || rest.front == '\t') then fmFail line "unrecognised key-value entry"
  return (key, lstrip rest)

/-- A plain or quoted scalar; `(value, quoted)`. -/
partial def parseScalar (value : String) (line : Nat) : FM (String × Bool) := do
  let value := trim value
  if value.isEmpty then fmFail line "expected a scalar value"
  let q := value.front
  if q == '\'' || q == '"' then
    if value.length < 2 || value.back != q then fmFail line "unterminated quoted scalar"
    let inner := (value.drop 1).toString |> (dropRight · 1)
    let rec scan : List Char → FM Unit
      | [] => pure ()
      | c :: cs =>
        if q == '\'' && c == '\'' then
          match cs with
          | '\'' :: cs' => scan cs'
          | _ => fmFail line "unexpected text after quoted scalar"
        else if q == '"' && c == '\\' then fmFail line "escape sequences are unsupported"
        else if c == q then fmFail line "unexpected text after quoted scalar"
        else scan cs
    scan inner.toList
    let inner := if q == '\'' then String.intercalate "'" (inner.splitOn "''") else inner
    return (inner, true)
  if "[{|>&*!%@`".contains q then fmFail line "unsupported scalar syntax"
  return (value, false)

/-- `[a, 'b', "c"]`. -/
partial def parseInlineList (value : String) (line : Nat) : FM (List String) := do
  if !value.endsWith "]" then fmFail line "unterminated inline list"
  let inner := (value.drop 1).toString |> (dropRight · 1)
  if (trim inner).isEmpty then return []
  let rec go (cs : List Char) (quote : Option Char) (cur : List Char) (acc : List String) :
      FM (List String) :=
    match cs with
    | [] =>
      if quote.isSome then fmFail line "unterminated quoted list item"
      else pure (acc ++ [String.ofList cur.reverse])
    | c :: rest =>
      match quote with
      | some q =>
        if q == '\'' && c == '\'' then
          match rest with
          | '\'' :: rest' => go rest' quote ('\'' :: '\'' :: cur) acc
          | _ => go rest none (c :: cur) acc
        else if q == '"' && c == '\\' then fmFail line "escape sequences are unsupported"
        else if c == q then go rest none (c :: cur) acc
        else go rest quote (c :: cur) acc
      | none =>
        if c == '\'' || c == '"' then go rest (some c) (c :: cur) acc
        else if c == ',' then go rest none [] (acc ++ [String.ofList cur.reverse])
        else if c == '[' || c == ']' || c == '{' || c == '}' then
          fmFail line "nested inline collections are unsupported"
        else go rest none (c :: cur) acc
  let items ← go inner.toList none [] []
  let items := items.map trim
  if items.any String.isEmpty then fmFail line "empty inline-list item"
  items.mapM fun item => (·.1) <$> parseScalar item line

/-- A scalar or an inline list; `(value, quoted)`. -/
def parseValue (value : String) (line : Nat) : FM (Value × Bool) := do
  let value := trim value
  if value.startsWith "[" then return (.list (← parseInlineList value line), false)
  if value.startsWith "]" then fmFail line "unexpected closing bracket"
  let (s, quoted) ← parseScalar value line
  return (.str s, quoted)

def indentation (line : String) (number : Nat) : FM Nat := do
  let pre := (line.takeWhile fun c => c == ' ' || c == '\t').toString
  if pre.contains '\t' then fmFail number "tabs are unsupported in indentation"
  return pre.length

def addMapping (m : Mapping) (key : String) (v : Value) (line : Nat) : FM Mapping :=
  if m.any (·.1 == key) then fmFail line s!"duplicate key '{key}'" else pure (m ++ [(key, v)])

/-- Numbered lines `(number, text)` of the front matter body. -/
abbrev NLines := List (Nat × String)

/-- An indented block after `key:` — a 2-space mapping, or a list of `- key: value` mappings
with 4-space continuation keys. Returns the value and the remaining lines. -/
partial def parseBlock (ls : NLines) (keyLine : Nat) : FM (Value × NLines) := do
  let ls := ls.dropWhile fun (_, l) => isBlank l
  match ls with
  | [] => fmFail keyLine "expected an indented mapping or list"
  | (number, first) :: _ =>
    if (← indentation first number) != 2 then fmFail number "expected two spaces of indentation"
    if ((first.drop 2).toString).startsWith "- " then
      let rec items (ls : NLines) (cur : Option Mapping) (acc : List Mapping) :
          FM (List Mapping × NLines) := do
        match ls with
        | [] => pure (acc ++ cur.toList, [])
        | (number, line) :: rest =>
          if isBlank line then items rest cur acc
          else
            let spaces ← indentation line number
            if spaces == 0 then pure (acc ++ cur.toList, ls)
            else if spaces == 2 && ((line.drop 2).toString).startsWith "- " then
              let (k, v) ← parseKeyValue ((line.drop 4).toString) number
              let (value, _) ← parseValue v number
              let m ← addMapping [] k value number
              items rest (some m) (acc ++ cur.toList)
            else if spaces == 4 && cur.isSome then
              let (k, v) ← parseKeyValue ((line.drop 4).toString) number
              let (value, _) ← parseValue v number
              let m ← addMapping cur.get! k value number
              items rest (some m) acc
            else fmFail number "unexpected indentation or block-list item"
      let (ms, rest) ← items ls none []
      return (.maps ms, rest)
    else
      let rec mapping (ls : NLines) (acc : Mapping) : FM (Mapping × NLines) := do
        match ls with
        | [] => pure (acc, [])
        | (number, line) :: rest =>
          if isBlank line then mapping rest acc
          else
            let spaces ← indentation line number
            if spaces == 0 then pure (acc, ls)
            else if spaces != 2 || ((line.drop 2).toString).startsWith "- " then
              fmFail number "unexpected indentation in mapping"
            else
              let (k, v) ← parseKeyValue ((line.drop 2).toString) number
              let (value, _) ← parseValue v number
              mapping rest (← addMapping acc k value number)
      let (m, rest) ← mapping ls []
      if m.isEmpty then fmFail keyLine "expected an indented mapping"
      return (.map m, rest)

/-- The document between the `---` delimiters (line numbers from 1). -/
partial def parseFrontMatter (text : String) : FM Mapping := do
  let ls := lines text
  match ls with
  | [] => fmFail 1 "missing opening delimiter"
  | first :: rest =>
    if first != "---" then fmFail 1 "missing opening delimiter"
    let body := rest.takeWhile (· != "---")
    if body.length == rest.length then fmFail ls.length "missing closing delimiter"
    let content : NLines := (body.zipIdx 2).map fun (l, n) => (n, l)
    let rec top (ls : NLines) (acc : Mapping) : FM Mapping := do
      match ls with
      | [] => pure acc
      | (number, line) :: rest =>
        if isBlank line then top rest acc
        else
          if (← indentation line number) != 0 then fmFail number "unexpected top-level indentation"
          let (key, raw) ← parseKeyValue line number
          if acc.any (·.1 == key) then fmFail number s!"duplicate key '{key}'"
          if (trim raw).isEmpty then
            let (v, rest') ← parseBlock rest number
            top rest' (acc ++ [(key, v)])
          else
            let (v, quoted) ← parseValue raw number
            let v := match v with
              | .str s => if !quoted && (key == "hcp" || key == "exercises") && s.isNat then .nat s.toNat! else v
              | _ => v
            top rest (acc ++ [(key, v)])
    top content []

/-- The front matter of a chapter: the first `/-` line to the first `-/` line after it. -/
def parseChapterFrontMatter (text : String) : FM Mapping := do
  let ls := lines text
  let isOpen (l : String) := rstrip l == "/-"
  let isClose (l : String) := rstrip l == "-/"
  match ls.findIdx? isOpen with
  | none => fmFail 1 "missing or unterminated front matter comment"
  | some o =>
    let after := ls.drop (o + 1)
    match after.findIdx? isClose with
    | none => fmFail ls.length "unterminated front matter comment"
    | some c =>
      let inner := after.take c
      let inner := (inner.dropWhile (· == "")).reverse.dropWhile (· == "") |>.reverse
      let leading := (after.take c).takeWhile (· == "") |>.length
      match parseFrontMatter (String.intercalate "\n" inner) with
      | .ok m => pure m
      | .error e => fmFail (o + 1 + leading + e.line) e.message

/-! ## Sections of a chapter -/

def chapterSections : List String :=
  ["Synopsis", "Persona", "Pull", "Risks at this step", "Small rigorous improvement",
   "Learning path", "Lesson", "AI assistance contract", "Questions to ask the model so far",
   "System-context card"]

def synopsisSubsections : List String :=
  ["Purpose", "PKC vocabulary in scope", "Verifiable properties", "Errors prevented"]

def verifiableTags : List String := ["type-checked", "refused", "theorem", "census", "gate"]

def requiredKeys : List String :=
  ["hcp", "id", "persona", "layer", "pull", "improvement", "concepts", "artifacts", "tools",
   "exercises", "disclosure", "owner", "state"]

def conceptKeys : List String := ["informal", "formal", "where"]

/-- A heading line of exactly `level` hashes; its title (trailing blanks removed). -/
def headingOf (level : Nat) (l : String) : Option String :=
  let hashes := String.ofList (List.replicate level '#')
  if l.startsWith (hashes ++ " ") then
    let t := (l.drop (level + 1)).toString
    if t.startsWith "#" || (trim t).isEmpty then none else some (rstrip t)
  else none

/-- The lines from the unique `#{level} title` heading up to the next heading of that level;
`none` unless the heading occurs exactly once. -/
def headingSection (ls : List String) (level : Nat) (title : String) : Option (List String) :=
  let starts := (ls.zipIdx).filter fun (l, _) => headingOf level l == some title
  match starts with
  | [(_, i)] =>
    let rest := ls.drop (i + 1)
    let body := rest.takeWhile fun l => (headingOf level l).isNone
    some (ls[i]! :: body)
  | _ => none

/-- The `%%% … %%%` metadata block: the lines strictly inside, and the index after it. -/
def metadataBlock (ls : List String) : Option (List String × Nat) :=
  let isFence (l : String) := rstrip l == "%%%"
  match ls.findIdx? isFence with
  | none => none
  | some o =>
    let after := ls.drop (o + 1)
    match after.findIdx? isFence with
    | none => none
    | some c => some (after.take c, o + 1 + c + 1)

/-- After the metadata, the first `# ` heading is `# Synopsis` and it is the only one; the lines
from it to the next `# ` heading. -/
def synopsisSection (ls : List String) : Option (List String) := do
  let (_, after) ← metadataBlock ls
  let body := ls.drop after
  let heads := (body.zipIdx).filter fun (l, _) => (headingOf 1 l).isSome
  match heads with
  | [] => none
  | (first, i) :: rest =>
    if headingOf 1 first != some "Synopsis" then none
    else if rest.any (fun (l, _) => headingOf 1 l == some "Synopsis") then none
    else
      let stop := match rest with | (_, j) :: _ => j | [] => body.length
      some ((body.drop i).take (stop - i))

/-- The bullets of a synopsis subsection (`- …`, indented continuation lines joined); non-bullet
lines are errors. -/
def synopsisBullets (path : String) (sec : List String) (label : String) :
    List String × List String :=
  let step := fun (acc : List String × List String) (l : String) =>
    let (bullets, errs) := acc
    if isBlank l then acc
    else if l.startsWith "- " then (bullets ++ [trim ((l.drop 2).toString)], errs)
    else if (l.startsWith "  " || l.startsWith "\t") && !bullets.isEmpty then
      (bullets.dropLast ++ [bullets.getLast! ++ " " ++ trim l], errs)
    else (bullets, errs ++ [s!"{path}: {label} contains a non-bullet line: {pyRepr (trim l)}"])
  let (bullets, errs) := sec.tail.foldl step ([], [])
  (bullets, if bullets.isEmpty then errs ++ [s!"{path}: {label} must contain at least one bullet"] else errs)

/-! ## Vocabulary names and the lesson that must mention them -/

/-- `#cmd` is a command; `@[attr]` names `attr`. -/
def vocabularyName (term : String) : String × Bool :=
  if term.startsWith "#" then (term, true)
  else if term.startsWith "@[" && term.endsWith "]" then (dropRight ((term.drop 2).toString) 1, false)
  else (term, false)

def isDeclKeyword (w : String) : Bool :=
  ["def", "theorem", "lemma", "abbrev", "structure", "class", "inductive", "instance"].contains w
def isModifier (w : String) : Bool := ["private", "protected", "noncomputable"].contains w

def words (l : String) : List String := (l.splitOn " ").flatMap (·.splitOn "\t") |>.filter (· ≠ "")

/-- `(declaration keyword, name)` of a line `[modifiers] kw name …`. -/
def declOf (l : String) : Option (String × String) :=
  let ws := (words l).dropWhile isModifier
  match ws with
  | kw :: name :: _ =>
    if isDeclKeyword kw then
      let n := (name.takeWhile fun c => isIdentChar c || c == '.').toString
      if n ≠ "" && (n.front.isAlpha || n.front == '_') then some (kw, n) else none
    else none
  | _ => none

def isNamespaceLine (l : String) : Option String :=
  match words l with
  | ["namespace", n] => some n
  | _ => none

def isEndLine (l : String) : Option (Option String) :=
  match words l with
  | ["end"] => some none
  | ["end", n] => some (some n)
  | _ => none

/-- `member` is declared in a namespace equal to or ending in `.ns`, or is a field of a
`structure`/`class`/`inductive … where` so named. -/
def declarationInNamespace (source ns member : String) : Bool :=
  let ls := lines source
  let n := ls.length
  let rec go (i : Nat) (stack : List String) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if h : i < n then
        let line := ls[i]
        match isNamespaceLine line with
        | some nsName => go (i + 1) (stack ++ [nsName]) fuel
        | none =>
          match isEndLine line with
          | some closed =>
            let stack' := match closed with
              | none => stack.dropLast
              | some name =>
                match stack.reverse.findIdx? (fun cur => cur == name || cur.endsWith ("." ++ name)) with
                | some k => stack.take (stack.length - k - 1)
                | none => []
            go (i + 1) stack' fuel
          | none =>
            let here := String.intercalate "." stack
            let matchesNs := here == ns || here.endsWith ("." ++ ns)
            match declOf line with
            | some (kw, name) =>
              if matchesNs && name == member then true
              else
                let isAgg := ["structure", "class", "inductive"].contains kw && (words line).getLast? == some "where"
                let aggName := if here.isEmpty then name else here ++ "." ++ name
                if isAgg && (aggName == ns || aggName.endsWith ("." ++ ns)) then
                  let base := indentOf line
                  let fields := (ls.drop (i + 1)).filter (fun l => !(trim l).isEmpty)
                    |>.takeWhile fun l => indentOf l > base
                  let fieldName (l : String) : String :=
                    let t := lstrip l
                    let t := if t.startsWith "|" then lstrip ((t.drop 1).toString) else t
                    (t.takeWhile isIdentChar).toString
                  if fields.any (fun l => fieldName l == member) then true else go (i + 1) stack fuel
                else go (i + 1) stack fuel
            | none => go (i + 1) stack fuel
      else false
  go 0 [] (n + 1)

/-- A term's name is found in the lesson, dotted names also through the package sources
(`PropertyKindCalculus/**`, `ForPhysLib/**`). -/
def containsVocabularyName (lesson : String) (sources : List String) (term : String) : Bool :=
  let (name, command) := vocabularyName term
  if name.isEmpty then false
  else if command then containsCommand lesson name
  else if term.startsWith "@[" && term.endsWith "]" then containsIdentifier lesson name
  else if !name.contains '.' then containsIdentifier lesson name
  else if containsIdentifier lesson name then true
  else
    let parts := name.splitOn "."
    let member := parts.getLast!
    let ns := String.intercalate "." parts.dropLast
    if !containsIdentifier lesson member then false
    else sources.any fun src =>
      containsIdentifier src name || declarationInNamespace src ns member

/-! ## Source anchors and chapter excerpts -/

/-- `-- ANCHOR: name` / `-- ANCHOR_END: name`. -/
def anchorMarker (l : String) : Option (Bool × String) :=
  let t := lstrip (stripCR l)
  if !t.startsWith "--" then none
  else
    let t := lstrip ((t.dropWhile (· == '-')).toString)
    if t.startsWith "ANCHOR_END:" then
      let n := trim ((t.drop "ANCHOR_END:".length).toString)
      if n.isEmpty then none else some (false, n)
    else if t.startsWith "ANCHOR:" then
      let n := trim ((t.drop "ANCHOR:".length).toString)
      if n.isEmpty then none else some (true, n)
    else none

/-- Each anchor's body lines, in order of closing, and the errors. Lines inside several open
anchors belong to each. -/
def sourceAnchors (path : String) (text : String) : List (String × List String) × List String :=
  let ls := lines text
  let step := fun (st : List (String × List String) × List (String × List String) × List String)
      (li : String × Nat) =>
    let (done, opn, errs) := st
    let (line, i) := li
    let n := i + 1
    match anchorMarker line with
    | some (true, name) =>
      if opn.any (·.1 == name) || done.any (·.1 == name) then
        (done, opn, errs ++ [s!"{path}:{n}: duplicate source anchor '{name}'"])
      else (done, opn ++ [(name, [])], errs)
    | some (false, name) =>
      match opn.find? (·.1 == name) with
      | none => (done, opn, errs ++ [s!"{path}:{n}: source anchor end '{name}' has no matching start"])
      | some (_, body) => (done ++ [(name, body)], opn.filter (·.1 != name), errs)
    | none => (done, opn.map (fun (k, b) => (k, b ++ [line])), errs)
  let (done, opn, errs) := ls.zipIdx.foldl step ([], [], [])
  (done, errs ++ opn.map fun (name, _) => s!"{path}: source anchor '{name}' is missing its ANCHOR_END marker")

def nonblankCodeLines (ls : List String) : List String :=
  (ls.filter fun l => !(l.all fun c => [' ', '\t', '\r', '\n', '\x0c', '\x0b'].contains c)).map stripCR

/-- ```` ```anchor name ```` fence header: `(fence, rest)`. -/
def anchorFence (l : String) : Option (String × String) :=
  let t := lstrip (stripCR l)
  let fence := (t.takeWhile (· == '`')).toString
  if fence.length < 3 then none
  else
    let after := (t.drop fence.length).toString
    if after.startsWith "anchor" then
      let rest := (after.drop "anchor".length).toString
      if rest.isEmpty || rest.front == ' ' || rest.front == '\t' then some (fence, rest) else none
    else none

/-- The index of the closing fence at or after `start`. -/
def closingFence (ls : List String) (start : Nat) (fence : String) : Option Nat :=
  let isClose (l : String) :=
    let t := trim (stripCR l)
    t.length ≥ fence.length && t.all (· == '`')
  ((ls.drop start).findIdx? isClose).map (· + start)

/-- `set_option verso.exampleModule "…"` declarations of a chapter. -/
def exampleModules (ls : List String) : List String :=
  ls.filterMap fun l =>
    match words (stripCR l) with
    | ["set_option", "verso.exampleModule", q] =>
      if q.startsWith "\"" && q.endsWith "\"" && q.length ≥ 2 then some (dropRight ((q.drop 1).toString) 1) else none
    | _ => none

def isLeanIdentPath (m : String) : Bool :=
  (m.splitOn ".").all fun p => p ≠ "" && (p.front.isAlpha || p.front == '_') && p.all isWordChar

/-- `Mod.Ule` → `Mod/Ule.lean`. -/
def modulePath (m : String) : String := String.intercalate "/" (m.splitOn ".") ++ ".lean"

/-- One chapter's excerpt check: errors, the chapter lines after `--fix-excerpts` rewrote the
differing excerpts, and whether anything was rewritten. -/
def excerptCheck (chapterPath sourceRel : String) (chapterLines : List String)
    (anchors : List (String × List String)) (fix : Bool) : List String × List String × Bool :=
  let n := chapterLines.length
  let rec go (i : Nat) (errs : List String) (seen : List String)
      (reps : List (Nat × Nat × List String)) (fuel : Nat) :
      List String × List String × List (Nat × Nat × List String) :=
    match fuel with
    | 0 => (errs, seen, reps)
    | fuel + 1 =>
      if h : i < n then
        match anchorFence chapterLines[i] with
        | none => go (i + 1) errs seen reps fuel
        | some (fence, rest) =>
          let ln := i + 1
          match closingFence chapterLines (i + 1) fence with
          | none => (errs ++ [s!"{chapterPath}:{ln}: unterminated anchor code fence"], seen, reps)
          | some cls =>
            let rest := trim rest
            if rest.isEmpty then
              go (cls + 1) (errs ++ [s!"{chapterPath}:{ln}: anchor code fence is missing its name"]) seen reps fuel
            else
              let name := (rest.takeWhile fun c => c != ' ' && c != '\t').toString
              let args := trim ((rest.drop name.length).toString)
              let errs := if seen.contains name then errs ++ [s!"{chapterPath}:{ln}: anchor '{name}' appears more than once"] else errs
              let seen := seen ++ [name]
              if !args.isEmpty then
                go (cls + 1) (errs ++ [s!"{chapterPath}:{ln}: anchor '{name}' has unsupported arguments '{args}'"]) seen reps fuel
              else match anchors.find? (·.1 == name) with
              | none => go (cls + 1) (errs ++ [s!"{chapterPath}:{ln}: anchor '{name}' is missing from {sourceRel}"]) seen reps fuel
              | some (_, expected) =>
                let actual := (chapterLines.drop (i + 1)).take (cls - i - 1)
                let el := nonblankCodeLines expected
                let al := nonblankCodeLines actual
                if el.isEmpty && al.isEmpty then
                  go (cls + 1) (errs ++ [s!"{chapterPath}:{ln}: anchor '{name}' excerpt is empty"]) seen reps fuel
                else if el != al then
                  if fix && !el.isEmpty then
                    go (cls + 1) errs seen (reps ++ [(i + 1, cls, expected.map stripCR)]) fuel
                  else
                    go (cls + 1) (errs ++ [s!"{chapterPath}:{ln}: anchor '{name}' excerpt differs from {sourceRel} (run hcp-check --fix-excerpts)"]) seen reps fuel
                else go (cls + 1) errs seen reps fuel
      else (errs, seen, reps)
  let (errs, seen, reps) := go 0 [] [] [] (n + 1)
  let errs := errs ++ (anchors.filter fun (name, _) => !seen.contains name).map fun (name, _) =>
    s!"{chapterPath}: source anchor '{name}' from {sourceRel} has no excerpt in this chapter"
  let fixed := reps.reverse.foldl (fun (cl : List String) (r : Nat × Nat × List String) =>
    let (start, stop, repl) := r
    cl.take start ++ repl ++ cl.drop stop) chapterLines
  (errs, fixed, !reps.isEmpty)

/-! ## Worksheets and commented probes -/

def normalizeProbeLine (l : String) : String := String.intercalate " " (words l)

def isGuardLine (l : String) : Bool :=
  let t := lstrip l
  t.startsWith "#guard_msgs" &&
    (let r := (t.drop "#guard_msgs".length).toString; r.isEmpty || !isWordChar r.front)

/-- `error:` as a word in the doc comment before a guard. -/
def mentionsError (l : String) : Bool :=
  (l.splitOn "error:").dropLast.any fun a => a.isEmpty || !isWordChar a.back

/-- The `#guard_msgs` commands whose expected message is an error: each a list of normalized
lines. -/
def errorGuardCommands (block : String) : List (List String) :=
  let ls := lines block
  let guards := ls.zipIdx.filterMap fun (l, i) => if isGuardLine l then some i else none
  let hasError (from_ to : Nat) : Bool := ((ls.drop from_).take (to - from_)).any mentionsError
  let rec collect (gs : List Nat) (prevEnd : Nat) (acc : List (List String)) : List (List String) :=
    match gs with
    | [] => acc
    | g :: rest =>
      let acc :=
        if hasError prevEnd g then
          let gl := ls[g]!
          let inlineCmd :=
            let after := ((lstrip gl).drop "#guard_msgs".length).toString
            match splitOnce (" " ++ after ++ " ") " in " with
            | some (_, c) => trim c
            | none => ""
          let nextGuard := match rest with | h :: _ => h | [] => ls.length
          let body := (ls.drop (g + 1)).take (nextGuard - g - 1)
          let rec take (bs : List String) (acc : List String) : List String :=
            match bs with
            | [] => acc
            | l :: bs' =>
              if (trim l).isEmpty then (if acc.isEmpty then take bs' acc else acc)
              else if isGuardLine l then acc
              else take bs' (acc ++ [trim l])
          let cmd := take body (if inlineCmd.isEmpty then [] else [inlineCmd])
          acc ++ [if cmd.isEmpty then ["<empty command>"] else cmd.map normalizeProbeLine]
        else acc
      collect rest (g + 1) acc
  collect guards 0 []

def probeStarters : List String :=
  ["example", "def", "theorem", "lemma", "abbrev", "structure", "class", "inductive", "instance"]

/-- `-- (modifier )*(example|def|…|#)…` starts a commented probe. -/
def isCommentedProbeStart (l : String) : Bool :=
  if !l.startsWith "-- " then false
  else
    let ws := (words ((l.drop 3).toString)).dropWhile fun w =>
      ["noncomputable", "private", "protected", "unsafe", "partial"].contains w
    match ws with
    | w :: _ => w.startsWith "#" || probeStarters.any fun k =>
        w == k || (w.startsWith k && !isWordChar (w.drop k.length).toString.front)
    | [] => false

/-- The commented probes of a worksheet block: runs of `-- ` lines starting at a probe start. -/
def commentedProbeCommands (block : String) : List (List String) :=
  let step := fun (st : List (List String) × List String) (l : String) =>
    let (probes, cur) := st
    let finish := if cur.isEmpty then probes else probes ++ [cur.map normalizeProbeLine]
    if l.startsWith "-- EXERCISE:" || l.startsWith "-- EXERCISE_END:" || l.startsWith "-- @[" then (finish, [])
    else if isCommentedProbeStart l then (finish, [(l.drop 3).toString])
    else if !cur.isEmpty && l.startsWith "-- " then (probes, cur ++ [(l.drop 3).toString])
    else (finish, [])
  let (probes, cur) := (lines block).foldl step ([], [])
  if cur.isEmpty then probes else probes ++ [cur.map normalizeProbeLine]

def exampleMarkers : List String :=
  ["-- ANCHOR:", "-- ANCHOR_END:", "-- EXERCISE:", "-- EXERCISE_END:", "-- TODO:", "-- GIVEN:"]

/-- `^\s*(?:#guard_msgs\b.*?\bin\s+)?(?:noncomputable\s+)?example\b`. -/
def isExampleDeclaration (l : String) : Bool :=
  let t := lstrip l
  let t := if isGuardLine t then
      match splitOnce (" " ++ t ++ " ") " in " with
      | some (_, r) => lstrip r
      | none => "\x00"
    else t
  let t := if t.startsWith "noncomputable " then lstrip ((t.drop "noncomputable".length).toString) else t
  t.startsWith "example" && (t.length == "example".length || !isWordChar (t.drop "example".length).toString.front)

/-- The index of the line preceding the `example` at `i`, skipping `#guard_msgs` lines above it
and a docstring ending just above. -/
def precedingLine (ls : List String) (i : Nat) : Option Nat :=
  let rec skipGuards (j : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if isGuardLine ls[j]! then (if j == 0 then none else skipGuards (j - 1) fuel) else some j
  let rec toOpen (j : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if (ls[j]!.splitOn "/--").length > 1 then (if j == 0 then none else some (j - 1))
      else if j == 0 then none else toOpen (j - 1) fuel
  if i == 0 then none
  else
    let j := i - 1
    let j := if isGuardLine ls[i]! then some j else skipGuards j (j + 1)
    match j with
    | none => none
    | some j => if (rstrip ls[j]!).endsWith "-/" then toOpen j (j + 1) else some j

/-- Every `example` must be preceded by a `-- ` comment (docstrings and `#guard_msgs` skipped). -/
def exampleCommentErrors (path : String) (text : String) : List String :=
  let ls := lines text
  ls.zipIdx.filterMap fun (l, i) =>
    if !isExampleDeclaration l then none
    else
      let precLine := match precedingLine ls i with | some j => lstrip ls[j]! | none => ""
      let hasComment := precLine.startsWith "-- " && !exampleMarkers.any fun m => precLine.startsWith m
      if hasComment then none else some s!"{path}:{i + 1}: example has no preceding comment saying what it shows"


/-! ## The snapshot a run decides over -/

structure Snapshot where
  /-- root-relative path → contents, for every file a check may read -/
  files : List (String × String)
  /-- the chapters, sorted by path -/
  chapters : List String
  /-- the vocabulary sources (`PropertyKindCalculus/**`, `ForPhysLib/**`), their texts -/
  vocabSources : List String
  deriving Inhabited

def Snapshot.read? (s : Snapshot) (p : String) : Option String := (s.files.find? (·.1 == p)).map (·.2)
def Snapshot.has (s : Snapshot) (p : String) : Bool := s.files.any (·.1 == p)

def fileName (p : String) : String := (p.splitOn "/").getLast!
def chapterDir : String := "blueprint/PropertyKindCalculusBlueprint/Chapters/HCP"
def sbvrChain : String := "HCP/sbvr/physlib-contributor.yaml"
def sbvrRenderedDir : String := "HCP/sbvr/rendered"
def sbvrFoundation : String := "PKC"


def pyShow : Option Value → String
  | none => "None"
  | some (.nat n) => toString n
  | some (.str s) => s
  | some (.list xs) => pyList xs
  | some (.map _) => "{…}"
  | some (.maps _) => "[…]"

def sortStrings (xs : List String) : List String := xs.mergeSort (· ≤ ·)

/-- `L<k>_<Name>` with k in 0..6 → k. -/
def stepOf (body : String) : Option Nat :=
  match body.toList with
  | 'L' :: d :: '_' :: rest =>
    if d.isDigit && d.toNat - '0'.toNat ≤ 6 && !rest.isEmpty && rest.all isWordChar then
      some (d.toNat - '0'.toNat) else none
  | _ => none

def chapterNumber (name : String) : Option Nat :=
  if name.endsWith ".lean" then stepOf (dropRight name 5) else none

def lessonNumber (m : String) : Option Nat :=
  if m.startsWith "HCP." then stepOf ((m.drop 4).toString) else none

/-- `tag := "<id>"` in the metadata block. -/
def tagOf (metaLines : List String) : Option String :=
  metaLines.findSome? fun l =>
    let l := rstrip l
    if l.startsWith "tag := \"" && l.endsWith "\"" && l.length > 9 then
      let inner := dropRight ((l.drop 8).toString) 1
      if inner.isEmpty || inner.contains '"' then none else some inner
    else none

/-- The `:::table +header` … `:::` blocks of a section (an unterminated one is not a block). -/
def learningTables (sec : List String) : List (List String) :=
  let step := fun (st : Option (List String) × List (List String)) (l : String) =>
    match st with
    | (none, tabs) => if rstrip l == ":::table +header" then (some [], tabs) else (none, tabs)
    | (some cur, tabs) => if rstrip l == ":::" then (none, tabs ++ [cur]) else (some (cur ++ [l]), tabs)
  (sec.foldl step (none, [])).2

def tableRows (t : List String) : Nat := (t.filter fun l => rstrip l == "*").length - 1

/-- `\(([a-z-]+)\)` occurrences: `(start, end, tag)` by character index. -/
def parenTags (b : String) : List (Nat × Nat × String) :=
  go b.toList 0 (b.length + 1)
where
  go : List Char → Nat → Nat → List (Nat × Nat × String)
    | _, _, 0 => []
    | [], _, _ => []
    | '(' :: rest, i, fuel + 1 =>
      let tag := rest.takeWhile fun c => c.isLower || c == '-'
      match rest.drop tag.length with
      | ')' :: rest' =>
        if tag.isEmpty then go rest (i + 1) fuel
        else (i, i + tag.length + 2, String.ofList tag) :: go rest' (i + tag.length + 2) fuel
      | _ => go rest (i + 1) fuel
    | _ :: rest, i, fuel + 1 => go rest (i + 1) fuel

/-- Only whitespace between character indices `a` and `b` of `s`. -/
def blankBetween (s : String) (a b : Nat) : Bool :=
  ((s.toList.drop a).take (b - a)).all fun c => c == ' ' || c == '\t'

def synopsisErrors (path : String) (ls : List String) (lesson : Option (String × String))
    (sources : List String) : List String :=
  match synopsisSection ls with
  | none => [s!"{path}: Synopsis must be first after %%% metadata"]
  | some syn =>
    let subs := syn.zipIdx.filterMap fun (l, i) => (headingOf 2 l).map (·, i)
    let names := subs.map (·.1)
    let e1 := if names != synopsisSubsections then
      [s!"{path}: Synopsis subsections must be exactly {pyList synopsisSubsections} in order"] else []
    let e2 := (subs.zipIdx).filterMap fun ((name, i), k) =>
      let stop := match subs[k + 1]? with | some (_, j) => j | none => syn.length
      if ((syn.drop (i + 1)).take (stop - i - 1)).all isBlank then
        some s!"{path}: Synopsis subsection '{name}' is empty" else none
    let e3 := match headingSection syn 2 "PKC vocabulary in scope" with
      | none => [s!"{path}: missing or duplicate 'PKC vocabulary in scope' subsection"]
      | some vocab =>
        let newErrs := match vocab.findIdx? (fun l => rstrip l == "New at this step:") with
          | none => [s!"{path}: vocabulary section is missing 'New at this step:'"]
          | some i =>
            if (vocab.drop (i + 1)).any (fun l => l.startsWith "- " && l.length > 2) then []
            else [s!"{path}: 'New at this step:' must be followed by a list"]
        let lessonErrs := match lesson with
          | none => [s!"{path}: could not map chapter to its HCP lesson"]
          | some (lp, ltext) =>
            ((backticked (String.intercalate "\n" vocab)).filter (· ≠ "")).filterMap fun term =>
              if containsVocabularyName ltext sources term then none
              else some s!"{path}: vocabulary term '{term}' not found in {fileName lp}"
        newErrs ++ lessonErrs
    let e4 := match headingSection syn 2 "Verifiable properties" with
      | none => []
      | some sec =>
        let (bullets, errs) := synopsisBullets path sec "Verifiable properties"
        errs ++ (bullets.zipIdx 1).flatMap fun (b, i) =>
          let tags := parenTags b
          let firstRef := (anchorRefsAt b).head?.map (·.1)
          let before := match tags, firstRef with
            | [(_, e, _)], some r => e ≤ r && blankBetween b e r
            | _, _ => false
          let tagOk := match tags with
            | [(_, _, t)] => verifiableTags.contains t && before
            | _ => false
          (if tagOk then [] else
            [s!"{path}: Verifiable-properties bullet {i} must have exactly one parenthesized lowercase tag from {pyList (sortStrings verifiableTags)} immediately before its first Module#anchor ref"])
          ++ (if firstRef.isNone then [s!"{path}: Verifiable-properties bullet {i} is missing a Module#anchor ref"] else [])
    let e5 := match headingSection syn 2 "Errors prevented" with
      | none => []
      | some sec =>
        let (bullets, errs) := synopsisBullets path sec "Errors prevented"
        errs ++ (bullets.zipIdx 1).filterMap fun (b, i) =>
          if (anchorRefs b).isEmpty then some s!"{path}: Errors-prevented bullet {i} is missing a Module#anchor ref" else none
    e1 ++ e2 ++ e3 ++ e4 ++ e5

/-- `-- <prefix> <name>` with `name` in `[A-Za-z0-9_-]+` and only blanks after. -/
def markerName (pre : String) (l : String) : Option String :=
  if l.startsWith pre then
    let n := rstrip ((l.drop pre.length).toString)
    if n ≠ "" && n.all (fun c => c.isAlphanum || c == '_' || c == '-') then some n else none
  else none

/-- The worksheet of a lesson: EXERCISE names, closings, TODOs, commented probes, no
`#guard_msgs`, and the Learning path naming both files. -/
def worksheetErrors (path : String) (ls : List String) (solution : Option (String × String))
    (snap : Snapshot) : List String :=
  match solution with
  | none => []
  | some (sp, sol) =>
    let wp := "HCP/Worksheets/" ++ fileName sp
    let (wErr, wtext) := match snap.read? wp with
      | none => ([s!"{path}: worksheet not found at {wp}"], "")
      | some t => ([], t)
    let errs := wErr ++ exampleCommentErrors sp sol ++ exampleCommentErrors wp wtext
    let sls := lines sol
    let anchorsAt := sls.zipIdx.filterMap fun (l, i) => (markerName "-- ANCHOR: " l).map (·, i)
    let anchors := anchorsAt.map (·.1)
    let anchorBlock (name : String) : String :=
      match anchorsAt.find? (·.1 == name) with
      | none => ""
      | some (_, i) =>
        let rest := sls.drop (i + 1)
        match rest.findIdx? (fun l => markerName "-- ANCHOR_END: " l == some name) with
        | none => ""
        | some e => String.intercalate "\n" (rest.take e)
    let wls := lines wtext
    let exercises := wls.zipIdx.filterMap fun (l, i) => (markerName "-- EXERCISE: " l).map (·, i)
    let eNames := if exercises.map (·.1) != anchors then
      [s!"{path}: worksheet EXERCISE names do not match solution ANCHOR names in order"] else []
    let perExercise := (exercises.zipIdx).flatMap fun ((name, ei), k) =>
      let nextStart := match exercises[k + 1]? with | some (_, j) => j | none => wls.length
      let between := (wls.drop (ei + 1)).take (nextStart - ei - 1)
      let (endErr, block) := match between.findIdx? (fun l => markerName "-- EXERCISE_END: " l == some name) with
        | none => ([s!"{path}: exercise '{name}' is missing its matching EXERCISE_END"], (wls.drop ei).take (nextStart - ei))
        | some e => ([], (wls.drop ei).take (e + 2))
      let blockText := String.intercalate "\n" block
      let todoErr := if (blockText.splitOn "TODO:").length > 1 then [] else [s!"{path}: exercise '{name}' is missing a TODO"]
      let cmds := errorGuardCommands (anchorBlock name)
      let firsts := cmds.map fun c => c.headD "<empty command>"
      let occurrences := (firsts.zipIdx).map fun (f, i) => ((firsts.take (i + 1)).filter (· == f)).length
      let probes := commentedProbeCommands blockText
      let order := (List.range cmds.length).mergeSort fun a b =>
        cmds[a]!.length > cmds[b]!.length || (cmds[a]!.length == cmds[b]!.length && a ≤ b)
      let (_, missing) := order.foldl (fun (st : List Bool × List Nat) ci =>
        let (un, miss) := st
        let cmd := cmds[ci]!
        match (List.range probes.length).find? (fun pi =>
            un[pi]! && probes[pi]!.length ≥ cmd.length && probes[pi]!.take cmd.length == cmd) with
        | some pi => (un.set pi false, miss)
        | none => (un, miss ++ [ci])) (List.replicate probes.length true, [])
      let missErrs := (missing.mergeSort (· ≤ ·)).map fun ci =>
        let f := firsts[ci]!
        let occ := if (firsts.filter (· == f)).length > 1 then s!" (occurrence {occurrences[ci]!})" else ""
        s!"{path}: exercise '{name}' is missing a commented counterpart for guarded command '{f}{occ}'"
      endErr ++ todoErr ++ missErrs
    let guardErr := if (wtext.splitOn "#guard_msgs").length > 1 then [s!"{path}: worksheet must not contain #guard_msgs"] else []
    let expected := s!"Worksheet: `HCP/Worksheets/{fileName sp}` · Solution: `HCP/{fileName sp}`"
    let learnErr := match headingSection ls 1 "Learning path" with
      | some sec => if ((String.intercalate "\n" sec).splitOn expected).length > 1 then [] else [s!"{path}: Learning path is missing '{expected}'"]
      | none => [s!"{path}: Learning path is missing '{expected}'"]
    errs ++ eNames ++ perExercise ++ guardErr ++ learnErr

/-- `check(path)`: one chapter's front matter, sections, synopsis, learning path, worksheet and
anchor references. -/
def chapterErrors (snap : Snapshot) (path : String) : List String :=
  let text := (snap.read? path).getD ""
  let ls := lines text
  match parseChapterFrontMatter text with
  | .error e => [s!"{path}: line {e.line}: {e.message}"]
  | .ok data =>
    let get (k : String) : Option Value := (data.find? (·.1 == k)).map (·.2)
    let missing := (sortStrings (requiredKeys.filter fun k => !data.any (·.1 == k))).map fun k =>
      s!"{path}: missing field '{k}'"
    let tagErr := match (metadataBlock ls).bind fun (m, _) => tagOf m with
      | none => [s!"{path}: missing blueprint tag in %%% metadata"]
      | some tag => if get "id" != some (.str tag) then
          [s!"{path}: id '{pyShow (get "id")}' does not match chapter tag '{tag}'"] else []
    let chapterNum := chapterNumber (fileName path)
    let (lesson, lessonNum, modErrs) : Option (String × String) × Option Nat × List String :=
      match exampleModules ls with
      | [m] =>
        match lessonNumber m with
        | none => (none, none, [s!"{path}: unsupported example module '{m}'"])
        | some k =>
          let lp := modulePath m
          let e1 := if snap.has lp then [] else [s!"{path}: example module '{m}' not found at {lp}"]
          let e2 := if chapterNum != some k then [s!"{path}: example module '{m}' does not match the chapter filename"] else []
          ((snap.read? lp).map (lp, ·), some k, e1 ++ e2)
      | _ => (none, none, [s!"{path}: expected one set_option verso.exampleModule declaration"])
    let nameErr := if chapterNum.isNone then [s!"{path}: chapter filename must be L0–L6 followed by its module name"] else []
    let hcpErr := match get "hcp", lessonNum with
      | some (.nat h), some k => if h == k + 1 then [] else [s!"{path}: hcp value '{h}' must equal the example module lesson number plus one"]
      | v, _ => [s!"{path}: hcp value '{pyShow v}' must equal the example module lesson number plus one"]
    let conceptErrs := match get "concepts" with
      | some (.maps ms) =>
        if ms.isEmpty then [s!"{path}: concepts must be a non-empty list"]
        else (ms.zipIdx).filterMap fun (m, i) =>
          if m.length == conceptKeys.length && conceptKeys.all (fun k => m.any (·.1 == k)) then none
          else some s!"{path}: concepts[{i}] must have exactly {pyList (sortStrings conceptKeys)}"
      | some (.list xs) =>
        if xs.isEmpty then [s!"{path}: concepts must be a non-empty list"]
        else (List.range xs.length).map fun i => s!"{path}: concepts[{i}] must have exactly {pyList (sortStrings conceptKeys)}"
      | _ => [s!"{path}: concepts must be a non-empty list"]
    let stateErr := match get "state" with
      | some (.map m) => match m.find? (·.1 == "completed") with
        | some (_, .list _) => []
        | _ => [s!"{path}: state.completed must be a list"]
      | _ => [s!"{path}: state.completed must be a list"]
    let headErr := if ls.filterMap (headingOf 1) != chapterSections then
      [s!"{path}: top-level headings must be exactly {pyList chapterSections} in order"] else []
    let synErrs := synopsisErrors path ls lesson snap.vocabSources
    let (learnErrs, rows) := match headingSection ls 1 "Learning path" with
      | none => ([s!"{path}: missing or duplicate '# Learning path' section"], 0)
      | some sec => match learningTables sec with
        | [t] => ([], tableRows t)
        | _ => ([s!"{path}: Learning path must contain exactly one :::table +header block"], 0)
    let exErr := match get "exercises" with
      | some (.nat n) => if n == rows then [] else [s!"{path}: front matter says {n} exercises, learning path has {rows}"]
      | v => [s!"{path}: front matter says {pyShow v} exercises, learning path has {rows}"]
    let wsErrs := worksheetErrors path ls lesson snap
    let refErrs := (anchorRefs text).filterMap fun (m, a) =>
      let lp := modulePath m
      match snap.read? lp with
      | none => some s!"{path}: Module#anchor module '{m}' not found at {lp}"
      | some t =>
        if (lines t).any (fun l => anchorMarker l == some (true, a)) then none
        else some s!"{path}: anchor '{a}' not found in {m}"
    missing ++ tagErr ++ modErrs ++ nameErr ++ hcpErr ++ conceptErrs ++ stateErr ++ headErr
      ++ synErrs ++ learnErrs ++ exErr ++ wsErrs ++ refErrs

/-- One chapter's excerpts against its lesson: errors, and the rewritten chapter when `fix`
changed it. -/
def chapterExcerpts (snap : Snapshot) (cp : String) (fix : Bool) : List String × Option String :=
  let text := (snap.read? cp).getD ""
  let cls := lines text
  match exampleModules cls with
  | [m] =>
    if !(m.startsWith "HCP." && isLeanIdentPath m) then ([s!"{cp}: unsupported example module '{m}'"], none)
    else
      let sp := modulePath m
      match snap.read? sp with
      | none => ([s!"{cp}: example module '{m}' not found at {sp}"], none)
      | some stext =>
        let (anchors, aErrs) := sourceAnchors sp stext
        let emptyErrs := anchors.filterMap fun (name, body) =>
          if (nonblankCodeLines body).isEmpty then some s!"{sp}: source anchor '{name}' is empty" else none
        let (errs, fixed, changed) := excerptCheck cp sp cls anchors fix
        (aErrs ++ emptyErrs ++ errs, if changed then some (String.intercalate "\n" fixed) else none)
  | _ => ([s!"{cp}: expected one set_option verso.exampleModule declaration"], none)

def excerptErrors (snap : Snapshot) : List String :=
  if snap.chapters.isEmpty then [s!"{chapterDir}: no HCP blueprint chapters found"]
  else snap.chapters.flatMap fun cp => (chapterExcerpts snap cp false).1

/-! ## The SBVR renderings -/

def sbvrLessonName (path : String) : Option String :=
  let n := fileName path
  match n.toList with
  | 'L' :: rest =>
    let ds := rest.takeWhile Char.isDigit
    match rest.drop ds.length with
    | '_' :: _ => if ds.isEmpty then none else some ("L" ++ String.ofList ds)
    | _ => none
  | _ => none

/-- The names a chapter lists as new at its step, `(name, member)`: a name inside parentheses
after a term, or one the explanation after the em dash introduces, is a member. -/
def sbvrNewTerms (ls : List String) : List (String × Bool) :=
  match synopsisSection ls >>= fun syn => headingSection syn 2 "PKC vocabulary in scope" with
  | none => []
  | some vocab =>
    match vocab.findIdx? (fun l => rstrip l == "New at this step:") with
    | none => []
    | some i =>
      let body := (vocab.drop (i + 1)).takeWhile fun l => !l.startsWith "Carried from earlier steps:"
      let bullets := body.filterMap fun l => if l.startsWith "- " then some ((l.drop 2).toString) else none
      bullets.foldl (fun (terms : List (String × Bool)) bullet =>
        let (names, explanation) := (splitOnce bullet " — ").getD (bullet, "")
        let rec scan (cs : List Char) (depth : Nat) (acc : List (String × Bool)) (fuel : Nat) : List (String × Bool) :=
          match fuel, cs with
          | 0, _ => acc
          | _, [] => acc
          | fuel + 1, '`' :: rest =>
            let piece := rest.takeWhile (· != '`')
            match rest.drop piece.length with
            | '`' :: rest' =>
              if piece.isEmpty then scan rest' depth acc fuel
              else scan rest' depth (acc ++ [(String.ofList piece, depth != 0)]) fuel
            | _ => scan rest depth acc fuel
          | fuel + 1, '(' :: rest => scan rest (depth + 1) acc fuel
          | fuel + 1, ')' :: rest => scan rest (depth - 1) acc fuel
          | fuel + 1, _ :: rest => scan rest depth acc fuel
        let terms := scan names.toList 0 terms (names.length + 1)
        ((backticked explanation).filter (· ≠ "")).foldl (fun terms name =>
          if terms.any (·.1 == name) then terms else terms ++ [(name, true)]) terms) []

/-- The parenthesised source at the end of a rendered definition: `(…)` with balanced parens. -/
def trailingSource (rest : String) : Option String :=
  if !rest.endsWith ")" then none
  else
    let cs := rest.toList.reverse.drop 1
    let rec go (cs : List Char) (depth : Nat) (acc : List Char) : Option String :=
      match cs with
      | [] => none
      | '(' :: rest => if depth == 0 then some (String.ofList acc) else go rest (depth - 1) ('(' :: acc)
      | ')' :: rest => go rest (depth + 1) (')' :: acc)
      | c :: rest => go rest depth (c :: acc)
    go cs 0 []

/-- What a rendering says is new at its step: the designations (preferred term and `also:`
synonyms) and the definition sources, read from the structure of `sbvr-check render`'s output. -/
def sbvrRenderingTerms (rendered : String) : List String × List String :=
  let block := ((splitOnce rendered "New at this step:").map (·.2)).getD rendered
  let block := ((splitOnce block "Carried from earlier steps:").map (·.1)).getD block
  (lines block).foldl (fun (st : List String × List String) l =>
    let (des, srcs) := st
    let l := trim l
    if !l.startsWith "- " then st
    else match splitOnce ((l.drop 2).toString) " — " with
    | none => st
    | some (head, rest) =>
      if rest == "verb" then st
      else
        let (head, syns) := match splitOnce head " (also: " with
          | some (h, tail) => if tail.endsWith ")" then (h, ((dropRight tail 1).splitOn ",").map trim) else (head, [])
          | none => (head, [])
        let des := des ++ [trim head] ++ syns
        (des, srcs ++ (trailingSource (trim rest)).toList)) ([], [])

def sbvrReferenceOnly (name : String) : Bool :=
  name.contains '.' || name.startsWith "#" || name.startsWith "@["

def sbvrTermErrors (path name : String) (ls : List String) (rendered : String) : List String :=
  let (des, srcs) := sbvrRenderingTerms rendered
  (sbvrNewTerms ls).filterMap fun (term, member) =>
    if !member && !sbvrReferenceOnly term then
      if des.contains term then none
      else some s!"{path}: `{term}` is new at this step but is not a designation of {sbvrChain} ({name})"
    else if srcs.any (containsIdentifier · term) then none
    else
      let what := if member then "a member of a term" else "a reference"
      some s!"{path}: `{term}` ({what}) is new at this step but no definition source of {sbvrChain} ({name}) cites it"

def renderedErrors (snap : Snapshot) : List String :=
  snap.chapters.flatMap fun path =>
    match sbvrLessonName path with
    | none => [s!"{path}: cannot name its SBVR vocabulary (expected L<k>_*.lean)"]
    | some name =>
      let target := s!"{sbvrRenderedDir}/{name}.md"
      match snap.read? target with
      | none => [s!"{target}: missing; run hcp-check --sbvr SBVR_CHECK --fix-sbvr"]
      | some r => sbvrTermErrors path name (lines ((snap.read? path).getD "")) r

/-! ## The verdict -/

/-- Every error of a snapshot, in the order they are printed (the `--sbvr` run's come between
`chapterErrors` and `renderedErrors`). -/
def errors (snap : Snapshot) : List String :=
  excerptErrors snap ++ snap.chapters.flatMap (chapterErrors snap) ++ renderedErrors snap

def Ok (snap : Snapshot) : Prop :=
  excerptErrors snap = [] ∧ (∀ c ∈ snap.chapters, chapterErrors snap c = []) ∧ renderedErrors snap = []

theorem errors_nil_iff (snap : Snapshot) : errors snap = [] ↔ Ok snap := by
  simp [errors, Ok, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]

/-! ## IO -/

def readText (root : System.FilePath) (rel : String) : IO (Option String) := do
  let p := root / rel
  if ← p.pathExists then
    if ← p.isDir then pure none else some <$> IO.FS.readFile p
  else pure none

def relOf (root : System.FilePath) (p : System.FilePath) : String :=
  let r := root.toString
  let s := p.toString
  if s.startsWith (r ++ "/") then (s.drop (r.length + 1)).toString else s

def listFiles (root : System.FilePath) (dir : String) (ext : String) (recursive : Bool) :
    IO (List String) := do
  let d := root / dir
  if !(← d.isDir) then return []
  let files ← if recursive then d.walkDir (fun _ => pure true) else
    (← d.readDir).mapM fun e => pure e.path
  let files := files.filter fun p => p.extension == some ext
  let rels := files.map (relOf root)
  return (rels.qsort (· < ·)).toList

def snapshot (root : System.FilePath) : IO Snapshot := do
  let chapters ← listFiles root chapterDir "lean" false
  let chapters := chapters.filter fun p => (fileName p).startsWith "L"
  let lessons ← listFiles root "HCP" "lean" false
  let worksheets ← listFiles root "HCP/Worksheets" "lean" false
  let rendered ← listFiles root sbvrRenderedDir "md" false
  let mut files : List (String × String) := []
  for p in chapters ++ lessons ++ worksheets ++ rendered do
    if let some t ← readText root p then files := files ++ [(p, t)]
  -- modules the chapters name (example modules and `Module#anchor` references) anywhere
  for c in chapters do
    let text := ((files.find? (·.1 == c)).map (·.2)).getD ""
    let mods := exampleModules (lines text) ++ (anchorRefs text).map (·.1)
    for m in mods do
      let p := modulePath m
      if isLeanIdentPath m && !files.any (·.1 == p) then
        if let some t ← readText root p then files := files ++ [(p, t)]
  let mut sources : List String := []
  for dir in ["PropertyKindCalculus", "ForPhysLib"] do
    for p in ← listFiles root dir "lean" true do
      if let some t ← readText root p then sources := sources ++ [t]
  return { files, chapters, vocabSources := sources }

def run (root : System.FilePath) (exe : String) (args : List String) : IO (UInt32 × String × String) := do
  let out ← IO.Process.output { cmd := exe, args := args.toArray, cwd := root }
  return (out.exitCode, out.stdout, out.stderr)

def renderedHeader (name : String) : String :=
  s!"<!-- Rendered from ../physlib-contributor.yaml by `sbvr-check render` ({name}); regenerate with `hcp-check --sbvr SBVR_CHECK --fix-sbvr`, do not edit. -->\n\n"

/-- The chain checks clean and each rendering equals the committed file (or is rewritten). -/
def sbvrErrors (root : System.FilePath) (chapters : List String) (exe : String) (fix : Bool) :
    IO (List String) := do
  let (code, out, err) ← run root exe [sbvrChain]
  if code != 0 then
    return [s!"{sbvrChain}: sbvr-check exited {code}:\n{rstrip (out ++ err)}"]
  let names := sbvrFoundation :: chapters.filterMap sbvrLessonName
  IO.FS.createDirAll (root / sbvrRenderedDir)
  let mut errs : List String := []
  for name in names do
    let (code, out, err) ← run root exe ["render", sbvrChain, name]
    if code != 0 then
      let gaps := (lines out).filterMap fun l =>
        if (l.splitOn "no definition at this step").length > 1 then some (trim l) else none
      errs := errs ++ [s!"{sbvrChain}: vocabulary {name} does not render clean (exit {code}): " ++
        (if gaps.isEmpty then trim (out ++ err) else String.intercalate "; " gaps)]
      continue
    let target := s!"{sbvrRenderedDir}/{name}.md"
    let expected := renderedHeader name ++ out
    let current ← readText root target
    if current != some expected then
      if fix then IO.FS.writeFile (root / target) expected
      else
        let state := if current.isNone then "missing" else "stale"
        errs := errs ++ [s!"{target}: {state}; rerun with --fix-sbvr to regenerate"]
  return errs

def usage : String :=
  "usage: hcp-check [--fix-excerpts] [--sbvr SBVR_CHECK] [--fix-sbvr]"

def parseArgs : List String → Except String (Bool × Option String × Bool)
  | [] => .ok (false, none, false)
  | "--fix-excerpts" :: rest => (fun (_, s, f) => (true, s, f)) <$> parseArgs rest
  | "--fix-sbvr" :: rest => (fun (e, s, _) => (e, s, true)) <$> parseArgs rest
  | "--sbvr" :: exe :: rest => (fun (e, _, f) => (e, some exe, f)) <$> parseArgs rest
  | ["--sbvr"] => .error "--sbvr requires a path"
  | a :: _ => .error s!"unknown argument '{a}'"

def main (args : List String) : IO UInt32 := do
  let (fixExcerpts, sbvr, fixSbvr) ← match parseArgs args with
    | .ok v => pure v
    | .error e => do IO.eprintln s!"{usage}\nhcp-check: error: {e}"; return 2
  if fixSbvr && sbvr.isNone then
    IO.eprintln s!"{usage}\nhcp-check: error: --fix-sbvr requires --sbvr"; return 2
  let root : System.FilePath := "."
  let mut snap ← snapshot root
  if snap.chapters.isEmpty then IO.eprintln "no HCPs found"; return 1
  if fixExcerpts then
    for cp in snap.chapters do
      if let (_, some fixed) := chapterExcerpts snap cp true then IO.FS.writeFile (root / cp) fixed
    snap ← snapshot root
  let errs1 := excerptErrors snap ++ snap.chapters.flatMap (chapterErrors snap)
  let errs2 ← match sbvr with
    | some exe => sbvrErrors root snap.chapters exe fixSbvr
    | none => pure []
  -- renderings read after `--fix-sbvr` may have rewritten them
  if fixSbvr then snap ← snapshot root
  let errs := errs1 ++ errs2 ++ renderedErrors snap
  for e in errs do IO.eprintln e
  IO.println s!"{snap.chapters.length} HCPs checked, {errs.length} errors"
  return if errs.isEmpty then 0 else 1

end Tools.HcpCheck

public def main (args : List String) : IO UInt32 := Tools.HcpCheck.main args
