/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import Lean
import PropertyKindCalculus.DocGenMath.Term

/-!
# Symbol registry + atom heuristics for PKC math rendering

Stage 3 (the pretty printer) turns each token into a `MathNotation`. Two sources feed it:

* **`@[pkc_math_symbol "…"]`** — an author-controlled, per-declaration override. Put it on a named
  helper (`attenuationQ`, an EM `curl` operator, …) to say *"render this as this LaTeX"*. This is the
  practical, high-leverage form of the recognition registry in `RENDERING.md` §5: it recognizes a
  **named** operator and gives it its conventional notation. (Recognizing an *unlabeled* op-tree
  shape — `x·x → x²` lives in `Normalize`; richer structural rules — is a documented future
  extension; the mechanism here already covers named operators, which is most of the win.)
  The optional `operator` marker — `@[pkc_math_symbol "\\nabla" operator]` — additionally declares
  the notation to be a **bare prefix operator**, so a one-argument application prints juxtaposed
  (`\nabla x`) instead of parenthesized. This has to be *declared*: it cannot be read off the LaTeX,
  because `builtinSymbol`'s upright fallback `\mathrm{…}` also begins with a backslash and must keep
  printing as `\mathrm{gain}\left(a\right)`.
* **`@[pkc_math_config]`** — a tag on a *structure*, declaring it a **configuration type**. A model's
  named constants live in such a structure (`AvsConfig.two`, the two-way optical-path factor), read
  through a field projection `cfg.two`. Without the tag that projection is just an unrecognized
  application and renders `\mathrm{two}\left(\mathrm{cfg}\right)` — the field stripped of the type it
  belongs to, plus a spurious application of a value that carries no information for the reader. With
  it, the projection renders as the qualified constant `\mathrm{AvsConfig.two}` and the configuration
  value is elided. The tag is what makes this safe: a blanket "drop the receiver" rule for *every*
  projection would turn `p.fst` into `\mathrm{fst}`.
* **`builtinSymbol`** — a pure heuristic for the common cases with no override: Greek names,
  trailing-digit subscripts (`s0 → s_{0}`), a small dictionary (`ndvi → \mathrm{NDVI}`), single
  letters as-is, and multi-letter identifiers as `\mathrm{…}`.

`resolveToken env` composes them: the `@[pkc_math_symbol]` registry first (by declaration name), then
the configuration qualification, then the heuristic.
-/

namespace PropertyKindCalculus.DocGenMath

open Lean

/-- Attribute syntax: `@[pkc_math_symbol "\\mathrm{NDVI}"]`, or `@[pkc_math_symbol "\\nabla"
operator]` to declare the notation a bare prefix operator. -/
syntax (name := pkc_math_symbol) "pkc_math_symbol " str (ppSpace &"operator")? : attr

/-- Per-declaration notation override. Maps a declaration to the exact LaTeX its name should render
as wherever the rendering pipeline meets it (as an atom or as a function head), together with the
head layout that LaTeX wants. -/
initialize pkcMathSymbolAttr : ParametricAttribute MathNotation ←
  registerParametricAttribute {
    name := `pkc_math_symbol
    descr := "Override the LaTeX notation used to render this declaration in PKC math rendering."
    getParam := fun _decl stx =>
      match stx with
      | `(attr| pkc_math_symbol $s:str operator) =>
        return { latex := s.getString, operator := true }
      | `(attr| pkc_math_symbol $s:str) => return { latex := s.getString }
      | _ => throwError "invalid `[pkc_math_symbol]` attribute; expected a string literal \
             optionally followed by `operator`"
  }

/-- The registered notation override for `declName`, if any. -/
def getMathSymbol? (env : Environment) (declName : Name) : Option MathNotation :=
  pkcMathSymbolAttr.getParam? env declName

/-! ### Configuration types -/

/-- Marks a structure as a **configuration type**: its fields are the model's named constants, so a
field projection renders as the qualified symbol `Struct.field` with the configuration value elided
(`RENDERING.md` §5). Applies to the structure, never to the individual fields — one tag covers them
all, and an individual field can still be given its own notation with `@[pkc_math_symbol]`. -/
initialize pkcMathConfigAttr : TagAttribute ←
  registerTagAttribute `pkc_math_config
    "Mark a structure as a configuration type: its field projections render as `Struct.field`."
    (validate := fun declName => do
      unless isStructure (← getEnv) declName do
        throwError "`[pkc_math_config]` expects a structure, but {declName} is not one")

/-- If `declName` is a field projection of a `@[pkc_math_config]` structure, the qualified display
name `Struct.field` — each component shortened to its last name, so the reader sees
`AvsConfig.two`, not the fully-qualified path. `none` for every other declaration, which is what
keeps ordinary projections (`Prod.fst`, …) on the normal application path. -/
def configFieldName? (env : Environment) (declName : Name) : Option String := do
  let structName ← env.getProjectionStructureName? declName
  guard <| pkcMathConfigAttr.hasTag env structName
  return structName.getString! ++ "." ++ declName.getString!

/-! ### Transparent wrappers -/

/-- Marks a declaration as a **notational wrapper**: an application of it renders as its argument.

The case that motivates it is a carrier's numeral injection — `ofN (n : Nat) : α := (n : α)` — which
otherwise renders `\mathrm{ofN}\left(2\right)` wherever the model writes a constant, so every
equation carries the name of the coercion instead of the number. `2` is what the definition
computes, so dropping the wrapper stays in the **F** (faithful) tier; it is notation, not algebra.

Only put it on a declaration that really is transparent — one whose value *is* its explicit
argument, up to the representation change the reader is meant not to see. A wrapper that scales
(`clayPctOfMassFraction c = c·100`) is **not** transparent: hiding it would drop the factor. Those
keep the ordinary application layout, and `@[pkc_math_symbol]` gives them their notation. -/
initialize pkcMathTransparentAttr : TagAttribute ←
  registerTagAttribute `pkc_math_transparent
    "Render an application of this notational wrapper as its argument (e.g. a numeral injection)."

/-- Whether `declName` is tagged `@[pkc_math_transparent]`. -/
def isTransparentWrapper (env : Environment) (declName : Name) : Bool :=
  pkcMathTransparentAttr.hasTag env declName

/-! ### Heuristic atom table (used when there is no `@[pkc_math_symbol]` override) -/

/-- Greek-letter spellings recognized in atom names. -/
private def greek : List (String × String) :=
  [ ("alpha", "\\alpha"), ("beta", "\\beta"), ("gamma", "\\gamma"), ("delta", "\\delta"),
    ("epsilon", "\\epsilon"), ("varepsilon", "\\varepsilon"), ("zeta", "\\zeta"),
    ("eta", "\\eta"), ("theta", "\\theta"), ("iota", "\\iota"), ("kappa", "\\kappa"),
    ("lambda", "\\lambda"), ("mu", "\\mu"), ("nu", "\\nu"), ("xi", "\\xi"), ("pi", "\\pi"),
    ("rho", "\\rho"), ("sigma", "\\sigma"), ("tau", "\\tau"), ("phi", "\\phi"),
    ("varphi", "\\varphi"), ("chi", "\\chi"), ("psi", "\\psi"), ("omega", "\\omega"),
    ("Gamma", "\\Gamma"), ("Delta", "\\Delta"), ("Theta", "\\Theta"), ("Lambda", "\\Lambda"),
    ("Sigma", "\\Sigma"), ("Phi", "\\Phi"), ("Psi", "\\Psi"), ("Omega", "\\Omega") ]

/-- A small dictionary of domain identifiers with a conventional typeset form. -/
private def dictionary : List (String × String) :=
  [ ("ndvi", "\\mathrm{NDVI}"), ("NDVI", "\\mathrm{NDVI}"),
    ("sigma0", "\\sigma^{0}"), ("sigma_0", "\\sigma^{0}") ]

/-- Split a trailing run of digits off an identifier: `"s0" ↦ ("s", "0")`, `"abc" ↦ ("abc", "")`. -/
private def splitTrailingDigits (s : String) : String × String :=
  let cs := s.toList
  let digits := cs.reverse.takeWhile Char.isDigit |>.reverse
  let letters := cs.take (cs.length - digits.length)
  (String.ofList letters, String.ofList digits)

/-- Upright multi-letter identifier, `\mathrm{name}`. -/
def mathrm (s : String) : String := "\\mathrm{" ++ s ++ "}"

/-- Escape arbitrary text for a LaTeX `\text{…}` box, and fold newlines into spaces.

Used for the lift's last-resort leaf, where the "text" is pretty-printed Lean source: it carries
braces, backslashes and line breaks, every one of which ends the math environment early or is read
as a control sequence. Escaping keeps an unrenderable subterm *visible and valid* rather than
silently malformed. -/
def latexText (s : String) : String :=
  let escaped := s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '\\' => "\\backslash "
      | '{'  => "\\{"     | '}' => "\\}"
      | '_'  => "\\_"     | '^' => "\\^{}"
      | '&'  => "\\&"     | '%' => "\\%"
      | '#'  => "\\#"     | '$' => "\\$"
      | '~'  => "\\~{}"
      | '\n' | '\r' | '\t' => " "
      | c    => c.toString
  "\\text{" ++ escaped ++ "}"

/-- Map the *base* token (already stripped of any namespace) to LaTeX, by heuristics only. -/
def builtinSymbol (base : String) : String := Id.run do
  -- 1. exact dictionary / Greek hit
  if let some l := dictionary.lookup base then return l
  if let some l := greek.lookup base then return l
  -- 2. trailing-digit subscript, on the (possibly Greek) letter stem: `s0 ↦ s_{0}`
  let (stem, digits) := splitTrailingDigits base
  if !digits.isEmpty && !stem.isEmpty then
    let stemLatex := (greek.lookup stem).getD (if stem.length == 1 then stem else mathrm stem)
    return stemLatex ++ "_{" ++ digits ++ "}"
  -- 3. single letter → itself (italic math); multi-letter → upright \mathrm
  if base.length ≤ 1 then return base
  return mathrm base

/-- The last dotted component of a possibly-qualified name string (`"A.B.foo" ↦ "foo"`). -/
def baseName (token : String) : String :=
  (token.splitOn ".").getLastD token

/-- Resolve an atom/function-head token to notation, in three tiers: a `@[pkc_math_symbol]` override
on the declaration of that name wins; then a field of a `@[pkc_math_config]` structure, qualified by
its type; then the heuristic on the base name. The latter two are only ever plain symbols — an
unregistered head always prints parenthesized. -/
def resolveToken (env : Environment) (token : String) : MathNotation :=
  let declName := token.toName
  match getMathSymbol? env declName with
  | some nota => nota
  | none      =>
    match configFieldName? env declName with
    | some qualified => .ofLatex (mathrm qualified)
    | none           => .ofLatex (builtinSymbol (baseName token))

end PropertyKindCalculus.DocGenMath
