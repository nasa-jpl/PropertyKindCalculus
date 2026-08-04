/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import Lean

/-!
# Symbol registry + atom heuristics for PKC math rendering

Stage 3 (the pretty printer) turns each atom token into a LaTeX symbol. Two sources feed it:

* **`@[pkc_math_symbol "…"]`** — an author-controlled, per-declaration override. Put it on a named
  helper (`attenuationQ`, an EM `curl` operator, …) to say *"render this as this LaTeX"*. This is the
  practical, high-leverage form of the recognition registry in `RENDERING.md` §5: it recognizes a
  **named** operator and gives it its conventional notation. (Recognizing an *unlabeled* op-tree
  shape — `x·x → x²` lives in `Normalize`; richer structural rules — is a documented future
  extension; the mechanism here already covers named operators, which is most of the win.)
* **`builtinSymbol`** — a pure heuristic for the common cases with no override: Greek names,
  trailing-digit subscripts (`s0 → s_{0}`), a small dictionary (`ndvi → \mathrm{NDVI}`), single
  letters as-is, and multi-letter identifiers as `\mathrm{…}`.

`resolveToken env` composes them: registry first (by declaration name), then the heuristic.
-/

namespace PropertyKindCalculus.DocGenMath

open Lean

/-- Attribute syntax: `@[pkc_math_symbol "\\mathrm{NDVI}"]`. -/
syntax (name := pkc_math_symbol) "pkc_math_symbol " str : attr

/-- Per-declaration LaTeX-notation override. Maps a declaration to the exact LaTeX its name should
render as wherever the rendering pipeline meets it (as an atom or as a function head). -/
initialize pkcMathSymbolAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `pkc_math_symbol
    descr := "Override the LaTeX notation used to render this declaration in PKC math rendering."
    getParam := fun _decl stx =>
      match stx with
      | `(attr| pkc_math_symbol $s:str) => return s.getString
      | _ => throwError "invalid `[pkc_math_symbol]` attribute; expected a string literal"
  }

/-- The registered LaTeX override for `declName`, if any. -/
def getMathSymbol? (env : Environment) (declName : Name) : Option String :=
  pkcMathSymbolAttr.getParam? env declName

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
private def mathrm (s : String) : String := "\\mathrm{" ++ s ++ "}"

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

/-- Resolve an atom/function-head token to LaTeX: a `@[pkc_math_symbol]` override on the
declaration of that name wins; otherwise the heuristic on the base name. -/
def resolveToken (env : Environment) (token : String) : String :=
  match getMathSymbol? env token.toName with
  | some latex => latex
  | none       => builtinSymbol (baseName token)

end PropertyKindCalculus.DocGenMath
