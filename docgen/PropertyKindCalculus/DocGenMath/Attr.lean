/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import Lean
import PropertyKindCalculus.DocGenMath.Term
import PropertyKindCalculus.DocGenMath.Registry
import PropertyKindCalculus.DocGenMath.Lift
import PropertyKindCalculus.DocGenMath.Normalize
import PropertyKindCalculus.DocGenMath.Pretty
import DocGen4.Process.DeclMath

/-!
# The `@[pkc_math]` attribute — orchestration + doc-gen4 hand-off

`quantityToLatex` runs the three-stage pipeline over a definition's value and returns a LaTeX
equation `lhs = rhs`. The `@[pkc_math]` attribute computes it (or takes a literal override) and
hands the rendered markdown to doc-gen4 via `DocGen4.Process.addDeclMath`, which appends it to the
declaration's docstring so it typesets through doc-gen4's normal, MathJax-processed rendering path
(see `RENDERING.md` §6). This is the only module coupled to doc-gen4.
-/

namespace PropertyKindCalculus.DocGenMath

open Lean Meta

/-- Attribute syntax: `@[pkc_math]` (auto-render) or `@[pkc_math "…literal LaTeX…"]` (override). -/
syntax (name := pkc_math) "pkc_math" (ppSpace str)? : attr

/-- Run the three stages (lift → normalize → pretty) over `declName`'s value and return the LaTeX
body of the equation `lhs = rhs` (no `$$` delimiters). Definitions only; anything else yields an
error the caller turns into a graceful skip. -/
def quantityToLatex (declName : Name) : MetaM String := do
  let env ← getEnv
  let some (.defnInfo di) := env.find? declName
    | throwError "`[pkc_math]` expects a definition, but {declName} is not one"
  let rhs ← lambdaTelescope di.value fun _xs body => do
    return pretty (resolveToken (← getEnv)) (normalize (← liftExpr body))
  let lhs := resolveToken env (toString declName)
  return lhs ++ " = " ++ rhs

/-- Wrap a LaTeX equation body as a MathJax **display-math** markdown block. -/
def displayMath (body : String) : String := "$$" ++ body ++ "$$"

/-- Compute the markdown for `@[pkc_math]` on `declName`: the literal `override?` if given (the
escape hatch of `RENDERING.md` §5), otherwise the rendered equation. -/
def mathMarkdown (declName : Name) (override? : Option String) : MetaM String := do
  match override? with
  | some s => return displayMath s
  | none   => return displayMath (← quantityToLatex declName)

initialize registerBuiltinAttribute {
  name := `pkc_math
  descr := "Render this quantity definition as typeset LaTeX on its doc-gen4 page."
  add := fun decl stx _kind => do
    let override? : Option String :=
      match stx with
      | `(attr| pkc_math $s:str) => some s.getString
      | _                        => none
    let md ← (mathMarkdown decl override?).run'
    DocGen4.Process.addDeclMath decl md
}

end PropertyKindCalculus.DocGenMath
