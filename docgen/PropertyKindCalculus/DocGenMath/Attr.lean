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

/-!
# The `@[pkc_math]` attribute — orchestration + docstring hand-off

`quantityToLatex` runs the three-stage pipeline over a definition's value and returns a LaTeX
equation `lhs = rhs`. The `@[pkc_math]` attribute computes it (or takes a literal override) and
appends to the declaration's **own docstring** both the rendered `$$…$$` equation and the
definition's Lean source (a ```` ```lean ```` code block), so the doc page shows the formula *and*
the source it came from — not the formula plus a link. The write goes through core Lean's
`Lean.addDocStringCore` (the `docStringExt` map extension), so the content flows through the standard
docstring path with no special support from any renderer: doc-gen4 typesets it on the declaration's
HTML page, and the Lean InfoView typesets it in the editor — both via MathJax. This makes the
library depend on core Lean only, never on doc-gen4 (see `RENDERING.md` §6).

The attribute runs at `AttributeApplicationTime.afterCompilation`, which is *after* the elaborator
attaches any authored `/-- … -/` docstring (see `Lean.Elab.PreDefinition.Basic.addNonRecAux`), so
reading the current docstring and appending preserves the authored prose. At the default time
(`afterTypeChecking`) the docstring is not yet present and the authored one would clobber ours.
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

/-- Pretty-print `declName`'s definition as Lean source, `def … := …`, for display next to the
rendered math (`none` when it is not a definition, so the caller omits the source block). The
delaborator runs in the ambient namespace / `open` context, so names print as authored. -/
def defSource? (declName : Name) : MetaM (Option String) := do
  let some (.defnInfo di) := (← getEnv).find? declName | return none
  let sig ← PrettyPrinter.ppSignature declName
  let body ← lambdaTelescope di.value fun _xs b => Meta.ppExpr b
  -- `ppSignature` prints the fully-qualified decl name as the header; shorten it to the base name
  -- (binders and body already delaborate to short names in the ambient `open` context).
  let full := toString declName
  let short := full.splitOn "." |>.getLastD full
  let sigStr := sig.fmt.pretty.replace full short
  return some ("def " ++ sigStr ++ " :=\n  " ++ body.pretty)

/-- Fence a Lean source snippet as a ```` ```lean ```` markdown code block. -/
def sourceBlock (src : String) : String := "```lean\n" ++ src ++ "\n```"

/-- Compute the markdown for `@[pkc_math]` on `declName`: the rendered equation (or the literal
`override?` — the escape hatch of `RENDERING.md` §5) as display math, followed by the definition's
Lean source in a code block, so the doc page shows both the formula and the source it came from. -/
def mathMarkdown (declName : Name) (override? : Option String) : MetaM String := do
  let math := displayMath (← match override? with
    | some s => pure s
    | none   => quantityToLatex declName)
  match (← defSource? declName) with
  | some src => return math ++ "\n\n" ++ sourceBlock src
  | none     => return math

initialize registerBuiltinAttribute {
  name := `pkc_math
  descr := "Render this quantity definition as typeset LaTeX in its docstring (doc-gen4 + InfoView)."
  -- Run after the elaborator attaches the authored docstring, so the append below preserves it.
  applicationTime := .afterCompilation
  add := fun decl stx _kind => do
    let override? : Option String :=
      match stx with
      | `(attr| pkc_math $s:str) => some s.getString
      | _                        => none
    let md ← (mathMarkdown decl override?).run'
    -- Append to the declaration's own docstring (or set it, if there is none). `docStringExt`
    -- serializes into the `.olean`, so the separate doc-gen4 process reads it back via
    -- `findDocString?` and MathJax typesets the `$$…$$`; the InfoView renders it the same way.
    let existing ← findSimpleDocString? (← getEnv) decl (includeBuiltin := false)
    let combined := match existing with
      | some doc => doc.trimAsciiEnd.toString ++ "\n\n" ++ md
      | none     => md
    addDocStringCore decl combined
}

end PropertyKindCalculus.DocGenMath
