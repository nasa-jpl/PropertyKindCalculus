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

## Derivations

`@[pkc_math substituting f]` adds, *after* the equation as written, the same equation with `f`
inlined. Each `substituting` clause is one derivation step and each step applies the union of the
clauses up to it, so the equations form a chain a reader can follow:

```lean
@[pkc_math substituting lavsForwardQ substituting attenuationQ]
```

renders the literal `s_0 - \mathrm{lavsForwardQ}\left(…\right)`, then the same with `lavsForwardQ`
substituted, then the same again with `attenuationQ` substituted as well. With no clauses the output
is byte-identical to what the attribute produced before derivations existed.

Substitution is *delta*, hence meaning-preserving, so every equation in the chain still denotes
exactly what the definition computes — the **F** tier of `RENDERING.md` §5. It is not a way to
assert algebra: a literal override and a derivation are mutually exclusive, and are rejected
together.
-/

namespace PropertyKindCalculus.DocGenMath

open Lean Meta

/-- One derivation step: the helpers to substitute at that step. -/
syntax pkcMathSubst := " substituting " ident,+

/-- The `let`-binding policy: `keeping` alone keeps every binding as an auxiliary equation,
`keeping x, y` keeps only those. -/
syntax pkcMathKeep := " keeping" (ppSpace ident,+)?

/-- Attribute syntax: `@[pkc_math]` (auto-render), `@[pkc_math "…literal LaTeX…"]` (override),
`@[pkc_math keeping]` / `@[pkc_math keeping x, y]` (render the `let` bindings as a `where` block
instead of inlining them), and `@[pkc_math substituting f, g substituting h]` (auto-render plus a
derivation, one step per `substituting` clause). The clauses compose. -/
syntax (name := pkc_math) "pkc_math" (ppSpace str)? (pkcMathKeep)? (pkcMathSubst)* : attr

/-- A rendered definition: the equation (or the aligned system of field equations, for a
record-valued definition) and, when there is one, the `where` block of auxiliary equations. Both are
LaTeX bodies, without `$$` delimiters. -/
structure MathRendering where
  /-- The main equation's LaTeX body. -/
  equation : String
  /-- The auxiliary equations' LaTeX body, if any binding was kept. -/
  whereEqs : Option String := none

/-- Run the three stages (lift → normalize → pretty) over `declName`'s value, first inlining the
bodies of `subst` (empty for the equation as written) and keeping the `let` bindings `keep` names.
Definitions only; anything else yields an error the caller turns into a graceful skip. -/
def quantityToRendering (declName : Name) (subst : Array Name) (keep : KeepPolicy) :
    MetaM MathRendering := do
  let env ← getEnv
  let some (.defnInfo di) := env.find? declName
    | throwError "`[pkc_math]` expects a definition, but {declName} is not one"
  let lhs := (resolveToken env (toString declName)).latex
  lambdaTelescope di.value fun _xs body => do
    let sys ← liftSystem keep (← substitute subst body)
    let resolve := resolveToken (← getEnv)
    return {
      equation := prettyEquation resolve lhs (normalize sys.body)
      whereEqs := prettyAux resolve (sys.aux.map fun (l, r) => (normalize l, normalize r))
    }

/-- The LaTeX body of `declName`'s equation with `subst` inlined, inlining every `let` — the
rendering as it was before `keeping` and record systems existed. -/
def quantityToLatexSubst (declName : Name) (subst : Array Name) : MetaM String :=
  return (← quantityToRendering declName subst .inlineAll).equation

/-- The equation as written — `quantityToLatexSubst` with nothing substituted. -/
def quantityToLatex (declName : Name) : MetaM String :=
  quantityToLatexSubst declName #[]

/-- Wrap a LaTeX equation body as a MathJax **display-math** markdown block. -/
def displayMath (body : String) : String := "$$" ++ body ++ "$$"

/-- Pretty-print `declName`'s definition as Lean source, `def … := …`, for display next to the
rendered math (`none` when it is not a definition, so the caller omits the source block). The
delaborator runs in the ambient namespace / `open` context, so names print as authored. -/
def defSource? (declName : Name) : MetaM (Option String) := do
  let env ← getEnv
  let some (.defnInfo di) := env.find? declName | return none
  let sig ← PrettyPrinter.ppSignature declName
  -- Inline the elaborator-extracted `<decl>._proof_k` kind witnesses. A kind-gated `Quantity.mul`/
  -- `exp` carries its edge proof in the first slot; the elaborator lifts each to a synthetic
  -- `theorem` and the body then references it by name (`Quantity.mul attenuationQ._proof_1 …`), which
  -- leaks internal machinery. Substituting the proof *term* back lets the pretty-printer treat it as
  -- the proof it is and elide it to the idiomatic `⋯`, so the source reads as a clean operator
  -- skeleton (`Quantity.mul ⋯ a ndvi + …`). These are `theorem`s, whose value `ConstantInfo.value?`
  -- withholds, so read `thmInfo.value` directly.
  let proofValue? (n : Name) : Option Expr :=
    match env.find? n with
    | some (.thmInfo v)  => some v.value
    | some (.defnInfo v) => some v.value
    | _                  => none
  let inlined ← Meta.transform di.value (pre := fun s => do
    if let .const n _ := s then
      if declName.isPrefixOf n && n.getString!.startsWith "_proof" then
        if let some v := proofValue? n then
          return .visit v
    return .continue)
  let body ← lambdaTelescope inlined fun _xs b => Meta.ppExpr b
  -- `ppSignature` prints the fully-qualified decl name as the header; shorten it to the base name
  -- (binders and body already delaborate to short names in the ambient `open` context).
  let full := toString declName
  let short := full.splitOn "." |>.getLastD full
  let sigStr := sig.fmt.pretty.replace full short
  return some ("def " ++ sigStr ++ " :=\n  " ++ body.pretty)

/-- Fence a Lean source snippet as a ```` ```lean ```` markdown code block. -/
def sourceBlock (src : String) : String := "```lean\n" ++ src ++ "\n```"

/-- The markdown blocks of one rendering: the display equation, then — when bindings were kept — a
`where` paragraph and the display block of auxiliary equations. Each `$$…$$` stays a *top-level*
block, the layout already known to typeset in both doc-gen4 and the InfoView. -/
def renderingBlocks (r : MathRendering) : Array String :=
  #[displayMath r.equation] ++ (r.whereEqs.map fun w => #["where", displayMath w]).getD #[]

/-- Render a derivation as markdown: a `**Derivation**` heading, then one numbered step per entry of
`steps`, each naming the helpers it substitutes and followed by the resulting display equation (and
its `where` block, if the step has one). The step number is written literally so the interleaved
display math does not restart the numbering. Empty `steps` renders nothing at all. -/
def derivationBlock (steps : Array (Array Name × MathRendering)) : String := Id.run do
  if steps.isEmpty then return ""
  let mut out := "**Derivation**"
  for h : i in [0:steps.size] do
    let (names, r) := steps[i]
    let named := String.intercalate ", " (names.toList.map fun n => "`" ++ n.getString! ++ "`")
    out := out ++ "\n\n" ++ toString (i + 1) ++ ". substituting " ++ named ++ ":"
      ++ "\n\n" ++ String.intercalate "\n\n" (renderingBlocks r).toList
  return out

/-- Compute the markdown for `@[pkc_math]` on `declName`: the rendered equation (or the literal
`override?` — the escape hatch of `RENDERING.md` §5) as display math, the `where` block of whatever
`keep` kept, then the derivation for `substSteps` (each step substituting the union of the clauses up
to it), then the definition's Lean source in a code block, so the doc page shows the formulas and the
source they came from. -/
def mathMarkdown (declName : Name) (override? : Option String) (keep : KeepPolicy := .inlineAll)
    (substSteps : Array (Array Name) := #[]) : MetaM String := do
  let main : MathRendering ← match override? with
    | some s => pure { equation := s }
    | none   => quantityToRendering declName #[] keep
  -- each step substitutes everything named so far, so the equations refine one another
  let mut cumulative : Array Name := #[]
  let mut steps : Array (Array Name × MathRendering) := #[]
  for names in substSteps do
    cumulative := cumulative ++ names.filter (!cumulative.contains ·)
    steps := steps.push (names, ← quantityToRendering declName cumulative keep)
  let src? := (← defSource? declName).map sourceBlock
  let blocks : Array String := renderingBlocks main ++ #[derivationBlock steps] ++ src?.toArray
  return String.intercalate "\n\n" (blocks.filter (!·.isEmpty)).toList

initialize registerBuiltinAttribute {
  name := `pkc_math
  descr := "Render this quantity definition as typeset LaTeX in its docstring (doc-gen4 + InfoView)."
  -- Run after the elaborator attaches the authored docstring, so the append below preserves it.
  applicationTime := .afterCompilation
  add := fun decl stx _kind => do
    -- `stx` is `pkc_math (str)? (keeping …)? (substituting ident,+)*`: child 1 is the optional
    -- literal override, child 2 the optional `keeping` clause, child 3 the (possibly empty)
    -- sequence of derivation steps.
    let override? : Option String := stx[1][0].isStrLit?
    let keep : KeepPolicy ←
      if stx[2].getNumArgs == 0 then pure .inlineAll
      else
        let namesStx := stx[2][0][1]
        if namesStx.getNumArgs == 0 then pure .keepAll
        else
          -- reject a name that binds nothing: it reads as a rendering instruction that was applied,
          -- and silently doing nothing would leave the equation inlined with no hint why
          let bound ← letBinderNames decl
          let names ← namesStx[0].getSepArgs.mapM fun ident => do
            let n := ident.getId
            unless bound.contains n do
              throwErrorAt ident "`[pkc_math keeping {n}]`: {decl} has no `let` binding named \
                {n}{if bound.isEmpty then "" else s!" (it binds {bound})"}"
            return n
          pure (.keepOnly names)
    let substSteps ← stx[3].getArgs.mapM fun step => do
      -- `step` is ` substituting ident,+`; its child 1 is the comma-separated ident list
      step[1].getSepArgs.mapM fun ident => do
        let n ← realizeGlobalConstNoOverload ident
        unless isSubstitutable (← getEnv) n do
          throwErrorAt ident "`[pkc_math substituting {n}]` cannot substitute {n}: it must be a \
            non-recursive definition (a recursive one would not terminate when inlined)"
        return n
    unless substSteps.isEmpty || override?.isNone do
      throwError "`[pkc_math]` cannot combine a literal LaTeX override with `substituting`: the \
        override replaces the rendering, so there is no equation to derive from"
    unless keep == .inlineAll || override?.isNone do
      throwError "`[pkc_math]` cannot combine a literal LaTeX override with `keeping`: the \
        override replaces the rendering, so there are no bindings to keep"
    let md ← (mathMarkdown decl override? keep substSteps).run'
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
