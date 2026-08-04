/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus
import PropertyKindCalculus.DocGenMath

/-!
# Demo — a `@[pkc_math]`-rendered `Quantity` definition + regression pins

A self-contained example over PKC primitives (a single dimensionless ratio kind, the `Float`
carrier). `avsForward` is the AVS-style backscatter model whose ASCII form motivated this work,
`σ⁰ = a·ndvi + exp(−2·b·ndvi)·c·r + d`; `@[pkc_math]` renders it to LaTeX and appends the `$$…$$`
to the declaration's own docstring, so it typesets on the doc-gen4 page and in the Lean InfoView.

The `#guard_msgs` blocks pin the pipeline output so a regression in any stage is a build error:
the first three exercise the pure `normalize`/`pretty` stages (no environment needed), the last the
full `Expr → LaTeX` path on `avsForward`.
-/

namespace PropertyKindCalculus.DocGenMath.Demo

open PropertyKindCalculus
open PropertyKindCalculus.DocGenMath

/-! ## Kinds and witnesses (all dimensionless / ratio-scale, so the gates discharge by `rfl`) -/

/-- A single dimensionless ratio kind used for every quantity in the demo. -/
def dl : KindOfProperty := { id := "1", scale := .ratio }

/-- The product kind-law `dl = dl × dl` (all ratio-scale). -/
theorem pk : ProductKind dl dl dl := ⟨rfl, rfl, rfl⟩

/-- The transcendental kind-law `dl → dl` (dimensionless in, dimensionless out). -/
theorem tk : TranscendentalKind dl dl := ⟨rfl, rfl⟩

/-! ## The rendered model -/

/-- The AVS-style backscatter forward model. Rendered on its doc page as
`σ⁰ = a·ndvi + exp(−2·b·ndvi)·c·r + d`. The `@[pkc_math_symbol]` override gives the left-hand side
its conventional notation `σ⁰`; `@[pkc_math]` (applied after it) renders the whole equation. -/
@[pkc_math_symbol "\\sigma^0", pkc_math]
def avsForward (a b c d r ndvi : Quantity dl Float) : Quantity dl Float :=
  Quantity.mul pk a ndvi
    + Quantity.mul pk
        (Quantity.mul pk (Quantity.exp tk (Quantity.mul pk (Quantity.mul pk (⟨-2⟩ : Quantity dl Float) b) ndvi)) c)
        r
    + d

/-! ## Regression pins — the pure `normalize`/`pretty` stages -/

-- `2·x·x` folds the coefficient and combines the repeated factor into a power.
/-- info: 2\,x^{2} -/
#guard_msgs in
#eval IO.println (pretty id (normalize (.mul #[.num 2, .sym "x", .sym "x"])))

-- `a + (−1)·b` renders as a subtraction (via the sign-aware sum printer + `−1·x → −x`).
/-- info: a - b -/
#guard_msgs in
#eval IO.println (pretty id (normalize (.add #[.sym "a", .mul #[.num (-1), .sym "b"]])))

-- a quotient of sums parenthesizes correctly and folds the numeral sum in the numerator.
/-- info: \frac{x + 3}{y} -/
#guard_msgs in
#eval IO.println (pretty id (normalize (.frac (.add #[.sym "x", .num 1, .num 2]) (.sym "y"))))

/-! ## Regression pin — the full `Expr → LaTeX` path on `avsForward`

The `@[pkc_math_symbol]` override resolves the LHS to `\sigma^0`; the local variable `ndvi` maps to
`\mathrm{NDVI}` through the dictionary; the `⟨-2⟩` literal folds into the exponent's coefficient. -/

/-- info: \sigma^0 = a\,\mathrm{NDVI} + e^{-2\,b\,\mathrm{NDVI}}\,c\,r + d -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``avsForward)
  Lean.logInfo s

/-! ## Regression pin — the Stage-1 `let`-zeta

A definition that threads an intermediate through a `let` renders in terms of its operators — the
bound value is inlined on the way into the lift (`Lift.liftExpr`'s `.letE` case), so the body is not
an opaque leaf. `letExample` squares `a` through a `let` and adds it back; the pipeline inlines the
binding, folds `a·a → a²`, and prints the sum. This is what lets kinded models written with named
intermediates (`let τ := exp …; …`) render at all. -/

/-- A `let`-bound intermediate `sq = a·a`, added back: exercises the lift's `let`-zeta. -/
@[pkc_math_symbol "q"]
def letExample (a : Quantity dl Float) : Quantity dl Float :=
  let sq := Quantity.mul pk a a
  sq + a

/-- info: q = a^{2} + a -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``letExample)
  Lean.logInfo s

/-! ## Regression pin — the attribute writes the equation into the declaration's docstring

`@[pkc_math]` appends to the declaration's own docstring (or sets it, when there is none) both the
rendered `$$…$$` equation and the definition's Lean source as a ```` ```lean ```` block, reading it
back with `findSimpleDocString?`. `noted` carries an authored one-line docstring, so this pins the
append: the prose is preserved, then the equation, then the source. Because the docstring is what
`findDocString?` returns, this is exactly what doc-gen4 and the InfoView render. -/

/-- Base backscatter. -/
@[pkc_math_symbol "\\gamma", pkc_math]
def noted (a b : Quantity dl Float) : Quantity dl Float := Quantity.mul pk a b

/-- info: Base backscatter.

$$\gamma = a\,b$$

```lean
def noted (a b : Quantity dl Float) : Quantity dl Float :=
  Quantity.mul pk a b
```
-/
#guard_msgs in
run_cmd do
  let doc := (← Lean.findSimpleDocString? (← Lean.getEnv) ``noted).getD "‹none›"
  Lean.logInfo doc

end PropertyKindCalculus.DocGenMath.Demo
