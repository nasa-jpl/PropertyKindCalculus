/-
`examples.doc_gen_math_demo` — **the worked `@[pkc_math]` rendering example + its regression pins**.

A self-contained model over PKC primitives (a single dimensionless ratio kind, the `Float` carrier).
`avsForward` is the AVS-style backscatter model whose ASCII form motivated this work,
`σ⁰ = a·ndvi + exp(−2·b·ndvi)·c·r + d`; `@[pkc_math]` renders it to LaTeX and appends the `$$…$$` to
the declaration's own docstring, so it typesets on the doc-gen4 page and in the Lean InfoView.

Lives in the `examples/` source tree (library `Examples`) rather than in `DocGenMath` itself, so no
module of the rendering library carries `#eval`/`#guard` — the same split as `UncertaintyExamples`.
The `#guard_msgs` blocks pin the pipeline output so a regression in any stage is a build error: the
pure `normalize`/`pretty` stages first (no environment needed), then the full `Expr → LaTeX` path,
then the docstring the attribute actually writes.

See `RENDERING.md` for the design.
-/
import PropertyKindCalculus
import PropertyKindCalculus.DocGenMath

namespace PropertyKindCalculus.Examples.DocGenMathDemo

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

/-! ## Regression pins — the pure `normalize`/`pretty` stages

`MathNotation.ofLatex` is the identity resolver: print each token as itself, laid out as an ordinary
function head. -/

-- `2·x·x` folds the coefficient and combines the repeated factor into a power.
/-- info: 2\,x^{2} -/
#guard_msgs in
#eval IO.println (pretty MathNotation.ofLatex (normalize (.mul #[.num 2, .sym "x", .sym "x"])))

-- `a + (−1)·b` renders as a subtraction (via the sign-aware sum printer + `−1·x → −x`).
/-- info: a - b -/
#guard_msgs in
#eval IO.println (pretty MathNotation.ofLatex (normalize (.add #[.sym "a", .mul #[.num (-1), .sym "b"]])))

-- a quotient of sums parenthesizes correctly and folds the numeral sum in the numerator.
/-- info: \frac{x + 3}{y} -/
#guard_msgs in
#eval IO.println
  (pretty MathNotation.ofLatex (normalize (.frac (.add #[.sym "x", .num 1, .num 2]) (.sym "y"))))

-- a tuple is self-bracketing and normalizes componentwise; components need no extra parentheses.
/-- info: \left(a, -b, 2\,x\right) -/
#guard_msgs in
#eval IO.println (pretty MathNotation.ofLatex
  (normalize (.tuple #[.sym "a", .mul #[.num (-1), .sym "b"], .mul #[.num 2, .sym "x"]])))

-- a negated factor hoists its sign out of the product, so an exponent reads `e^{-c\,b}` rather
-- than `e^{\left(-c\right)\,b}`. The sign composes with the integer coefficient, not beside it.
/-- info: -c\,b -/
#guard_msgs in
#eval IO.println (pretty MathNotation.ofLatex (normalize (.mul #[.neg (.sym "c"), .sym "b"])))

/-- info: 2\,c\,b -/
#guard_msgs in
#eval IO.println
  (pretty MathNotation.ofLatex (normalize (.mul #[.num (-2), .neg (.sym "c"), .sym "b"])))

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

/-! ## Regression pin — tuples and head layout

A multi-output model (a residual plus its Jacobian columns, say) returns a `Prod.mk` chain. `Prod`
nests to the right, and the lift flattens it, so a triple prints as one `(x, y, z)` rather than as
two nested pairs.

The two helpers pin the head-layout rule. `grad` is *registered* as a bare prefix operator, so its
one argument is juxtaposed; `gain` is not registered, so it prints parenthesized even though its
heuristic upright form `\mathrm{gain}` also begins with a backslash. Layout comes from the
registration, never from the shape of the LaTeX. Neither body matters here — the lift renders a
named helper by its head and never unfolds it. -/

/-- An unregistered named helper: prints as `\mathrm{gain}\left(a\right)`. -/
def gain (a : Quantity dl Float) : Quantity dl Float := Quantity.mul pk a a

/-- A named helper registered as a bare prefix operator: prints as `\nabla a`. -/
@[pkc_math_symbol "\\nabla" operator]
def grad (a : Quantity dl Float) : Quantity dl Float := a

/-- Three columns returned as a triple: exercises the `Prod.mk` flattening and both head layouts. -/
@[pkc_math_symbol "J", pkc_math]
def columns (a b : Quantity dl Float) :
    Quantity dl Float × Quantity dl Float × Quantity dl Float :=
  (gain a, grad b, Quantity.mul pk a b)

/-- info: J = \left(\mathrm{gain}\left(a\right), \nabla b, a\,b\right) -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``columns)
  Lean.logInfo s

/-! ## Regression pin — configuration constants

A model's named constants live in a configuration structure and are read through a field projection
(`cfg.scale`). `@[pkc_math_config]` on the *structure* says those fields are constants of the model,
so the projection renders as the qualified symbol `\mathrm{DemoConfig.scale}` and the configuration
value is elided — instead of `\mathrm{scale}\left(\mathrm{cfg}\right)`, which strips the field of the
type it belongs to and applies a value that tells the reader nothing. The tag is what makes this
safe: an untagged structure keeps the ordinary application layout, so `Prod.fst` is unaffected. -/

/-- A configuration type: one dimensionless scale factor, the demo's sole configured constant. -/
@[pkc_math_config]
structure DemoConfig where
  /-- The scale factor. -/
  scale : Quantity dl Float

/-- Reads a configuration constant. -/
@[pkc_math_symbol "g", pkc_math]
def scaled (cfg : DemoConfig) (a : Quantity dl Float) : Quantity dl Float :=
  Quantity.mul pk cfg.scale a

/-- info: g = \mathrm{DemoConfig.scale}\,a -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``scaled)
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

/-! ## Regression pins — derivations by substitution

`@[pkc_math substituting f]` shows the equation as written *and* the same equation with `f` inlined.
Each `substituting` clause is one step, applying the union of the clauses up to it, so the equations
refine one another the way a textbook derivation does. Substitution is delta, hence
meaning-preserving: every line still denotes exactly what the definition computes (the **F** tier of
`RENDERING.md` §5). It is not a licence to assert algebra — a literal `@[pkc_math "…"]` override and
`substituting` are mutually exclusive and rejected together.

`decay` also exercises the interaction of all three notational rules at once: substituting it brings
a configuration constant into the exponent, where the hoisted sign lets it read `e^{-\mathrm{
DemoConfig.scale}\,b}` rather than `e^{\left(-\mathrm{DemoConfig.scale}\right)\,b}`. -/

/-- A named helper with its own notation, folded by default and substituted on request. -/
@[pkc_math_symbol "\\tau"]
def decay (cfg : DemoConfig) (b : Quantity dl Float) : Quantity dl Float :=
  Quantity.exp tk ((⟨0⟩ : Quantity dl Float) - Quantity.mul pk cfg.scale b)

/-- One derivation step. -/
@[pkc_math_symbol "F", pkc_math substituting decay]
def model (cfg : DemoConfig) (a b : Quantity dl Float) : Quantity dl Float :=
  Quantity.mul pk (decay cfg b) a

/-- info: F = \tau\left(\mathrm{cfg}, b\right)\,a -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``model)
  Lean.logInfo s

/-- info: F = e^{-\mathrm{DemoConfig.scale}\,b}\,a -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatexSubst ``model #[``decay])
  Lean.logInfo s

/-- The residual of `model`: two cumulative steps, so the reader sees the call, then the call
expanded, then the constant it bottoms out in. -/
@[pkc_math_symbol "R", pkc_math substituting model substituting decay]
def residual (cfg : DemoConfig) (a b s : Quantity dl Float) : Quantity dl Float :=
  s - model cfg a b

/-- info: The residual of `model`: two cumulative steps, so the reader sees the call, then the call
expanded, then the constant it bottoms out in.

$$R = s - F\left(\mathrm{cfg}, a, b\right)$$

**Derivation**

1. substituting `model`:

$$R = s - \tau\left(\mathrm{cfg}, b\right)\,a$$

2. substituting `decay`:

$$R = s - e^{-\mathrm{DemoConfig.scale}\,b}\,a$$

```lean
def residual (cfg : DemoConfig) (a b s : Quantity dl Float) : Quantity dl Float :=
  s - model cfg a b
```
-/
#guard_msgs in
run_cmd do
  let doc := (← Lean.findSimpleDocString? (← Lean.getEnv) ``residual).getD "‹none›"
  Lean.logInfo doc

end PropertyKindCalculus.Examples.DocGenMathDemo
