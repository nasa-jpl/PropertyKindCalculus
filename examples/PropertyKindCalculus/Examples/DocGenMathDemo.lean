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

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
public import PropertyKindCalculus.DocGenMath
meta import PropertyKindCalculus.DocGenMath

@[expose] public section Blanket

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

/-- The AVS-style backscatter forward model, rendered on its doc page as
`σ⁰ = a·ndvi + exp(−2·b·ndvi)·c·r + d`.

The `@[pkc_math_symbol]` override gives the left-hand side its conventional notation `σ⁰`;
`@[pkc_math]` (applied after it) renders the whole equation. -/
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

/-! ## Regression pins — notational wrappers

A carrier's numeral injection is notation, not content: `ofN 2` *is* `2`, so
`@[pkc_math_transparent]` renders it as its argument. Without the tag every constant in every
equation carries the name of the coercion (`\mathrm{ofN}\left(2\right)`). The tag belongs only on a
wrapper that really is transparent — one that scales, like a percent conversion, must keep showing
its factor. -/

/-- The carrier's numeral injection: a transparent wrapper. -/
@[pkc_math_transparent]
def ofN (n : Nat) : Quantity dl Float := ⟨n.toFloat⟩

/-- Doubling through the numeral injection. -/
@[pkc_math_symbol "u", pkc_math]
def scaledByTwo (a : Quantity dl Float) : Quantity dl Float := Quantity.mul pk (ofN 2) a

/-- info: u = 2\,a -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``scaledByTwo)
  Lean.logInfo s

/-! ## Regression pin — a record result is a *system* of equations

A model whose result is a record of quantities has no single defining equation: it has one per
field. The lift reads the structure literal as a `record` and the printer renders the aligned
system, which is how such a model is written on paper. Collapsing it into one right-hand side is
what a record-valued definition used to do. -/

/-- Two outputs of one model, as a record. -/
structure Bounds where
  /-- The upper output. -/
  hi : Quantity dl Float
  /-- The lower output. -/
  lo : Quantity dl Float

/-- A record-valued model: renders as the system `hi = a·b`, `lo = a − b`. -/
@[pkc_math]
def spread (a b : Quantity dl Float) : Bounds :=
  { hi := Quantity.mul pk a b, lo := a - b }

/-- info: \begin{aligned} \mathrm{hi} &= a\,b \\ \mathrm{lo} &= a - b \end{aligned} -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``spread)
  Lean.logInfo s

/-! ## Regression pin — a destructuring `let` becomes a `where` equation

`let (x, y) := split a` elaborates to a one-branch `match`. There is no case analysis to show, and
inlining it would repeat the scrutinee once per component, so the binder is named: the pair becomes
one auxiliary equation and the body renders in terms of the names. The docstring pin below is the
whole markdown the attribute writes — equation, `where`, source — so it also pins the block layout
that MathJax needs (each `$$…$$` a top-level block). -/

/-- Splits an input into a pair — the destructured helper. -/
def split (a : Quantity dl Float) : Quantity dl Float × Quantity dl Float := (a, a)

/-- Consumes a destructured pair. -/
@[pkc_math_symbol "D", pkc_math]
def combined (a b : Quantity dl Float) : Quantity dl Float :=
  let (x, y) := split a
  Quantity.mul pk x y + b

/-- info: Consumes a destructured pair.

$$D = x\,y + b$$

where

$$\left(x, y\right) = \mathrm{split}\left(a\right)$$

```lean
def combined (a b : Quantity dl Float) : Quantity dl Float :=
  match split a with
| (x, y) => Quantity.mul pk x y + b
```
-/
#guard_msgs in
run_cmd do
  let doc := (← Lean.findSimpleDocString? (← Lean.getEnv) ``combined).getD "‹none›"
  Lean.logInfo doc

/-! ## Regression pin — `match` is case analysis

A multi-alternative `match` renders as `\begin{cases}`, each branch labelled with the pattern it
holds for. The patterns are read from the matcher's own **equation lemmas**, which is the only place
Lean keeps them — `MatcherInfo` records arities, not patterns.

`byPolarization` writes its alternatives in the *reverse* of `Pol`'s constructor order, so this pin
is what proves the labels come from the equations and not from a guess at constructor order: a guess
would swap the two conditions and publish a wrong equation. -/

/-- A two-way polarization tag. -/
inductive Pol where
  /-- Horizontal. -/
  | hh
  /-- Vertical. -/
  | vv

/-- Case analysis on the polarization, written vertical-first. -/
@[pkc_math_symbol "P", pkc_math]
def byPolarization (p : Pol) (a b : Quantity dl Float) : Quantity dl Float :=
  match p with
  | .vv => Quantity.mul pk a b
  | .hh => a - b

/--
info: P = \begin{cases} a\,b & \text{if } p = \mathrm{vv} \\ a - b & \text{if } p = \mathrm{hh} \end{cases}
-/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``byPolarization)
  Lean.logInfo s

/-! ## Regression pins — `keeping`: the inverse of the `let`-zeta

The lift inlines `let` bindings by default, which is right for one threaded intermediate and ruinous
for a shared one: a Debye denominator used by four outputs is duplicated four times, and the
equation grows past reading. `keeping` binds them instead, as the `where` block of the equation.

`keeping` alone keeps every binding; `keeping d` keeps the named ones and inlines the rest. The
three pins below are the same definition rendered all three ways, so the difference is visible. -/

/-- A model with a shared intermediate: `d` is used by both `s` and the sum. -/
@[pkc_math_symbol "S", pkc_math keeping]
def shared (a b : Quantity dl Float) : Quantity dl Float :=
  let d := a + b
  let s := Quantity.mul pk d d
  s + d

-- inlining everything (the default): `d` appears three times over
/-- info: S = \left(a + b\right)^{2} + a + b -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``shared)
  Lean.logInfo s

-- keeping everything: each binding once, in binding order
/-- info: S = s + d | where \begin{aligned} d &= a + b \\ s &= d^{2} \end{aligned} -/
#guard_msgs in
run_cmd do
  let r ← Lean.Elab.Command.liftTermElabM (quantityToRendering ``shared #[] .keepAll)
  Lean.logInfo (r.equation ++ " | where " ++ (r.whereEqs.getD "‹none›"))

-- keeping only `d`: `s` is inlined around it
/-- info: S = d^{2} + d | where d = a + b -/
#guard_msgs in
run_cmd do
  let r ← Lean.Elab.Command.liftTermElabM (quantityToRendering ``shared #[] (.keepOnly #[`d]))
  Lean.logInfo (r.equation ++ " | where " ++ (r.whereEqs.getD "‹none›"))

/-! ## Regression pins — names in a system

Two refinements that keep a `where` block readable, both about names rather than about math.

**An alias is not an equation.** A definition that binds its outputs with `let` and then packs them
into a record would render `hi = d` above `d = a + b`. When a field's value is nothing but the name
of an auxiliary equation used *exactly once*, the field takes its right-hand side and the equation
goes away. The single-use condition is what stops this from duplicating a shared intermediate — the
second pin keeps `d` precisely because two fields read it. -/

/-- info: hi = a + b (0 auxiliary) -/
#guard_msgs in
#eval do
  let s : MathSystem := { body := .record #[("hi", .sym "d")],
                          aux := #[(.sym "d", .add #[.sym "a", .sym "b"])] }
  let c := s.collapseAliases
  IO.println s!"{prettyEquation MathNotation.ofLatex "F" c.body} ({c.aux.size} auxiliary)"

/-- info: \begin{aligned} hi &= d \\ lo &= -d \end{aligned} (1 auxiliary) -/
#guard_msgs in
#eval do
  let s : MathSystem := { body := .record #[("hi", .sym "d"), ("lo", .neg (.sym "d"))],
                          aux := #[(.sym "d", .add #[.sym "a", .sym "b"])] }
  let c := s.collapseAliases
  IO.println s!"{prettyEquation MathNotation.ofLatex "F" c.body} ({c.aux.size} auxiliary)"

/-! **A re-bound name disambiguates.** A definition may open two blocks with the same local name for
different values (a Debye model binds `ωτ` twice). Keeping both would put two equations with one
left-hand side and two right-hand sides in a single block, so the second becomes `u2` — which the
trailing-digit rule then typesets as a subscript. Inlining the shadowed binding instead reads worse:
it turns `u²` into `a\,b\,a\,b`, because the faithful normalizer folds powers only from *adjacent*
equal factors. -/

/-- A definition that binds `u` twice, for different values. -/
@[pkc_math_symbol "T", pkc_math keeping]
def twiceBound (a b : Quantity dl Float) : Quantity dl Float :=
  let u := a + b
  let x := Quantity.mul pk u u
  let u := a - b
  let y := Quantity.mul pk u u
  x + y

/--
info: T = x + y | where \begin{aligned} u &= a + b \\ x &= u^{2} \\ u_{2} &= a - b \\ y &= u_{2}^{2} \end{aligned}
-/
#guard_msgs in
run_cmd do
  let r ← Lean.Elab.Command.liftTermElabM (quantityToRendering ``twiceBound #[] .keepAll)
  Lean.logInfo (r.equation ++ " | where " ++ (r.whereEqs.getD "‹none›"))

end PropertyKindCalculus.Examples.DocGenMathDemo

end Blanket
