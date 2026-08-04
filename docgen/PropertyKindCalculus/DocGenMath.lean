/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.DocGenMath.Term
import PropertyKindCalculus.DocGenMath.Registry
import PropertyKindCalculus.DocGenMath.Lift
import PropertyKindCalculus.DocGenMath.Normalize
import PropertyKindCalculus.DocGenMath.Pretty
import PropertyKindCalculus.DocGenMath.Attr

/-!
# `DocGenMath` — typeset math on doc-gen4 pages for PKC `Quantity` definitions

A docs-only library (never imported by the PKC core spine) that renders a `@[pkc_math]`-annotated
`Quantity` definition as human-friendly LaTeX on its generated documentation page, via a three-stage
presentation pipeline (see `RENDERING.md` §5):

  `Lean.Expr`  ──Lift──▶  `MathTerm`  ──Normalize──▶  `MathTerm`  ──Pretty──▶  `LaTeX`

* `DocGenMath.Term`      — the presentation IR.
* `DocGenMath.Lift`      — Stage 1: walk the authored surface, drop witnesses/instances, flatten.
* `DocGenMath.Normalize` — Stage 2: faithful cleanups (numeral fold, `x·x → x²`, scalars-first).
* `DocGenMath.Pretty`    — Stage 3: precedence printer to LaTeX.
* `DocGenMath.Registry`  — `@[pkc_math_symbol]` notation overrides + atom heuristics.
* `DocGenMath.Attr`      — the `@[pkc_math]` attribute; hands the LaTeX to doc-gen4's `addDeclMath`.

The rendering is **faithful** (the F tier): the LaTeX denotes exactly what the definition computes.
-/
