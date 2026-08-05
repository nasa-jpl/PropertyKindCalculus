/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import Lean

/-!
# `MathTerm` — the presentation IR for PKC math rendering

The middle representation of the three-stage rendering pipeline (see `RENDERING.md` §5):

1. **Lift** `Lean.Expr → MathTerm` (`DocGenMath.Lift`) — strip `Prop`/instance/`mdata` noise,
   flatten associativity to n-ary `mul`/`add`.
2. **Normalize/Recognize** `MathTerm → MathTerm` (`DocGenMath.Normalize`) — faithful,
   meaning-preserving cleanups (numeral folding, `x·x → x²`, `a + (−b) → a − b`, flatten).
3. **Pretty** `MathTerm → String` (`DocGenMath.Pretty`) — an operator-precedence printer that
   owns every parenthesis and space, so stages 1–2 never think about layout.

`MathTerm` is deliberately a *presentation* AST, not a semantic one: it is what we want the reader
to see, one step before LaTeX. It is carrier-agnostic and PKC-agnostic (it only imports `Lean`), so
the pipeline can be unit-tested without building PKC or doc-gen4.
-/

namespace PropertyKindCalculus.DocGenMath

open Lean

/-- The presentation IR. A tree of the mathematical *notation* we intend to render, already free of
the kind-law witnesses, instance arguments, and coercions that clutter the raw `Expr`.

Design notes:
* `mul`/`add` are **n-ary** — associativity is flattened during the lift, so the printer emits
  `a\,b\,c` and `a + b + c` without a spine of nested binary nodes.
* Subtraction is *not* a constructor: `a - b` is represented as `add #[a, neg b]`, so the sum
  printer can render mixed `+`/`−` chains uniformly (`a − b + c`).
* `fn` is the generic escape for any named application the lift did not special-case
  (`exp`, `sin`, `curl`, a user helper, …). Its `name` is the *raw* head (a Lean declaration name
  or a bare identifier); the printer resolves it to a LaTeX symbol/notation via the registry.
* `tuple` is n-ary for the same reason `mul`/`add` are: a `Prod.mk` chain is right-nested, and the
  lift flattens it, so `(a, b, c, d)` prints the way Lean's own anonymous-constructor notation
  displays it rather than as three nested pairs. -/
inductive MathTerm where
  /-- An atom: a bound variable, a free parameter, or an unrecognized constant, by its raw name. -/
  | sym  (name : String)
  /-- An integer literal (numerals are folded here; `Float`/rational literals fall back to `sym`). -/
  | num  (n : Int)
  /-- Unary negation. -/
  | neg  (t : MathTerm)
  /-- An n-ary sum. Terms may themselves be `neg`, giving mixed `+`/`−` chains. -/
  | add  (ts : Array MathTerm)
  /-- An n-ary product (juxtaposition, printed with thin spaces). -/
  | mul  (ts : Array MathTerm)
  /-- A quotient `a / b`, printed as `\frac{a}{b}`. -/
  | frac (a b : MathTerm)
  /-- A power `a ^ b`. -/
  | pow  (a b : MathTerm)
  /-- A named function application `name(args)` — `exp`, trig, `log`, or a user-named operator.
  The printer decides layout (`e^{…}` for `exp`, `\sin …`, `\nabla\times …`, `name(…)`, …). -/
  | fn   (name : String) (args : Array MathTerm)
  /-- An n-ary tuple `(a, b, …)`: a flattened right-nested `Prod.mk` chain. -/
  | tuple (ts : Array MathTerm)
  deriving Inhabited, Repr, BEq

namespace MathTerm

/-- Smart constructor for a difference, kept as `add #[a, neg b]` (the canonical sum form). -/
def sub (a b : MathTerm) : MathTerm := .add #[a, .neg b]

/-- A rough structural size, used only to order factors deterministically (atoms before compounds)
so the faithful normalizer's sort is stable and total. -/
partial def weight : MathTerm → Nat
  | .num _      => 0
  | .sym _      => 1
  | .neg t      => 1 + t.weight
  | .pow a b    => 1 + a.weight + b.weight
  | .frac a b   => 1 + a.weight + b.weight
  | .fn _ args  => 1 + args.foldl (· + ·.weight) 1
  | .add ts     => 1 + ts.foldl (· + ·.weight) 0
  | .mul ts     => 1 + ts.foldl (· + ·.weight) 0
  | .tuple ts   => 1 + ts.foldl (· + ·.weight) 0

end MathTerm

/-- A token resolved to notation: the LaTeX it prints as, plus how it lays out when it *heads* an
application (`DocGenMath.Registry.resolveToken` builds these, `DocGenMath.Pretty` consumes them).

`operator` is the author's declaration — through `@[pkc_math_symbol "…" operator]` — that the
notation is a bare prefix operator (`\nabla`, `\partial`), to be juxtaposed with its single argument
instead of parenthesized. It is never inferred from the shape of the LaTeX: the heuristic upright
form `\mathrm{…}` also begins with a backslash, and a helper that merely *has* a multi-letter name
must still print as `\mathrm{gain}\left(a\right)`. -/
structure MathNotation where
  /-- The LaTeX for the token itself. -/
  latex : String
  /-- Print a one-argument application as juxtaposition (`\nabla x`) rather than `\mathrm{f}(x)`. -/
  operator : Bool := false
  deriving Inhabited, Repr, BEq

/-- The plain notation for a piece of LaTeX: print it as-is, laid out as an ordinary function head.
This is the identity resolver the pure-stage tests use. -/
def MathNotation.ofLatex (latex : String) : MathNotation := { latex }

end PropertyKindCalculus.DocGenMath
