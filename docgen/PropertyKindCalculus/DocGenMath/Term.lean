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
  displays it rather than as three nested pairs.
* `record` is a *structure literal*: a model whose result is a record of quantities
  (`MironovNK`, with its seven refractive-index parameters) has no single defining equation — it has
  a **system** of them, one per field. Each field carries its projection's declaration name, so the
  left-hand side of its equation resolves through the registry like any other token.
* `cases` is a `match`: one `(pattern, value)` alternative per branch. The pattern is itself a
  `MathTerm` (a constructor application, or a bare `sym` for a nullary constructor), so it resolves
  to notation the same way the values do. -/
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
  /-- A structure literal, as `(projection name, value)` pairs in field order. -/
  | record (fields : Array (String × MathTerm))
  /-- A `match`: the scrutinee and one `(pattern, value)` alternative per branch. -/
  | cases (scrutinee : MathTerm) (alts : Array (MathTerm × MathTerm))
  /-- Verbatim LaTeX. The lift's last resort for a leaf it cannot read — escaped `\text{…}`, never
  raw Lean source — and the printer emits it unchanged. Keeping this distinct from `sym` is what
  guarantees an unreadable term degrades to *valid* LaTeX: a `sym` is a token to be resolved through
  the registry, so feeding it pretty-printed Lean (with its braces, backslashes and line breaks)
  produced malformed math on the published page. -/
  | raw (latex : String)
  deriving Inhabited, Repr, BEq

namespace MathTerm

/-- Smart constructor for a difference, kept as `add #[a, neg b]` (the canonical sum form). -/
def sub (a b : MathTerm) : MathTerm := .add #[a, .neg b]

/-- A rough structural size, used only to order factors deterministically (atoms before compounds)
so the faithful normalizer's sort is stable and total. -/
partial def weight : MathTerm → Nat
  | .num _      => 0
  | .sym _      => 1
  | .raw _      => 1
  | .neg t      => 1 + t.weight
  | .pow a b    => 1 + a.weight + b.weight
  | .frac a b   => 1 + a.weight + b.weight
  | .fn _ args  => 1 + args.foldl (· + ·.weight) 1
  | .add ts     => 1 + ts.foldl (· + ·.weight) 0
  | .mul ts     => 1 + ts.foldl (· + ·.weight) 0
  | .tuple ts   => 1 + ts.foldl (· + ·.weight) 0
  | .record fs  => 1 + fs.foldl (fun acc (_, t) => acc + t.weight) 0
  | .cases s as => 1 + s.weight + as.foldl (fun acc (p, t) => acc + p.weight + t.weight) 0

/-- How many times the atom `x` occurs in a term. -/
partial def countSym (x : String) : MathTerm → Nat
  | .sym s      => if s == x then 1 else 0
  | .num _      => 0
  | .raw _      => 0
  | .neg t      => t.countSym x
  | .pow a b    => a.countSym x + b.countSym x
  | .frac a b   => a.countSym x + b.countSym x
  | .fn _ as    => as.foldl (fun acc t => acc + t.countSym x) 0
  | .add ts     => ts.foldl (fun acc t => acc + t.countSym x) 0
  | .mul ts     => ts.foldl (fun acc t => acc + t.countSym x) 0
  | .tuple ts   => ts.foldl (fun acc t => acc + t.countSym x) 0
  | .record fs  => fs.foldl (fun acc (_, t) => acc + t.countSym x) 0
  | .cases s as => s.countSym x + as.foldl (fun acc (p, t) => acc + p.countSym x + t.countSym x) 0

end MathTerm

/-- A rendered term together with the auxiliary equations its kept `let` bindings and destructuring
`match`es were named by — the `where` of a textbook equation.

The lift zeta-inlines `let`s by default, which is right for a model that threads one intermediate
through one use. It is wrong for a model that shares a subexpression across many outputs: inlining a
Debye denominator into seven field equations both explodes the LaTeX and hides the structure the
author wrote. `@[pkc_math keeping]` binds those `let`s here instead, so each appears once, by name,
below the equation it serves. A destructuring `match` (`let (n, k) := …`) always lands here: its
binders have no other rendering, and `(n, k) = …` is what the source says. -/
structure MathSystem where
  /-- The main term (the right-hand side of the equation, or a `record` system of them). -/
  body : MathTerm
  /-- Auxiliary `lhs = rhs` equations, in the order the definition binds them. -/
  aux : Array (MathTerm × MathTerm) := #[]
  deriving Inhabited, Repr, BEq

/-- A term with no auxiliary equations — what every rendering produced before `keeping` existed. -/
def MathSystem.ofTerm (t : MathTerm) : MathSystem := { body := t }

/-- Collapse *aliases* in a record system: a field whose value is nothing but the name of an
auxiliary equation used nowhere else takes that equation's right-hand side, and the equation goes
away.

This is what a definition that binds its outputs with `let` and then packs them into a record looks
like — `let nd := …; … ; { nd := nd, … }` — and rendering it literally gives a field equation
`n_d = \mathrm{nd}` sitting above `\mathrm{nd} = …`, which says nothing twice. Restricted to a
single occurrence, so nothing is ever duplicated: an intermediate that two fields share stays a
named equation in the `where` block, which is the whole point of keeping it. -/
def MathSystem.collapseAliases (s : MathSystem) : MathSystem :=
  match s.body with
  | .record fs => Id.run do
    let uses (x : String) : Nat :=
      fs.foldl (fun acc (_, t) => acc + t.countSym x) 0
        + s.aux.foldl (fun acc (l, r) => acc + r.countSym x
            + (match l with | .sym _ => 0 | l => l.countSym x)) 0
    let mut fields := #[]
    let mut dropped : Array String := #[]
    for (f, v) in fs do
      match v with
      | .sym x =>
        match s.aux.find? (fun (l, _) => l == MathTerm.sym x) with
        | some (_, rhs) =>
          if uses x == 1 then
            fields := fields.push (f, rhs); dropped := dropped.push x
          else fields := fields.push (f, v)
        | none => fields := fields.push (f, v)
      | _ => fields := fields.push (f, v)
    return { body := .record fields,
             aux := s.aux.filter fun (l, _) =>
               match l with | .sym x => !dropped.contains x | _ => true }
  | _ => s

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
