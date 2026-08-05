/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.DocGenMath.Term

/-!
# Stage 3 — Pretty-print `MathTerm → LaTeX`

An operator-precedence printer that owns **all** parenthesization and spacing, so stages 1–2 never
reason about layout. Precedence: sum (10) < unary minus (15) < product (20) < power (30) < atoms and
self-bracketing forms — `\frac`, function applications, tuples — (40). A subterm is parenthesized
exactly when its own precedence is below the position it sits in.

Tokens are resolved to notation by a caller-supplied `resolve : String → MathNotation` (built in
`DocGenMath.Attr` from the `@[pkc_math_symbol]` registry + heuristics), keeping this module pure and
unit-testable with `MathNotation.ofLatex`. The `MathNotation.operator` flag — and *only* that flag —
selects the juxtaposed prefix layout `\nabla x`; layout is never inferred from the LaTeX itself.
-/

namespace PropertyKindCalculus.DocGenMath

/-- Wrap in `{…}` (a LaTeX group). -/
private def br (s : String) : String := "{" ++ s ++ "}"

/-- Wrap in sizing parentheses. -/
private def paren (s : String) : String := "\\left(" ++ s ++ "\\right)"

/-- The self-precedence of a term (see the module header). -/
private def precOf : MathTerm → Nat
  | .add _    => 10
  | .neg _    => 15
  | .mul _    => 20
  | .pow _ _  => 30
  | .frac _ _ => 40
  | .fn _ _   => 40
  | .tuple _  => 40
  | .sym _    => 40
  | .num _    => 40
  | .record _ => 40
  | .cases _ _ => 40
  | .raw _    => 40

/-- LaTeX macro for a recognized elementary function head (`exp` is handled separately). -/
private def funcMacro : String → Option String
  | "log"  => some "\\log"  | "sin"  => some "\\sin"   | "cos"  => some "\\cos"
  | "tan"  => some "\\tan"  | "sinh" => some "\\sinh"  | "cosh" => some "\\cosh"
  | "tanh" => some "\\tanh" | "asin" => some "\\arcsin"| "acos" => some "\\arccos"
  | "atan" => some "\\arctan"
  | _      => none

/-- Split a signed sum term into its sign and its magnitude, for rendering `a − b` instead of
`a + (−b)`. -/
private def signOf : MathTerm → Bool × MathTerm
  | .neg t            => (true, t)
  | .num n            => if n < 0 then (true, .num (-n)) else (false, .num n)
  | t                 => (false, t)

/-- Stage 3. Render a `MathTerm` as LaTeX, resolving tokens through `resolve`. -/
partial def pretty (resolve : String → MathNotation) (t : MathTerm) : String :=
  go 0 t
where
  /-- Render `t` for a slot requiring precedence `prec`, adding parentheses if needed. -/
  go (prec : Nat) (t : MathTerm) : String :=
    let s := core t
    if precOf t < prec then paren s else s
  /-- Render `t` without regard to the surrounding precedence. -/
  core : MathTerm → String
    | .num n      => toString n
    | .sym s      => (resolve s).latex
    | .raw l      => l
    | .neg t      => "-" ++ go 16 t
    | .pow a b    => go 31 a ++ "^" ++ br (go 0 b)
    | .frac a b   => "\\frac" ++ br (go 0 a) ++ br (go 0 b)
    | .add ts     => renderSum ts
    | .mul ts     => renderProd ts
    | .fn name as => renderFn name as
    | .tuple ts   => paren (String.intercalate ", " (ts.toList.map (go 0 ·)))
    -- a record met *inside* an expression stays inline, `\{ n_d = …,\ k_d = … \}`; only a record
    -- that is the whole right-hand side becomes the aligned system (`prettyEquation` below)
    | .record fs  =>
      "\\left\\{ " ++ String.intercalate ",\\; "
        (fs.toList.map fun (f, v) => (resolve f).latex ++ " = " ++ go 0 v) ++ " \\right\\}"
    | .cases s as => renderCases s as
  /-- A sum `t₀ ± t₁ ± …`, choosing `+`/`−` from each term's sign. -/
  renderSum (ts : Array MathTerm) : String := Id.run do
    if ts.isEmpty then return "0"
    let mut out := ""
    for h : i in [0:ts.size] do
      let (neg, body) := signOf ts[i]
      let bodyStr := go 11 body
      if i == 0 then
        out := (if neg then "-" ++ bodyStr else bodyStr)
      else
        out := out ++ (if neg then " - " else " + ") ++ bodyStr
    return out
  /-- A product, factors joined by thin spaces (`\,`). -/
  renderProd (ts : Array MathTerm) : String :=
    String.intercalate "\\," (ts.toList.map (go 21 ·))
  /-- A `match`, as the conventional brace-and-conditions layout: each branch's value, then the
  pattern it holds for. `\begin{cases}` is AMSmath, which MathJax bundles, so this typesets on the
  doc-gen4 page and in the InfoView without any extra configuration. -/
  renderCases (scrut : MathTerm) (as : Array (MathTerm × MathTerm)) : String :=
    let rows := as.toList.map fun (pat, val) =>
      go 0 val ++ " & \\text{if } " ++ go 0 scrut ++ " = " ++ go 0 pat
    "\\begin{cases} " ++ String.intercalate " \\\\ " rows ++ " \\end{cases}"
  /-- A function application, laid out by head. -/
  renderFn (name : String) (as : Array MathTerm) : String :=
    if name == "exp" && as.size == 1 then
      "e^" ++ br (go 0 as[0]!)
    else if name == "atan2" && as.size == 2 then
      "\\operatorname{atan2}" ++ paren (go 0 as[0]! ++ ", " ++ go 0 as[1]!)
    else match funcMacro name with
      | some mac =>
        -- `\sin x` when the argument is atomic, `\sin(…)` when compound
        if as.size == 1 && precOf as[0]! ≥ 40 then mac ++ " " ++ go 40 as[0]!
        else mac ++ paren (String.intercalate ", " (as.toList.map (go 0 ·)))
      | none =>
        let nota := resolve name
        if as.isEmpty then nota.latex
        -- a notation *registered* as a bare prefix operator juxtaposes its single argument
        else if nota.operator && as.size == 1 then
          nota.latex ++ " " ++ go 40 as[0]!
        else nota.latex ++ paren (String.intercalate ", " (as.toList.map (go 0 ·)))

/-- An aligned block of `lhs = rhs` rows, the AMSmath layout MathJax bundles. One row renders as a
plain equation: a single-line `\begin{aligned}` buys nothing and reads worse. -/
private def alignedRows (rows : Array (String × String)) : String :=
  if h : rows.size = 1 then
    let (l, r) := rows[0]'(by omega)
    l ++ " = " ++ r
  else
    "\\begin{aligned} " ++ String.intercalate " \\\\ "
      (rows.toList.map fun (l, r) => l ++ " &= " ++ r) ++ " \\end{aligned}"

/-- Render a definition's rendering as its equation. A record-valued definition has no single
defining equation — it has one per field — so it renders as the aligned *system* of them, which is
how such a model is written on paper. Everything else is the familiar `lhs = rhs`. -/
def prettyEquation (resolve : String → MathNotation) (lhs : String) (t : MathTerm) : String :=
  match t with
  | .record fs => alignedRows (fs.map fun (f, v) => ((resolve f).latex, pretty resolve v))
  | _          => lhs ++ " = " ++ pretty resolve t

/-- Render the auxiliary equations of a `MathSystem` as one aligned block, or `none` when there are
none. This is the `where` of the equation above it: each kept `let` and each destructured `match`,
once, in the order the definition binds them. -/
def prettyAux (resolve : String → MathNotation) (aux : Array (MathTerm × MathTerm)) :
    Option String :=
  if aux.isEmpty then none
  else some (alignedRows (aux.map fun (l, r) => (pretty resolve l, pretty resolve r)))

end PropertyKindCalculus.DocGenMath
