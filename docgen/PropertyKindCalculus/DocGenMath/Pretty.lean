/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/

module

public import PropertyKindCalculus.DocGenMath.Term

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

@[expose] public section Blanket

namespace PropertyKindCalculus.DocGenMath

/-- Wrap in `{…}` (a LaTeX group). -/
def br (s : String) : String := "{" ++ s ++ "}"

/-- Wrap in sizing parentheses. -/
def paren (s : String) : String := "\\left(" ++ s ++ "\\right)"

/-- The self-precedence of a term (see the module header). -/
def precOf : MathTerm → Nat
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
def funcMacro : String → Option String
  | "log"  => some "\\log"  | "sin"  => some "\\sin"   | "cos"  => some "\\cos"
  | "tan"  => some "\\tan"  | "sinh" => some "\\sinh"  | "cosh" => some "\\cosh"
  | "tanh" => some "\\tanh" | "asin" => some "\\arcsin"| "acos" => some "\\arccos"
  | "atan" => some "\\arctan"
  | _      => none

/-- Split a signed sum term into its sign and its magnitude, for rendering `a − b` instead of
`a + (−b)`. -/
def signOf : MathTerm → Bool × MathTerm
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

/-! ## Breaking a wide equation across lines

A rendered equation has no width limit, and some are far wider than a documentation page: a
four-component Jacobian tuple comes out around 240 characters of LaTeX on one line, which makes the
whole doc-gen4 page scroll horizontally.

MathJax cannot be asked to fix this. Automatic display-math line breaking is a MathJax **4** feature
(`displayOverflow: 'linebreak'`), and doc-gen4 loads MathJax 3 — the `v4.34.0` tag this package
resolves still does (`DocGen4/Output/Template.lean` names `mathjax@3`). So the break has to be authored into the LaTeX, and this is the right
stage to author it: `Pretty` already owns every space and parenthesis, and `MathTerm` is *n-ary*, so
the seams a reader would break at (`add`'s summands, `tuple`'s components) are explicit nodes rather
than something to recover from a string.

Breaking is purely presentational — the same term, laid out over more lines — so it stays inside the
**F (faithful)** tier that `RENDERING.md` §5 fixes as the standing policy.

### Estimating width

We need the *rendered* width, which is not the LaTeX length: `\mathrm{}` costs eight characters and
no glyphs, `\left(` costs six and one, `\tau` costs four and one. So the estimate walks the term,
charging each leaf its resolved notation's glyph count, and accounts for the two constructors that
lay out *vertically* rather than horizontally — a fraction is as wide as the wider of its parts, not
their sum, and a superscript renders small. It does not have to be exact; it has to be good enough to
decide "does this need breaking". -/

/-- The visible width of a piece of LaTeX, in glyphs: braces, sub/superscript markers and spacing
macros cost nothing, a structural macro costs nothing, and any other control sequence
(`\tau`, `\nabla`, `\sigma`) is one glyph. -/
partial def latexWidth (s : String) : Nat :=
  go s.toList 0
where
  go : List Char → Nat → Nat
    | [], acc => acc
    | '\\' :: rest, acc =>
      let (name, rest') := rest.span Char.isAlpha
      if name.isEmpty then
        -- `\,` `\;` `\!` `\\` — spacing or a row break, no glyph
        go (rest.drop 1) acc
      else if ["mathrm", "left", "right", "begin", "end", "big", "Big"].contains
                (String.ofList name) then
        go rest' acc
      else go rest' (acc + 1)
    | c :: rest, acc =>
      if c == '{' || c == '}' || c == '^' || c == '_' then go rest acc
      else go rest (acc + 1)

/-- An estimate of `t`'s rendered width in glyphs, used only to decide whether to break it. -/
partial def estWidth (resolve : String → MathNotation) : MathTerm → Nat
  | .num n      => (toString n).length
  | .sym s      => latexWidth (resolve s).latex
  | .raw l      => latexWidth l
  | .neg t      => 1 + estWidth resolve t
  -- a fraction stacks, so it is as wide as its wider part; a superscript renders small
  | .frac a b   => 2 + max (estWidth resolve a) (estWidth resolve b)
  | .pow a b    => estWidth resolve a + (estWidth resolve b * 7 + 9) / 10
  | .add ts     => ts.foldl (fun acc t => acc + 3 + estWidth resolve t) 0
  | .mul ts     => ts.foldl (fun acc t => acc + 1 + estWidth resolve t) 0
  | .tuple ts   => 2 + ts.foldl (fun acc t => acc + 2 + estWidth resolve t) 0
  | .fn name as =>
    latexWidth (resolve name).latex + 2 + as.foldl (fun acc t => acc + 2 + estWidth resolve t) 0
  -- these two already lay out vertically, so their width is that of their widest row
  | .record fs  => fs.foldl (fun acc (f, v) => max acc (latexWidth f + 3 + estWidth resolve v)) 0
  | .cases s as =>
    estWidth resolve s
      + as.foldl (fun acc (p, v) => max acc (estWidth resolve p + estWidth resolve v + 8)) 0

/-- The width past which an equation is broken across lines.

Chosen against doc-gen4's own layout: its declaration column is about 100 glyphs of body text at the
default size, and display math renders slightly larger, so ~90 is where a formula starts to push the
page. Deliberately generous — a break costs vertical space and an unnecessary one reads worse than a
slightly wide line. -/
def wideThreshold : Nat := 90

/-- An aligned block of `lhs = rhs` rows, the AMSmath layout MathJax bundles. One row renders as a
plain equation: a single-line `\begin{aligned}` buys nothing and reads worse. -/
def alignedRows (rows : Array (String × String)) : String :=
  if h : rows.size = 1 then
    let (l, r) := rows[0]'(by omega)
    l ++ " = " ++ r
  else
    "\\begin{aligned} " ++ String.intercalate " \\\\ "
      (rows.toList.map fun (l, r) => l ++ " &= " ++ r) ++ " \\end{aligned}"

/-- A wide sum broken before each top-level `+`/`−`, continuation rows indented under the first.

The conventional textbook layout for a long sum, and the break points are the `add` node's own
elements — no string has to be re-parsed to find them. -/
def brokenSum (resolve : String → MathNotation) (lhs : String) (ts : Array MathTerm) :
    String := Id.run do
  let mut rows : Array String := #[]
  for h : i in [0:ts.size] do
    let (neg, body) := signOf ts[i]
    let s := pretty resolve body
    if i == 0 then rows := rows.push (lhs ++ " &= " ++ (if neg then "-" ++ s else s))
    else rows := rows.push ("&\\quad " ++ (if neg then "- " else "+ ") ++ s)
  return "\\begin{aligned} " ++ String.intercalate " \\\\ " rows.toList ++ " \\end{aligned}"

/-- A wide tuple broken one component per row, as the column vector it is.

`pmatrix` rather than a broken `\left(…\right)`: a wide tuple in this library is a Jacobian's columns
or a model's several outputs, which *is* a column vector, and `pmatrix` is AMSmath, which MathJax
bundles — so it needs no configuration on either the doc-gen4 page or the InfoView. -/
def brokenTuple (resolve : String → MathNotation) (lhs : String) (ts : Array MathTerm) :
    String :=
  lhs ++ " = \\begin{pmatrix} "
    ++ String.intercalate " \\\\ " (ts.toList.map (pretty resolve ·))
    ++ " \\end{pmatrix}"

/-- Render a definition's rendering as its equation. A record-valued definition has no single
defining equation — it has one per field — so it renders as the aligned *system* of them, which is
how such a model is written on paper. Everything else is the familiar `lhs = rhs`.

A right-hand side wider than `wideThreshold` is broken at its own top-level seams: a sum before each
`+`/`−`, a tuple one component per row. Anything else is left alone — a single wide product or
function application has no seam a reader would break at, and inventing one would read worse than the
horizontal scroll. -/
def prettyEquation (resolve : String → MathNotation) (lhs : String) (t : MathTerm) : String :=
  match t with
  | .record fs => alignedRows (fs.map fun (f, v) => ((resolve f).latex, pretty resolve v))
  | .add ts =>
    if latexWidth lhs + 3 + estWidth resolve t > wideThreshold then brokenSum resolve lhs ts
    else lhs ++ " = " ++ pretty resolve t
  | .tuple ts =>
    if latexWidth lhs + 3 + estWidth resolve t > wideThreshold then brokenTuple resolve lhs ts
    else lhs ++ " = " ++ pretty resolve t
  | _ => lhs ++ " = " ++ pretty resolve t

/-- Render the auxiliary equations of a `MathSystem` as one aligned block, or `none` when there are
none. This is the `where` of the equation above it: each kept `let` and each destructured `match`,
once, in the order the definition binds them. -/
def prettyAux (resolve : String → MathNotation) (aux : Array (MathTerm × MathTerm)) :
    Option String :=
  if aux.isEmpty then none
  else some (alignedRows (aux.map fun (l, r) => (pretty resolve l, pretty resolve r)))

end PropertyKindCalculus.DocGenMath

end Blanket
