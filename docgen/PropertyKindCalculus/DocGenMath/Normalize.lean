/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/

module

public import PropertyKindCalculus.DocGenMath.Term

/-!
# Stage 2 — Normalize the presentation IR (faithful)

Meaning-preserving cleanups, all sound under ring/field laws, so the LaTeX still *denotes exactly
what the definition computes* (the **F** — faithful — tier of `RENDERING.md` §5):

* flatten nested `add`/`mul` (belt-and-braces after the lift);
* fold integer literals (`2·3 → 6`, `2 + 3 → 5`) and drop the multiplicative/additive identities
  (`1·x → x`, `x + 0 → x`), simplify `(−1)·x → −x` and double negation;
* combine adjacent equal factors into a power (`x·x → x²`);
* move the numeric coefficient to the front of a product (`b·2·ndvi → 2·b·ndvi`), a stable partition
  that leaves the *symbolic* factor order the author chose untouched;
* hoist a product's sign out of it (`(−x)·y·z → −(x·y·z)`), so an exponent reads
  `e^{-c\,b\,\mathrm{NDVI}}` rather than `e^{\left(-c\right)\,b\,\mathrm{NDVI}}`. The sign is
  collected from the integer coefficient *and* from any negated factors, so it composes with the
  `(−1)·x → −x` rule above rather than duplicating it.

Sum term order is **preserved** (a model's `a·ndvi + … + d` reads in the author's order); only the
commutative *product* is reordered, and only to hoist the scalar. Editorial regrouping/factoring
(the **E**/**P** tiers) is deliberately *not* done here.
-/

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.DocGenMath

/-- Read a term as an integer coefficient, seeing through a leading negation. -/
def asInt? : MathTerm → Option Int
  | .num n       => some n
  | .neg t       => (asInt? t).map (- ·)
  | _            => none

/-- Combine runs of *adjacent, structurally-equal* factors into powers: `x·x·x → x³`.
(Non-adjacent equal factors are left alone — the lift keeps authored order, and this is enough for
the common `x*x` case without a full commutative regrouping, which would be an E-tier move.) -/
def groupPowers (fs : Array MathTerm) : Array MathTerm := Id.run do
  let mut out : Array MathTerm := #[]
  let mut i := 0
  while h : i < fs.size do
    let base := fs[i]
    let mut cnt := 1
    while i + cnt < fs.size && fs[i + cnt]! == base do
      cnt := cnt + 1
    out := out.push (if cnt == 1 then base else .pow base (.num (Int.ofNat cnt)))
    i := i + cnt
  return out

/-- Stage 2. Normalize a `MathTerm`, faithfully. -/
partial def normalize : MathTerm → MathTerm
  | .num n      => .num n
  | .sym s      => .sym s
  | .raw l      => .raw l
  | .neg t      =>
    match normalize t with
    | .num n  => .num (-n)
    | .neg t' => t'
    | t'      => .neg t'
  | .pow a b    => .pow (normalize a) (normalize b)
  | .frac a b   => .frac (normalize a) (normalize b)
  | .fn n args  => .fn n (args.map normalize)
  | .tuple ts   => .tuple (ts.map normalize)
  | .record fs  => .record (fs.map fun (f, t) => (f, normalize t))
  -- values only: a pattern is a constructor application the reader matches against literally, so
  -- folding inside it would rewrite what the author wrote the branch on
  | .cases s as => .cases (normalize s) (as.map fun (p, t) => (p, normalize t))
  | .add ts     => Id.run do
    -- normalize + flatten
    let flat : Array MathTerm := (ts.map normalize).foldl
      (fun acc t => match t with | .add us => acc ++ us | t => acc.push t) #[]
    -- fold the integer terms, drop zeros, keep the symbolic terms in order
    let mut c : Int := 0
    let mut rest : Array MathTerm := #[]
    for t in flat do
      match asInt? t with
      | some k => c := c + k
      | none   => rest := rest.push t
    let terms := if c == 0 then rest else rest.push (.num c)
    match terms.size with
    | 0 => .num 0
    | 1 => terms[0]!
    | _ => .add terms
  | .mul ts     => Id.run do
    let flat : Array MathTerm := (ts.map normalize).foldl
      (fun acc t => match t with | .mul us => acc ++ us | t => acc.push t) #[]
    -- fold the integer coefficients (product); absorbing zero. A negated factor contributes its
    -- sign to the coefficient and enters `rest` unnegated, hoisting the sign out of the product.
    let mut coeff : Int := 1
    let mut rest : Array MathTerm := #[]
    for t in flat do
      match asInt? t with
      | some k => coeff := coeff * k
      | none   =>
        match t with
        | .neg u => coeff := -coeff; rest := rest.push u
        | u      => rest := rest.push u
    if coeff == 0 then return .num 0
    rest := groupPowers rest
    -- reassemble: scalar magnitude first, then the symbolic factors in authored order, with the
    -- sign (from the coefficient and from any hoisted negations) wrapped around the whole product
    if rest.isEmpty then
      return .num coeff
    let neg := coeff < 0
    let mag := coeff.natAbs
    let factors : Array MathTerm :=
      if mag == 1 then rest else #[.num (Int.ofNat mag)] ++ rest
    let core : MathTerm :=
      if factors.size == 1 then factors[0]! else .mul factors
    return (if neg then .neg core else core)

end PropertyKindCalculus.DocGenMath

end -- pkc-blanket-expose
end -- pkc-blanket
