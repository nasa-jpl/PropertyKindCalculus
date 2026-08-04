/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.DocGenMath.Term

/-!
# Stage 2 — Normalize the presentation IR (faithful)

Meaning-preserving cleanups, all sound under ring/field laws, so the LaTeX still *denotes exactly
what the definition computes* (the **F** — faithful — tier of `RENDERING.md` §5):

* flatten nested `add`/`mul` (belt-and-braces after the lift);
* fold integer literals (`2·3 → 6`, `2 + 3 → 5`) and drop the multiplicative/additive identities
  (`1·x → x`, `x + 0 → x`), simplify `(−1)·x → −x` and double negation;
* combine adjacent equal factors into a power (`x·x → x²`);
* move the numeric coefficient to the front of a product (`b·2·ndvi → 2·b·ndvi`), a stable partition
  that leaves the *symbolic* factor order the author chose untouched.

Sum term order is **preserved** (a model's `a·ndvi + … + d` reads in the author's order); only the
commutative *product* is reordered, and only to hoist the scalar. Editorial regrouping/factoring
(the **E**/**P** tiers) is deliberately *not* done here.
-/

namespace PropertyKindCalculus.DocGenMath

/-- Read a term as an integer coefficient, seeing through a leading negation. -/
private def asInt? : MathTerm → Option Int
  | .num n       => some n
  | .neg t       => (asInt? t).map (- ·)
  | _            => none

/-- Combine runs of *adjacent, structurally-equal* factors into powers: `x·x·x → x³`.
(Non-adjacent equal factors are left alone — the lift keeps authored order, and this is enough for
the common `x*x` case without a full commutative regrouping, which would be an E-tier move.) -/
private def groupPowers (fs : Array MathTerm) : Array MathTerm := Id.run do
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
  | .neg t      =>
    match normalize t with
    | .num n  => .num (-n)
    | .neg t' => t'
    | t'      => .neg t'
  | .pow a b    => .pow (normalize a) (normalize b)
  | .frac a b   => .frac (normalize a) (normalize b)
  | .fn n args  => .fn n (args.map normalize)
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
    -- fold the integer coefficients (product); absorbing zero
    let mut coeff : Int := 1
    let mut rest : Array MathTerm := #[]
    for t in flat do
      match asInt? t with
      | some k => coeff := coeff * k
      | none   => rest := rest.push t
    if coeff == 0 then return .num 0
    rest := groupPowers rest
    -- reassemble: scalar coefficient first, then the symbolic factors in authored order
    if rest.isEmpty then
      return .num coeff
    let factors : Array MathTerm :=
      if coeff == 1 then rest
      else if coeff == -1 then #[]        -- handled by wrapping in `neg` below
      else #[.num coeff] ++ rest
    let core : MathTerm :=
      match factors.size with
      | 0 => (if rest.size == 1 then rest[0]! else .mul rest)   -- coeff == -1 path
      | 1 => factors[0]!
      | _ => .mul factors
    return (if coeff == -1 then .neg core else core)

end PropertyKindCalculus.DocGenMath
