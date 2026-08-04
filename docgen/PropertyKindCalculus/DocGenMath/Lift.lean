/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import Lean
import PropertyKindCalculus
import PropertyKindCalculus.DocGenMath.Term

/-!
# Stage 1 — Lift `Lean.Expr → MathTerm`

Walk the *authored surface* of a definition's value (never `whnf`/unfold — that would collapse
`Quantity.mul h a b` into `Quantity.mk (a.magnitude * b.magnitude)` and destroy the notation we want
to show). We match the PKC combinator alphabet by its head symbol and keep only the value operands,
dropping the kind-law `Prop` witnesses, the instance arguments, the carrier/kind implicits, and any
`mdata`. Associativity is flattened here, so `a + b + c` and `a·b·c` become single n-ary nodes.

A definition's authored value often threads intermediate results through `let` bindings (`let τ :=
exp …; …`). Those are `zeta`-reduced on the way in — the bound value is substituted into the body —
so the body renders in terms of the model's operators rather than falling to the opaque-leaf branch.
This is a presentation-only inlining (it duplicates a `let`-bound subterm if it is used more than
once); it does not `delta`-unfold *named* helpers, so a `let x := f a` still shows `f a`.

The lift is **total and defensive**: any head it does not special-case becomes a generic `fn`
(keeping only the explicit arguments), and any leaf it cannot read becomes a `sym` of its
pretty-printed form. It never fails, so rendering degrades gracefully on unfamiliar models rather
than crashing the attribute.
-/

namespace PropertyKindCalculus.DocGenMath

open Lean Meta

/-- Splice a term into an n-ary sum's argument array (flatten nested `add`). -/
private def addArgs : MathTerm → Array MathTerm
  | .add ts => ts
  | t       => #[t]

/-- Splice a term into an n-ary product's argument array (flatten nested `mul`). -/
private def mulArgs : MathTerm → Array MathTerm
  | .mul ts => ts
  | t       => #[t]

/-- The last argument of an application (the innermost operand of a unary combinator). -/
private def lastArg (args : Array Expr) : Expr := args[args.size - 1]!

/-- The last two arguments (the operands of a binary combinator, regardless of how many
implicit/instance arguments precede them). -/
private def lastTwo (args : Array Expr) : Expr × Expr :=
  (args[args.size - 2]!, args[args.size - 1]!)

/-- The names of the transcendental/trig unary functions, rendered as `fn <base> #[arg]`. -/
private def unaryFns : List Name :=
  [``PropertyKindCalculus.Quantity.exp, ``PropertyKindCalculus.Quantity.log,
   ``PropertyKindCalculus.Quantity.sin, ``PropertyKindCalculus.Quantity.cos,
   ``PropertyKindCalculus.Quantity.tan, ``PropertyKindCalculus.Quantity.sinh,
   ``PropertyKindCalculus.Quantity.cosh, ``PropertyKindCalculus.Quantity.tanh,
   ``PropertyKindCalculus.Quantity.asin, ``PropertyKindCalculus.Quantity.acos,
   ``PropertyKindCalculus.Quantity.atan]

/-- Keep only the explicitly-bound arguments of `fn` applied to `args` (drop implicits, instances,
and strict-implicits), for the generic `fn` fallback on an unrecognized head. -/
private def explicitArgs (fn : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let finfo ← getFunInfo fn
  let mut out := #[]
  for h : i in [0:args.size] do
    let a := args[i]
    if hi : i < finfo.paramInfo.size then
      if finfo.paramInfo[i].binderInfo == .default then out := out.push a
    else
      out := out.push a
  return out

/-- Stage 1. Lift an already-elaborated value `Expr` to the presentation IR. -/
partial def liftExpr (e : Expr) : MetaM MathTerm := do
  match e with
  | .mdata _ e'        => liftExpr e'
  | .letE _ _ v b _    => liftExpr (b.instantiate1 v)   -- zeta: inline the `let`-bound value
  | .lit (.natVal n)   => return .num (Int.ofNat n)
  | .fvar fid          => return .sym (toString (← fid.getUserName))
  | .bvar _            => return .sym "?"        -- should not occur after `lambdaTelescope`
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const name _ => liftApp name args e
    | .fvar fid =>
      let nm := toString (← fid.getUserName)
      if args.isEmpty then return .sym nm
      else return .fn nm (← (← explicitArgs fn args).mapM liftExpr)
    | _ => return .sym (toString (← ppExpr e))
where
  /-- Lift an application whose head is the constant `name`. -/
  liftApp (name : Name) (args : Array Expr) (e : Expr) : MetaM MathTerm := do
    let fn := e.getAppFn
    -- numerals: `@OfNat.ofNat α n inst` — the numeral is the raw `Nat` literal argument
    if name == ``OfNat.ofNat then
      if let some n := args.findSome? (fun a => match a with
          | .lit (.natVal k) => some k | _ => none) then
        return .num (Int.ofNat n)
    -- coercions: drop and descend into the underlying value
    if name == ``Nat.cast || name == ``Int.cast || name == ``NatCast.natCast
        || name == ``IntCast.intCast then
      if args.size ≥ 1 then return ← liftExpr (lastArg args)
    -- the `Quantity` wrapper: `⟨r⟩` — render its magnitude
    if name == ``PropertyKindCalculus.Quantity.mk then
      if args.size ≥ 1 then return ← liftExpr (lastArg args)
    -- binary ring operators (ergonomic `+ - * /` and the named kind-gated forms)
    if args.size ≥ 2 then
      let (x, y) := lastTwo args
      if name == ``HAdd.hAdd || name == ``PropertyKindCalculus.Quantity.add then
        return .add (addArgs (← liftExpr x) ++ addArgs (← liftExpr y))
      if name == ``HSub.hSub || name == ``PropertyKindCalculus.Quantity.sub then
        return .add (addArgs (← liftExpr x) ++ #[.neg (← liftExpr y)])
      if name == ``HMul.hMul || name == ``PropertyKindCalculus.Quantity.mul then
        return .mul (mulArgs (← liftExpr x) ++ mulArgs (← liftExpr y))
      if name == ``HDiv.hDiv || name == ``PropertyKindCalculus.Quantity.div then
        return .frac (← liftExpr x) (← liftExpr y)
      if name == ``HPow.hPow then
        return .pow (← liftExpr x) (← liftExpr y)
      if name == ``PropertyKindCalculus.Quantity.atan2 then
        return .fn "atan2" #[← liftExpr x, ← liftExpr y]
    -- unary negation
    if name == ``Neg.neg && args.size ≥ 1 then
      return .neg (← liftExpr (lastArg args))
    -- unary transcendental/trig functions: keep the last (value) operand, drop the witness
    if unaryFns.contains name && args.size ≥ 1 then
      return .fn (baseName' name) #[← liftExpr (lastArg args)]
    -- generic fallback: a named application, keeping only explicit operands
    let expl ← explicitArgs fn args
    if expl.isEmpty then return .sym (toString name)
    else return .fn (toString name) (← expl.mapM liftExpr)
  /-- The final component of `name`, as a bare string (for `fn` heads of known functions). -/
  baseName' (name : Name) : String := name.getString!

end PropertyKindCalculus.DocGenMath
