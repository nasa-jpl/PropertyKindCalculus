/-
`examples.tape_host_float_model` — **the host `Float` is a specification, not an oracle.**

The per-backend obligation the one-program/N-printers architecture leaves to trust is "each of the
printer's fixed forms means, in the host language, what `SLExpr.denote` means in Lean's `Float`".
That sentence is only as good as what Lean's `Float` *is*. On the pinned toolchain it is a structure
over `Float.Model`, the bit-level IEEE 754 binary64 model in core (`Init.Data.Float.Model`:
sign/exponent/mantissa unpacking, round-to-nearest-even, NaN and infinity rules), and `+ - * /`,
`sqrt`, `abs`, `≤`, `<`, `==`, `toBits`/`ofBits` are *defined* through that model — the C externs
are compiled replacements of a definition, not the definition. So for every op of the alphabet but
two, `BinOp.eval`/`UnOp.eval` unfold, by `rfl`, to model arithmetic, and the obligation reads: the
host's binary64 `+` is IEEE round-to-nearest-even — a conformance claim about the host, not a claim
about Lean. The two exceptions are `Float.exp` and `Float.log`: `opaque` externs (libm) with no
model; they are the whole of what "libm" means in the trusted base.

The theorems below pin each clause by `rfl`; their axiom profile is the standard three the model's
own definitions use (guarded `#print axioms`) — no `sorry`, no extern taken as an axiom. Builds under the
`Examples` glob.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeStraightLine
public import Batteries.Data.Float.Lemmas
meta import PropertyKindCalculus.Torch.Paradigm.TapeStraightLine

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.TapeHostFloatModel

open PropertyKindCalculus.Paradigm.TapeCodegen.SL (BinOp UnOp)

/-! ## The binary alphabet: model arithmetic by definition -/

theorem BinOp_eval_add_model (a b : Float) :
    BinOp.eval .add a b = Float.ofModel (a.toModel + b.toModel) := rfl

theorem BinOp_eval_sub_model (a b : Float) :
    BinOp.eval .sub a b = Float.ofModel (a.toModel - b.toModel) := rfl

theorem BinOp_eval_mul_model (a b : Float) :
    BinOp.eval .mul a b = Float.ofModel (a.toModel * b.toModel) := rfl

theorem BinOp_eval_div_model (a b : Float) :
    BinOp.eval .div a b = Float.ofModel (a.toModel / b.toModel) := rfl

/-- `min`/`max` are Lean's `≤`-conditionals (`minOfLe`/`maxOfLe`), and `≤` on `Float` is the model's
`≤` — so the ternary every printer writes is decided by the model's comparison, NaN included. -/
theorem BinOp_eval_min_ite (a b : Float) :
    BinOp.eval .min a b = (if a ≤ b then a else b) := rfl

theorem BinOp_eval_max_ite (a b : Float) :
    BinOp.eval .max a b = (if a ≤ b then b else a) := rfl

theorem Float_le_model (a b : Float) : (a ≤ b) = (a.toModel ≤ b.toModel) := rfl

theorem Float_lt_model (a b : Float) : (a < b) = (a.toModel < b.toModel) := rfl

/-! ## The unary alphabet: `sqrt` and `abs` in the model; `exp` and `log` outside it

`Float.exp` and `Float.log` are `opaque` in core (`@[extern "exp"]`, `@[extern "log"]`): no
model clause exists to state, which is the precise content of "libm is trusted". -/

theorem UnOp_eval_sqrt_model (a : Float) :
    UnOp.eval .sqrt a = Float.ofModel a.toModel.sqrt := rfl

theorem UnOp_eval_abs_model (a : Float) :
    UnOp.eval .abs a = Float.ofModel a.toModel.abs := rfl

/-! ## The bit view is the model's -/

theorem Float_toBits_model (a : Float) : a.toBits = a.toModel.toBits := rfl

/-- Two values with the same bits are the same value — Batteries' `Float.toBits_inj`, which the
chain theorem's const-leaf case already rests on; it is a theorem of the model, not an axiom. -/
theorem toBits_inj {a b : Float} : a.toBits = b.toBits ↔ a = b := Float.toBits_inj

/-! The model clauses are definitional; the axioms are those of `Float.Model`'s definitions. -/

/--
info: 'PropertyKindCalculus.Examples.TapeHostFloatModel.BinOp_eval_add_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms BinOp_eval_add_model

/--
info: 'PropertyKindCalculus.Examples.TapeHostFloatModel.UnOp_eval_sqrt_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnOp_eval_sqrt_model

/-- info: 'PropertyKindCalculus.Examples.TapeHostFloatModel.toBits_inj' depends on axioms: [propext] -/
#guard_msgs in #print axioms toBits_inj

end PropertyKindCalculus.Examples.TapeHostFloatModel

end Blanket
