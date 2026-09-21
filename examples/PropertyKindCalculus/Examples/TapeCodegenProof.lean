/-
`examples.tape_codegen_proof` — **codegen faithfulness as a theorem** (not just the concrete-pixel
`#guard` of `examples.tape_codegen_demo`).

The megakernel codegen (`paradigm.tape_codegen`) renders the recorded, CSE'd tape node-for-node into
straight-line C. Its correctness rests on one fact: the recorded tape faithfully computes the source
`[NumCarrier α]` kernel *for all inputs*. Here we prove exactly that for the AVS Stage-2 kernel
`resJac`, composing the `paradigm.tape_parity` `Evaluates` alphabet — "parity is a `rfl`, not a
hope." Because the codegen emits the same DAG the tape stores, and `evalTape` interprets each node
with the matching scalar op (`cOp`), this `Evaluates` result is the semantic core of codegen
faithfulness; the remaining rendering table (`cOp`/`cExpr` ↔ the tape ops) is a per-op correspondence.
-/
import PropertyKindCalculus.Examples.TapeCodegenDemo
import PropertyKindCalculus.Torch.Paradigm.TapeParity

open Spec TorchLean
open TorchLean TorchLean.Tensor
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm (TapeBuilder)
open PropertyKindCalculus.Paradigm.TapeParity
open PropertyKindCalculus.Examples.AvsForward
  (attenuation resJac ofN attenuationQ deployed lavsForwardQ lavsResidualQ lavsJacResidualQ)

namespace PropertyKindCalculus.Examples.TapeCodegenProof

-- Several columns (∂a, ∂c, ∂d) don't depend on every parameter, so their faithfulness proofs
-- leave some interface hypotheses unused — that is the point, not a defect.
set_option linter.unusedVariables false

/-- Scalar tape shape (one pixel / one thread). -/
abbrev S : Shape := Shape.scalar
abbrev TB := TapeBuilder S
abbrev T := Tensor Float S

/-! ### Constants of the kernel evaluate to their filled tensors -/

theorem eval_zero : Evaluates (0 : TB) (Tensor.full S (0 : Float)) := Evaluates_const 0
theorem eval_one  : Evaluates (1 : TB) (Tensor.full S (1 : Float)) := Evaluates_const 1
theorem eval_two  : Evaluates (ofN 2 : TB) (Tensor.full S ((2 : Nat) : Float)) := Evaluates_const _

/-! ### Spec-level twins of the kernel (the eager `Spec` value each output must carry) -/

/-- `exp((0−2)·b·ndvi)` at the `Spec` carrier — the value the recorded `attenuation` builder must
carry. -/
def attenSpec (vb vndvi : T) : T :=
  expSpec (mulSpec (mulSpec (subSpec (Tensor.full S (0 : Float)) (Tensor.full S ((2 : Nat) : Float))) vb) vndvi)

/-- The five `Spec`-level outputs (residual + 4 Jacobian columns), mirroring `resJac`'s association. -/
def resSpec (va vb vc vd vndvi vr vs0 : T) : T :=
  subSpec vs0 (addSpec (addSpec (mulSpec va vndvi)
    (mulSpec (mulSpec (attenSpec vb vndvi) vc) vr)) vd)
def jaSpec (vndvi : T) : T := subSpec (Tensor.full S (0 : Float)) vndvi
def jbSpec (vb vc vd_unused vndvi vr : T) : T :=
  mulSpec (mulSpec (mulSpec (mulSpec (Tensor.full S ((2 : Nat) : Float)) vndvi) vc) vr) (attenSpec vb vndvi)
def jcSpec (vb vndvi vr : T) : T := subSpec (Tensor.full S (0 : Float)) (mulSpec (attenSpec vb vndvi) vr)
def jdSpec : T := subSpec (Tensor.full S (0 : Float)) (Tensor.full S (1 : Float))

/-! ### Faithfulness: the recorded builders carry exactly the `Spec` values, for all inputs -/

variable {a b c d ndvi r s0 : TB} {va vb vc vd vndvi vr vs0 : T}

/-- The recorded `attenuation` sub-kernel computes `attenSpec` for all inputs. -/
theorem attenuation_faithful (hb : Evaluates b vb) (hn : Evaluates ndvi vndvi) :
    Evaluates (attenuation (α := TB) b ndvi) (attenSpec vb vndvi) := by
  simp only [attenuation, attenuationQ, deployed, attenSpec,
    Quantity.exp_magnitude, Quantity.mul_magnitude, Quantity.sub_magnitude]
  exact Evaluates_exp (Evaluates_mul (Evaluates_mul (Evaluates_sub eval_zero eval_two) hb) hn)

/-- The recorded residual output carries the source residual value, for all inputs. -/
theorem residual_faithful
    (ha : Evaluates a va) (hb : Evaluates b vb) (hc : Evaluates c vc) (hd : Evaluates d vd)
    (hn : Evaluates ndvi vndvi) (hr : Evaluates r vr) (hs0 : Evaluates s0 vs0) :
    Evaluates (resJac (α := TB) a b c d ndvi r s0).1 (resSpec va vb vc vd vndvi vr vs0) := by
  simp only [resJac, lavsResidualQ, lavsForwardQ, resSpec,
    Quantity.sub_magnitude, Quantity.add_magnitude, Quantity.mul_magnitude]
  exact Evaluates_sub hs0
    (Evaluates_add (Evaluates_add (Evaluates_mul ha hn)
      (Evaluates_mul (Evaluates_mul (attenuation_faithful hb hn) hc) hr)) hd)

/-- ∂/∂a column. -/
theorem ja_faithful (hn : Evaluates ndvi vndvi) :
    Evaluates (resJac (α := TB) a b c d ndvi r s0).2.1 (jaSpec vndvi) := by
  simp only [resJac, lavsJacResidualQ, jaSpec, Quantity.sub_magnitude]
  exact Evaluates_sub eval_zero hn

/-- ∂/∂b column. -/
theorem jb_faithful (hb : Evaluates b vb) (hc : Evaluates c vc) (hn : Evaluates ndvi vndvi)
    (hr : Evaluates r vr) :
    Evaluates (resJac (α := TB) a b c d ndvi r s0).2.2.1 (jbSpec vb vc vd vndvi vr) := by
  simp only [resJac, lavsJacResidualQ, deployed, jbSpec, Quantity.mul_magnitude]
  exact Evaluates_mul (Evaluates_mul (Evaluates_mul (Evaluates_mul eval_two hn) hc) hr)
    (attenuation_faithful hb hn)

/-- ∂/∂c column. -/
theorem jc_faithful (hb : Evaluates b vb) (hn : Evaluates ndvi vndvi) (hr : Evaluates r vr) :
    Evaluates (resJac (α := TB) a b c d ndvi r s0).2.2.2.1 (jcSpec vb vndvi vr) := by
  simp only [resJac, lavsJacResidualQ, jcSpec, Quantity.sub_magnitude, Quantity.mul_magnitude]
  exact Evaluates_sub eval_zero (Evaluates_mul (attenuation_faithful hb hn) hr)

/-- ∂/∂d column. -/
theorem jd_faithful :
    Evaluates (resJac (α := TB) a b c d ndvi r s0).2.2.2.2 jdSpec := by
  simp only [resJac, lavsJacResidualQ, jdSpec, Quantity.sub_magnitude]
  exact Evaluates_sub eval_zero eval_one

-- Axiom audit: these must rest only on the standard axioms (no `sorryAx`).
/-- info: 'PropertyKindCalculus.Examples.TapeCodegenProof.residual_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms residual_faithful

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenProof.attenuation_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attenuation_faithful

end PropertyKindCalculus.Examples.TapeCodegenProof
