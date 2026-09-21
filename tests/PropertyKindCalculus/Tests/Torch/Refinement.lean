/-
# Torch-tier validation probes — the multiplicative rungs of the R10 bridge

`Tests.Core.Representation` exercises `Quantity.{mul,div}_refines` over a toy lossy carrier,
where the rounding is visible and both capstones are shown non-vacuous. This file carries the
same two laws down to the carriers they exist for: TorchLean's binary32 *rounding spec* `FP32`,
where the bridge is unconditional, and its *executable* `IEEE32Exec`, where it is not.

The executable rung is the point of the file. `Quantity.div_refines_exec` needs four facts about
the actual bits — both operands decode to dyadics, the divisor's mantissa is nonzero, the quotient
is finite — and the probes below discharge all four on concrete binary32 values and then **refute
two of them at a zero denominator**. So the claim that the hazard lives one rung below the
specification is checked here rather than asserted in a docstring: at `FP32` a zero divisor is
harmless because `ℝ` totalizes `x / 0`, and at `IEEE32Exec` the same division is not finite and its
divisor's mantissa is zero.
-/

import PropertyKindCalculus.Torch.Fp32

open TorchLean.Floats
open TorchLean.Floats.IEEE754
open FloatLib.Floats (ExecFloat)
open FloatLib.Floats.ExecFloat.Binary (isFinite toModel)

namespace PropertyKindCalculus.Tests.Refinement

open PropertyKindCalculus

/-! ## Kinds, so the bridge is applied across a kind change -/

/-- Length, ratio-scale (so it may multiply). -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }

/-- Area — the product kind of two lengths. -/
def areaK : KindOfProperty := { id := "area", scale := .ratio }

theorem prodLen : ProductKind lengthK lengthK areaK := .ofRatio _ _ _
theorem quotArea : QuotientKind areaK lengthK lengthK := .ofRatio _ _ _

/-! ## The spec rung — `FP32`, unconditional

`NF` arithmetic is "compute in `ℝ`, then round" for `*` and `/` exactly as for `+`, so both
instances hold by `rfl` and the two capstones apply with no side condition. -/

/-- Two binary32 spec lengths. -/
noncomputable def fTwo : Quantity lengthK FP32 := ⟨((2 : Nat) : FP32)⟩
noncomputable def fThree : Quantity lengthK FP32 := ⟨((3 : Nat) : FP32)⟩

-- Inhabitation: the kind-crossing bridge at the binary32 rounding spec.
theorem fp32_mul_refines :
    (Quantity.toSpec (Quantity.mul prodLen fTwo fThree) : Quantity areaK ℝ)
      = Quantity.roundBy (CarrierRefinement.round (E := FP32))
          (Quantity.mul prodLen (Quantity.toSpec fTwo) (Quantity.toSpec fThree)) :=
  Quantity.mul_refines_fp32 prodLen fTwo fThree

theorem fp32_div_refines :
    (Quantity.toSpec (Quantity.div quotArea (Quantity.mul prodLen fTwo fThree) fTwo)
        : Quantity lengthK ℝ)
      = Quantity.roundBy (CarrierRefinement.round (E := FP32))
          (Quantity.div quotArea
            (Quantity.toSpec (Quantity.mul prodLen fTwo fThree)) (Quantity.toSpec fTwo)) :=
  Quantity.div_refines_fp32 quotArea (Quantity.mul prodLen fTwo fThree) fTwo

/-! ## The exec rung — `IEEE32Exec`, with the bits discharged

`2.0` and `3.0` as binary32 bit patterns, their decoded dyadics written out, and the two
conditional refinements applied with every hypothesis settled by `decide`. -/

/-- Binary32 `2.0` and `3.0`, by bit pattern. -/
def two : IEEE32Exec := ExecFloat.Binary.ofBits32 0x40000000
/-- Binary32 `3.0`. -/
def three : IEEE32Exec := ExecFloat.Binary.ofBits32 0x40400000

/-- Exec length `2.0`. -/
def qTwo : Quantity lengthK IEEE32Exec := ⟨two⟩
/-- Exec length `3.0`. -/
def qThree : Quantity lengthK IEEE32Exec := ⟨three⟩
/-- Exec area `6.0`, formed by the executable multiplication. -/
def qSix : Quantity areaK IEEE32Exec := ⟨ExecFloat.mul two three⟩

/-- The dyadic decoding of `2.0`. -/
def dTwo : FloatLib.Numerics.Dyadic := { negative := false, significand := 8388608, exponent := -22 }
/-- The dyadic decoding of `3.0`. -/
def dThree : FloatLib.Numerics.Dyadic := { negative := false, significand := 12582912, exponent := -22 }
/-- The dyadic decoding of `6.0`. -/
def dSix : FloatLib.Numerics.Dyadic := { negative := false, significand := 12582912, exponent := -21 }

-- The written-out dyadics are the real decodings, not guesses.
#guard (toModel two).toDyadic? == some dTwo
#guard (toModel three).toDyadic? == some dThree
#guard (toModel (ExecFloat.mul two three)).toDyadic? == some dSix

-- Inhabitation: the executable product and quotient refine, every hypothesis discharged.
theorem exec_mul_refines :
    (Quantity.mul prodLen qTwo qThree).toRealExec
      = Quantity.roundBy IEEE32Exec.fp32Round
          (Quantity.mul prodLen qTwo.toRealExec qThree.toRealExec) :=
  Quantity.mul_refines_exec prodLen qTwo qThree (by decide)

theorem exec_div_refines :
    (Quantity.div quotArea qSix qTwo).toRealExec
      = Quantity.roundBy IEEE32Exec.fp32Round
          (Quantity.div quotArea qSix.toRealExec qTwo.toRealExec) :=
  Quantity.div_refines_exec quotArea qSix qTwo (dx := dSix) (dy := dTwo)
    (by decide) (by decide) (by decide) (by decide)

/-! ## And the same division at a zero denominator, refuted

Two of `div_refines_exec`'s four hypotheses fail outright when the divisor is zero: the divisor's
decoded mantissa *is* zero, and the executable quotient is not finite. This is the hazard the
unconditional spec-side `DivRefinement FP32 ℝ` cannot express — a mean whose total weight is zero
does not produce a wrong number at this rung, it produces one the bridge refuses to relate to any
real quotient at all. -/

#guard ((toModel (0 : IEEE32Exec)).toDyadic?.map (·.significand)) == some 0
#guard isFinite (ExecFloat.div two 0) == false

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Tests.Refinement.fp32_mul_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp32_mul_refines

/-- info: 'PropertyKindCalculus.Tests.Refinement.fp32_div_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp32_div_refines

/-- info: 'PropertyKindCalculus.Tests.Refinement.exec_mul_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exec_mul_refines

/-- info: 'PropertyKindCalculus.Tests.Refinement.exec_div_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exec_div_refines

end PropertyKindCalculus.Tests.Refinement
