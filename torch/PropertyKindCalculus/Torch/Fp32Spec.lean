/-
`PropertyKindCalculus.Torch.Fp32Spec` — the binary32 rounding-spec vocabulary the uncertainty
layer and the refinement bridge are written in: the exponent grid `fexp32`, the rounding mode
`rnd32`, the real-level rounding operator `round32`, the unit in the last place `ulp32`, its half
`eps32`, and the per-operation error and exactness lemmas over TorchLean's `FP32` (FloatLib's
rounded-real `NF` at binary32 precision, with gradual underflow and no upper exponent bound).

Every name here is an abbreviation of, or a one-line consequence of, FloatLib's format-indexed
rounding theory at `FloatFormat.binary32`: `Model.roundAt`, `Model.ulpAt`, `Model.epsilonAt`,
`Model.abs_roundAt_sub_le`, `Model.roundAt_sub_eq_of_sterbenz`. The grid `Model.fexpOf binary32`
is `fltExp (-149) 24` by computation (`fexp32_eq_fltExp`). TorchLean states its executable
refinement theorems (`toReal_add_eq_round_of_isFinite` and its siblings) against the same
`Model.roundAt`, so a `round32` fact and an executable fact meet with no conversion lemma between
them. A `module` file, like the TorchLean and FloatLib modules it imports.
-/

module

public import NN.Floats.FP32
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz

@[expose] public section Blanket

open FloatLib.Numerics FloatLib.Floats.Formats.Flocq
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open TorchLean.Floats (FP32)

namespace PropertyKindCalculus.Fp32

/-- The binary32 exponent grid: 24 bits of precision with gradual underflow down to `2^-149`
(`fltExp (-149) 24`) and no upper exponent bound; overflow belongs to the executable word. -/
abbrev fexp32 : ℤ → ℤ := Model.fexpOf FloatFormat.binary32

/-- `fexp32` is the Flocq FLT grid binary32 is built on. -/
theorem fexp32_eq_fltExp : fexp32 = fltExp (-149) 24 := rfl

/-- Round to nearest, ties to even: the binary32 default rounding. -/
noncomputable abbrev rnd32 : ℝ → ℤ := nearestEven

/-- Real-level binary32 rounding (`Model.roundAt FloatFormat.binary32`): the operator every
arithmetic operation on `FP32` applies to its exact real result. -/
noncomputable abbrev round32 (x : ℝ) : ℝ := Model.roundAt FloatFormat.binary32 x

/-- One unit in the last place at `x` on the binary32 grid. -/
noncomputable abbrev ulp32 (x : ℝ) : ℝ := Model.ulpAt FloatFormat.binary32 x

/-- Half a unit in the last place at `x`: the distance one nearest-even rounding can move `x`. -/
noncomputable abbrev eps32 (x : ℝ) : ℝ := Model.epsilonAt FloatFormat.binary32 x

/-- Binary32 has a smallest grid step, so its ulp at zero is `2^-149`. -/
@[simp] theorem ulp32_zero : ulp32 0 = bpow binaryRadix (-149) :=
  ulp_zero_FLT (-149) 24 (by norm_num)

/-- Rounding fixes zero: it is on the grid. -/
theorem round32_zero : round32 0 = 0 := Model.roundAt_zero FloatFormat.binary32

/-- **Sterbenz at binary32.** If two positive binary32-representable reals are within a factor of
two, rounding their exact difference is the identity. -/
theorem round32_sub_exact_of_sterbenz {u v : ℝ}
    (hu : genericFormat binaryRadix fexp32 u) (hv : genericFormat binaryRadix fexp32 v)
    (hupos : 0 < u) (hvpos : 0 < v) (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) :
    round32 (u - v) = u - v :=
  Model.roundAt_sub_eq_of_sterbenz FloatFormat.binary32 hu hv hupos hvpos huv hvu

namespace FP32

/-- Every binary32 rounding is within half an ulp of the exact real. -/
theorem round_abs_error (x : ℝ) : |round32 x - x| ≤ eps32 x :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 x

/-- `FP32` addition rounds the exact real sum once, so it lands within half an ulp of it. -/
theorem add_abs_error (a b : FP32) :
    |(a + b).val - (a.val + b.val)| ≤ eps32 (a.val + b.val) :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 (a.val + b.val)

/-- `FP32` subtraction rounds the exact real difference once. -/
theorem sub_abs_error (a b : FP32) :
    |(a - b).val - (a.val - b.val)| ≤ eps32 (a.val - b.val) :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 (a.val - b.val)

/-- `FP32` multiplication rounds the exact real product once. -/
theorem mul_abs_error (a b : FP32) :
    |(a * b).val - (a.val * b.val)| ≤ eps32 (a.val * b.val) :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 (a.val * b.val)

/-- `FP32` division rounds the exact (totalized) real quotient once. -/
theorem div_abs_error (a b : FP32) :
    |(a / b).val - (a.val / b.val)| ≤ eps32 (a.val / b.val) :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 (a.val / b.val)

/-- Subtraction of positive representable `FP32` values within a factor of two is exact. -/
theorem sub_exact_of_sterbenz {a b : FP32}
    (ha : a.IsRepresentable) (hb : b.IsRepresentable)
    (hapos : 0 < a.val) (hbpos : 0 < b.val)
    (hab : a.val ≤ 2 * b.val) (hba : b.val ≤ 2 * a.val) :
    (a - b).val = a.val - b.val :=
  round32_sub_exact_of_sterbenz ha hb hapos hbpos hab hba

end FP32

end PropertyKindCalculus.Fp32

end Blanket
