/-
# Worked example — Stage 3.2: A2 (Sterbenz) at the real binary32 format

Stage 3 proved A2 — near-equal subtraction is exact — over a self-contained `FLX` (fixed-precision,
unbounded-exponent) model (`Sterbenz32.flx_sterbenz`). Stage 3.2 carries it to the format binary32
*actually uses*: TorchLean's `fexp32 = FLTExp (−149) 24` (an `FLT` format with gradual underflow),
via FloatLib's `generic_format_FLT_sterbenz`. This example applies the grounded
theorems (`Fp32Grounding.round32_sterbenz_exact` / `sub32_exact_of_sterbenz`) and confirms the
sorry-free axiom profile.

  * **`round32_sterbenz`.** For representable binary32 `u`, `v` within a factor of two, the exact
    difference is already on the binary32 grid — `round32 (u − v) = u − v`. Symbolic in `u`, `v`
    (the guarantee holds for *every* such pair, so no concrete grid witness is needed — the same
    stance the noncomputable-FP32 `AdequacyDag` example takes).
  * **`fp32_sub_exact`.** The operational form on the `FP32` scalar type: `(a − b).val = a.val −
    b.val` — a near-equal binary32 subtraction is lossless.
  * **`sub32_error_vanishes`.** The `sub32_within_half_ulp` bound (`≤ eps32`) collapses to *exactly*
    zero in the Sterbenz regime.
  * **`flx_model_sterbenz`.** The self-contained `FLX 24` fact from Stage 3 (`3 − 2` stays
    representable) that Stage 3.2 now realizes at the genuine `fexp32` format.

Everything is a **checked fact** (the module builds under CI); the axiom prints confirm no `sorryAx`.
Mathlib- and TorchLean-backed.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy.Fp32Grounding
public import PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.UncertaintyExamples.AdequacySterbenz32

open PropertyKindCalculus.Uncertainty.Adequacy
open TorchLean.Floats
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics (binaryRadix Radix)

/-! ## A2 at the real binary32 format (`fexp32`, gradual underflow) -/

/-- **Sterbenz over `round32`.** For representable binary32 `u`, `v` within a factor of two, the exact
difference is already on the binary32 grid — so `round32` is the identity on it. -/
theorem round32_sterbenz {u v : ℝ}
    (hu : genericFormat binaryRadix fexp32 u) (hv : genericFormat binaryRadix fexp32 v)
    (hupos : 0 < u) (hvpos : 0 < v) (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) :
    round32 (u - v) = u - v :=
  round32_sterbenz_exact hu hv hupos hvpos huv hvu

/-- **Sterbenz on the `FP32` type.** Near-equal representable binary32 subtraction is lossless. -/
theorem fp32_sub_exact {a b : FP32}
    (ha : a.IsRepresentable) (hb : b.IsRepresentable)
    (hapos : 0 < a.val) (hbpos : 0 < b.val) (hab : a.val ≤ 2 * b.val) (hba : b.val ≤ 2 * a.val) :
    (a - b).val = a.val - b.val :=
  sub32_exact_of_sterbenz ha hb hapos hbpos hab hba

/-- **The half-ulp bound collapses to zero.** `sub32_within_half_ulp` bounds the binary32 subtraction
error by `eps32`; in the Sterbenz regime that error is *exactly* `0`. -/
theorem sub32_error_vanishes {a b : FP32}
    (ha : a.IsRepresentable) (hb : b.IsRepresentable)
    (hapos : 0 < a.val) (hbpos : 0 < b.val) (hab : a.val ≤ 2 * b.val) (hba : b.val ≤ 2 * a.val) :
    |(a - b).val - (a.val - b.val)| = 0 := by
  rw [sub32_exact_of_sterbenz ha hb hapos hbpos hab hba]; simp

/-! ## Tie to the self-contained `FLX` model of Stage 3 -/

/-- The local `FLX 24` Sterbenz fact — `3 − 2` stays representable — which Stage 3.2 now realizes at
the genuine `fexp32` format above. -/
theorem flx_model_sterbenz : FLX 24 (3 - 2) :=
  flx_sterbenz (by norm_num) (by norm_num) (by norm_num)
    ⟨3, 0, by norm_num, by norm_num⟩ ⟨2, 0, by norm_num, by norm_num⟩

/-! ## Sorry-free — the axiom profile of the Stage-3.2 theorems -/

/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacySterbenz32.round32_sterbenz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms round32_sterbenz
/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacySterbenz32.fp32_sub_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp32_sub_exact
/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacySterbenz32.sub32_error_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sub32_error_vanishes

end PropertyKindCalculus.UncertaintyExamples.AdequacySterbenz32

end -- pkc-blanket-expose
end -- pkc-blanket
