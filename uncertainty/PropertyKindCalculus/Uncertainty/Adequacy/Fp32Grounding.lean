/-
`PropertyKindCalculus.Uncertainty.Adequacy.Fp32Grounding` — the **binary32 grounding** of the
adequacy layer (Stage 3, `UNCERTAINTY.md` §4.2).

The grid model of `Adequacy.Grid`/`Absorption`/`Soundness` is deliberately abstract (a uniform
spacing `u = ulp`), because absorption and its verdict are *local* statements at one magnitude. This
module records that the abstraction is faithful to a *real* floating-point format by importing
TorchLean's `FP32` — a native Flocq port of IEEE-754 binary32 over `ℝ` — and re-exposing, under
adequacy-layer names, the exact lemmas the grid model localizes:

  * `round32_within_half_ulp` — every binary32 round is within half a ulp of the exact real
    (`FP32.round_abs_error`); the genuine form of `Adequacy.abs_sub_gridRound_le`.
  * `add32_within_half_ulp` / `sub32_within_half_ulp` — each binary32 `+`/`−` is within half a ulp of
    the exact result (`FP32.add_abs_error`, `FP32.sub_abs_error`); the per-operation bound the
    accumulation argument composes.
  * `interval_add_sound` — the sound interval enclosure the adequacy range analysis rests on
    (`Interval.mem_add`): the exact real sum is enclosed by the outward-rounded interval sum.

  * `round32_sterbenz_exact` / `sub32_exact_of_sterbenz` (**A2 at the real binary32 format, Stage
    3.2**) — Sterbenz's theorem lifted from the grid model's `Sterbenz32.flx_sterbenz` to TorchLean's
    genuine `fexp32 = FLTExp (−149) 24` (gradual underflow): a near-equal binary32 subtraction is
    *exact*, `round₃₂ (u − v) = u − v`. Grounded in TorchLean's `round32_sub_exact_of_sterbenz` /
    `FP32.sub_exact_of_sterbenz` (`NN/Floats/FP32/Sterbenz.lean`, added in the Stage-3.2 TorchLean PR).

**Caveat (drives the remaining sub-stage).** TorchLean's entire `FP32`/Flocq layer is
`noncomputable` — `round₃₂ : ℝ → ℝ` is an ℝ-level *specification*, not an executable float — so these
lemmas ground the *proofs*, while the executable `Adequacy` carrier (`Adequacy.lean`) computes over
Lean's `Float`. Bridging the two (executable rounding that provably matches this spec) is Stage 3.3,
which still calls for a TorchLean PR (`UNCERTAINTY.md` §6). Stage 3.2 (this file's Sterbenz grounding)
is now realized at the FLT/`fexp32` format binary32 actually uses.
-/
import PropertyKindCalculus.Uncertainty.Adequacy.Grid
import NN.Floats.FP32.Notation
import NN.Floats.FP32.Error
import NN.Floats.FP32.Sterbenz
import NN.Floats.Interval.Quantized

namespace PropertyKindCalculus.Uncertainty.Adequacy

open TorchLean.Floats

/-- **The binary32 half-ulp rounding bound.** Every FP32 round is within half a ulp of the exact
real — the genuine, Flocq-backed form of the grid model's `Adequacy.abs_sub_gridRound_le`. -/
theorem round32_within_half_ulp (x : ℝ) : |round₃₂ x - x| ≤ eps₃₂ x :=
  FP32.round_abs_error x

/-- **The binary32 addition is within half a ulp** of the exact real sum: the per-operation rounding
bound the accumulation argument composes over an evaluation. -/
theorem add32_within_half_ulp (a b : FP32) :
    |(a + b).val - (a.val + b.val)| ≤ eps₃₂ (a.val + b.val) :=
  FP32.add_abs_error a b

/-- **The binary32 subtraction is within half a ulp** of the exact real difference (a bound that is
*zero* in the Sterbenz regime — cf. `Sterbenz32.flx_sterbenz`). -/
theorem sub32_within_half_ulp (a b : FP32) :
    |(a - b).val - (a.val - b.val)| ≤ eps₃₂ (a.val - b.val) :=
  FP32.sub_abs_error a b

/-- **Sound interval enclosure of addition.** The exact real sum of two enclosed reals is enclosed by
the outward-rounded interval sum — the soundness the adequacy *range* analysis rests on. -/
theorem interval_add_sound {R : Interval.Rounder} {A B : Interval.RInterval} {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ B) : x + y ∈ Interval.RInterval.add R A B :=
  Interval.RInterval.mem_add hx hy

/-- **A2 at the real binary32 format — Sterbenz as a theorem about `round₃₂` (Stage 3.2).** For two
representable binary32 values within a factor of two (`0 < u`, `0 < v`, `u ≤ 2v`, `v ≤ 2u`), the
difference is *exactly* representable, so `round₃₂` is the identity on it: `round₃₂ (u − v) = u − v`.
This is the genuine binary32 realization — over TorchLean's `fexp32 = FLTExp (−149) 24`, gradual
underflow — of the grid model's self-contained `Sterbenz32.flx_sterbenz`, discharging Stage 3.2:
near-equal binary32 subtraction is lossless at *the format the model actually uses*. -/
theorem round32_sterbenz_exact {u v : ℝ}
    (hu : neuralGenericFormat binaryRadix fexp32 u) (hv : neuralGenericFormat binaryRadix fexp32 v)
    (hupos : 0 < u) (hvpos : 0 < v) (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) :
    round₃₂ (u - v) = u - v :=
  TorchLean.Floats.round32_sub_exact_of_sterbenz hu hv hupos hvpos huv hvu

/-- **Sterbenz on the `FP32` scalar type.** The operational form: subtracting two representable,
near-equal binary32 values introduces *no* rounding error — `(a − b).val = a.val − b.val`. The dual
of `sub32_within_half_ulp`, whose half-ulp bound this collapses to *zero* in the Sterbenz regime. -/
theorem sub32_exact_of_sterbenz {a b : FP32}
    (ha : a.IsRepresentable) (hb : b.IsRepresentable)
    (hapos : 0 < a.val) (hbpos : 0 < b.val)
    (hab : a.val ≤ 2 * b.val) (hba : b.val ≤ 2 * a.val) :
    (a - b).val = a.val - b.val :=
  TorchLean.Floats.FP32.sub_exact_of_sterbenz ha hb hapos hbpos hab hba

end PropertyKindCalculus.Uncertainty.Adequacy
