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

**Caveat (drives the follow-up sub-stages).** TorchLean's entire `FP32`/Flocq layer is
`noncomputable` — `round₃₂ : ℝ → ℝ` is an ℝ-level *specification*, not an executable float — so these
lemmas ground the *proofs*, while the executable `Adequacy` carrier (`Adequacy.lean`) computes over
Lean's `Float`. Bridging the two (executable rounding that provably matches this spec) is Stage 3.3;
lifting the FLX Sterbenz (`Sterbenz32.flx_sterbenz`) to the FLT/`fexp32` format binary32 actually
uses is Stage 3.2 — both call for TorchLean PRs (`UNCERTAINTY.md` §6).
-/
import PropertyKindCalculus.Uncertainty.Adequacy.Grid
import NN.Floats.FP32.Notation
import NN.Floats.FP32.Error
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

end PropertyKindCalculus.Uncertainty.Adequacy
