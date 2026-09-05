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
    *exact*, `round32 (u − v) = u − v`. Grounded in TorchLean's `round32_sub_exact_of_sterbenz` /
    `FP32.sub_exact_of_sterbenz` (`NN/Floats/FP32/Sterbenz.lean`, added in the Stage-3.2 TorchLean PR).

**Caveat (drives the remaining sub-stage).** TorchLean's entire `FP32`/Flocq layer is
`noncomputable` — `round32 : ℝ → ℝ` is an ℝ-level *specification*, not an executable float — so these
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
theorem round32_within_half_ulp (x : ℝ) : |round32 x - x| ≤ eps32 x :=
  FP32.round_abs_error x

/-! ## Grid membership — when rounding does nothing

The half-ulp bound above says how far a round can move a value. These say when it moves it *not at
all*, which is the hypothesis an exactness argument needs. The two facts are the two directions of
one characterization: a round lands on the grid, and the grid is exactly what a round fixes. -/

/-- **Rounding fixes the grid.** A real already representable in binary32 is returned unchanged. -/
theorem round32_fix {x : ℝ} (h : neuralGenericFormat binaryRadix fexp32 x) : round32 x = x :=
  neural_round_preserves_generic rnd32 x h

/-- **A rounded real is on the grid** — the range of `round32` is the representable set. -/
theorem round32_representable (x : ℝ) : neuralGenericFormat binaryRadix fexp32 (round32 x) :=
  neural_generic_format_round rnd32 x

/-- **The characterization.** `round32` fixes exactly the representable reals. This is what makes
"the exact value is representable" the *weakest* hypothesis under which a node does not round: any
condition implying the node is exact implies this one. -/
theorem round32_eq_self_iff (x : ℝ) :
    round32 x = x ↔ neuralGenericFormat binaryRadix fexp32 x := by
  constructor
  · intro h; exact h ▸ round32_representable x
  · exact round32_fix

/-- **`0` is representable.** -/
theorem zero_representable : neuralGenericFormat binaryRadix fexp32 (0 : ℝ) :=
  neural_generic_format_zero

/-- **And so is `1`** — the two values an indicator weighting uses, so a masked aggregation can
discharge a grid hypothesis without reaching into the format theory itself. -/
theorem one_representable : neuralGenericFormat binaryRadix fexp32 (1 : ℝ) := by
  have h := neural_generic_format_bpow (β := binaryRadix) (fexp := fexp32) 0 (by decide)
  rwa [show neuralBpow binaryRadix 0 = (1:ℝ) by simp [neuralBpow]] at h

/-- **Rounding is monotone**, which is what lets a sign survive a rounded fold. -/
theorem round32_mono {x y : ℝ} (h : x ≤ y) : round32 x ≤ round32 y := neuralRound_mono rnd32 h

/-- **Every power of the radix whose exponent clears the format's grid is representable.** This is
the general lever `one_representable` is one instance of: a value the format can name exactly, and
so a value at which a rounding node provably does nothing. `fexp32 (e + 1) ≤ e` is the format's own
side condition, decidable at any concrete `e`. -/
theorem bpow_representable {e : ℤ} (h : fexp32 (e + 1) ≤ e) :
    neuralGenericFormat binaryRadix fexp32 (neuralBpow binaryRadix e) :=
  neural_generic_format_bpow e h

/-- The radix is two — the bridge from a `neuralBpow` to a numeral. -/
theorem binaryRadix_toReal : binaryRadix.toReal = (2 : ℝ) := by
  simp [NeuralRadix.toReal, binaryRadix]

/-- **The binary32 addition is within half a ulp** of the exact real sum: the per-operation rounding
bound the accumulation argument composes over an evaluation. -/
theorem add32_within_half_ulp (a b : FP32) :
    |(a + b).val - (a.val + b.val)| ≤ eps32 (a.val + b.val) :=
  FP32.add_abs_error a b

/-- **The binary32 subtraction is within half a ulp** of the exact real difference (a bound that is
*zero* in the Sterbenz regime — cf. `Sterbenz32.flx_sterbenz`). -/
theorem sub32_within_half_ulp (a b : FP32) :
    |(a - b).val - (a.val - b.val)| ≤ eps32 (a.val - b.val) :=
  FP32.sub_abs_error a b

/-- **The binary32 multiplication is within half a ulp** of the exact real product: the per-operation
rounding bound the accumulation argument composes at a `mul` node (`FP32.mul_abs_error`). Unlike
`+`/`−`, the *propagated* operand error passes through a product with magnitude-dependent factors, so
`DagBound.errBound` weights each operand's error by the other operand's magnitude. -/
theorem mul32_within_half_ulp (a b : FP32) :
    |(a * b).val - (a.val * b.val)| ≤ eps32 (a.val * b.val) :=
  FP32.mul_abs_error a b

/-- **The binary32 division is within half a ulp** of the exact real quotient (`FP32.div_abs_error`):
the per-operation rounding bound at a `div` node. This isolates only the *rounding* stage; the
propagated operand error at a division is governed by the denominator's magnitude (hence
`DagBound.errBound`'s `1/|b|` factors and the nonzero-denominator side condition `DagBound.Regular`). -/
theorem div32_within_half_ulp (a b : FP32) :
    |(a / b).val - (a.val / b.val)| ≤ eps32 (a.val / b.val) :=
  FP32.div_abs_error a b

/-- **Sound interval enclosure of addition.** The exact real sum of two enclosed reals is enclosed by
the outward-rounded interval sum — the soundness the adequacy *range* analysis rests on. -/
theorem interval_add_sound {R : Interval.Rounder} {A B : Interval.RInterval} {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ B) : x + y ∈ Interval.RInterval.add R A B :=
  Interval.RInterval.mem_add hx hy

/-- **A2 at the real binary32 format — Sterbenz as a theorem about `round32` (Stage 3.2).** For two
representable binary32 values within a factor of two (`0 < u`, `0 < v`, `u ≤ 2v`, `v ≤ 2u`), the
difference is *exactly* representable, so `round32` is the identity on it: `round32 (u − v) = u − v`.
This is the genuine binary32 realization — over TorchLean's `fexp32 = FLTExp (−149) 24`, gradual
underflow — of the grid model's self-contained `Sterbenz32.flx_sterbenz`, discharging Stage 3.2:
near-equal binary32 subtraction is lossless at *the format the model actually uses*. -/
theorem round32_sterbenz_exact {u v : ℝ}
    (hu : neuralGenericFormat binaryRadix fexp32 u) (hv : neuralGenericFormat binaryRadix fexp32 v)
    (hupos : 0 < u) (hvpos : 0 < v) (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) :
    round32 (u - v) = u - v :=
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
