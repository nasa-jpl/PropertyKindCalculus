/-
`PropertyKindCalculus.Uncertainty.Adequacy.MeanBound` — **the weighted mean at binary32**, the
rung between the carrier-parametric mode (`PropertyKindCalculus.Aggregation`) and its law over `ℝ`
(`WeightedCarving.mean_const`).

A mean is the first aggregation mode that is not a fold: it is a `×`-then-`+`-then-`÷` expression,
so it is exactly the shape `DagBound` was built to bound. This module compiles a carving into a
`DagBound.Expr` — the weights and values as exact binary32 constants, the folds as `add` nodes, the
final ratio as a `div` node — and reads `dag_fp32_error_bound` off it. The result:

  * **`mean_fp32_within_errBound`** — the binary32 weighted mean of a carving, forgotten to `ℝ`,
    differs from the exact real mean of the *same* weights and values by at most the DAG's
    accumulated rounding budget `errBound`. Every rounding the mean incurs — one per weighted
    product, one per join of the numerator, one per join of the denominator, one at the ratio — is
    a node of that budget, and the quotient rule's magnitude factors (`1/|b|`, `|a|/|b|²`) are what
    the denominator's smallness costs.

## The license does not cross the bridge; each rung needs its own

`WeightedCarving`'s field says the total weight is not the *carrier's* zero. At `FP32` that is a
statement about the **rounded** fold, and the theorem here needs a second one about the **exact**
fold — `DagBound.Regular`'s two conditions at a `div` node, which are not one condition read twice.
Neither implies the other, and both directions of the failure are ordinary floating-point
behavior: weights whose exact sum is nonzero can round to a zero total when a large one absorbs
the rest, and weights whose exact sum is zero can total nonzero once each partial sum is snapped to
the grid. So `specCarving` — forgetting an `FP32` carving to the `ℝ` carving it specifies — takes
the specification's license as an *argument*. It is not derivable from the executable one, and the
signature is where that is recorded.

This is the numerical half of what `Torch.Fp32`'s `Quantity.div_refines_exec` records
algebraically: the metrological side condition a mean's denominator carries reappears at every
lower rung as a condition that rung can actually violate.

Proved over `ℝ`/`FP32`, sorry-free.
-/
import PropertyKindCalculus.Uncertainty.Adequacy.DagBound
import PropertyKindCalculus.Aggregation
import PropertyKindCalculus.Torch.Fp32

namespace PropertyKindCalculus.Uncertainty.Adequacy

open TorchLean.Floats
open TorchLean.Floats.IEEE754

universe u

variable {P : Type u}

/-! ## A carving, compiled into an evaluation DAG

The weights and the per-part values enter as `Expr.const` — they are given binary32 data, not
free inputs — so the input assignment `ρ` is irrelevant to every theorem here and the leaves
contribute nothing to the budget. What the budget counts is exactly the arithmetic the mean does. -/

/-- The mean's **numerator**, compiled: a weighted product at each part, a rounding `add` at each
join of the carving. -/
def numExpr (w v : P → FP32) : Decomposition P → Expr
  | .atom p => .mul (.const (w p)) (.const (v p))
  | .union a b => .add (numExpr w v a) (numExpr w v b)

/-- The mean's **denominator**, compiled: the weights themselves at the parts, a rounding `add`
at each join. This is the sub-DAG whose two nonzero-denominator conditions are the mean's two
licenses. -/
def denExpr (w : P → FP32) : Decomposition P → Expr
  | .atom p => .const (w p)
  | .union a b => .add (denExpr w a) (denExpr w b)

/-- **The weighted mean, compiled** — the one `div` node in the DAG, over the two folds. -/
def meanExpr (w v : P → FP32) (d : Decomposition P) : Expr :=
  .div (numExpr w v d) (denExpr w d)

/-! ## The compiled DAG computes the two means -/

/-- The compiled denominator evaluates, in binary32, to the carving's total weight. -/
theorem evalFP32_denExpr (w : P → FP32) (ρ : ℕ → FP32) :
    ∀ d : Decomposition P, evalFP32 (denExpr w d) ρ = totalWeight w d
  | .atom _ => rfl
  | .union a b => by
      show evalFP32 (denExpr w a) ρ + evalFP32 (denExpr w b) ρ = _
      rw [evalFP32_denExpr w ρ a, evalFP32_denExpr w ρ b]
      rfl

/-- The compiled numerator evaluates, in binary32, to the carving's weighted sum. -/
theorem evalFP32_numExpr (w v : P → FP32) (ρ : ℕ → FP32) :
    ∀ d : Decomposition P, evalFP32 (numExpr w v d) ρ = weightedSum w v d
  | .atom _ => rfl
  | .union a b => by
      show evalFP32 (numExpr w v a) ρ + evalFP32 (numExpr w v b) ρ = _
      rw [evalFP32_numExpr w v ρ a, evalFP32_numExpr w v ρ b]
      rfl

/-- The compiled denominator evaluates, exactly over `ℝ`, to the total of the *forgotten* weights
— the specification's denominator, which is a different number from the rounded one. -/
theorem evalExact_denExpr (w : P → FP32) (ρ : ℕ → FP32) :
    ∀ d : Decomposition P, evalExact (denExpr w d) ρ = totalWeight (fun p => (w p).val) d
  | .atom _ => rfl
  | .union a b => by
      show evalExact (denExpr w a) ρ + evalExact (denExpr w b) ρ = _
      rw [evalExact_denExpr w ρ a, evalExact_denExpr w ρ b]
      rfl

/-- The compiled numerator evaluates, exactly over `ℝ`, to the weighted sum of the forgotten
weights and values. -/
theorem evalExact_numExpr (w v : P → FP32) (ρ : ℕ → FP32) :
    ∀ d : Decomposition P,
      evalExact (numExpr w v d) ρ
        = weightedSum (fun p => (w p).val) (fun p => (v p).val) d
  | .atom _ => rfl
  | .union a b => by
      show evalExact (numExpr w v a) ρ + evalExact (numExpr w v b) ρ = _
      rw [evalExact_numExpr w v ρ a, evalExact_numExpr w v ρ b]
      rfl

/-- **The compiled DAG's binary32 evaluation is the binary32 mean.** -/
theorem evalFP32_meanExpr (w v : P → FP32) (d : Decomposition P) (ρ : ℕ → FP32) :
    evalFP32 (meanExpr w v d) ρ = weightedSum w v d / totalWeight w d := by
  show evalFP32 (numExpr w v d) ρ / evalFP32 (denExpr w d) ρ = _
  rw [evalFP32_numExpr, evalFP32_denExpr]

/-- **And its exact evaluation is the real mean of the forgotten data.** -/
theorem evalExact_meanExpr (w v : P → FP32) (d : Decomposition P) (ρ : ℕ → FP32) :
    evalExact (meanExpr w v d) ρ
      = weightedSum (fun p => (w p).val) (fun p => (v p).val) d
          / totalWeight (fun p => (w p).val) d := by
  show evalExact (numExpr w v d) ρ / evalExact (denExpr w d) ρ = _
  rw [evalExact_numExpr, evalExact_denExpr]

/-! ## Regularity — the mean's one `div` node, and its two licenses -/

/-- The numerator is `div`-free, so it is regular at every input. -/
theorem regular_numExpr (w v : P → FP32) (ρ : ℕ → FP32) :
    ∀ d : Decomposition P, Regular (numExpr w v d) ρ
  | .atom _ => ⟨trivial, trivial⟩
  | .union a b => ⟨regular_numExpr w v ρ a, regular_numExpr w v ρ b⟩

/-- So is the denominator. -/
theorem regular_denExpr (w : P → FP32) (ρ : ℕ → FP32) :
    ∀ d : Decomposition P, Regular (denExpr w d) ρ
  | .atom _ => trivial
  | .union a b => ⟨regular_denExpr w ρ a, regular_denExpr w ρ b⟩

/-- **The mean's DAG is regular exactly when both totals are nonzero** — the rounded one and the
exact one. `DagBound.Regular` asks for both at a `div` node, and here they are the executable and
the specification readings of the very same weights. -/
theorem regular_meanExpr (w v : P → FP32) (d : Decomposition P) (ρ : ℕ → FP32)
    (hE : (totalWeight w d).val ≠ 0)
    (hS : totalWeight (fun p => (w p).val) d ≠ 0) :
    Regular (meanExpr w v d) ρ :=
  ⟨regular_numExpr w v ρ d, regular_denExpr w ρ d,
    by rw [evalFP32_denExpr]; exact hE,
    by rw [evalExact_denExpr]; exact hS⟩

/-! ## The carving's own license, read at binary32 -/

/-- `NF`'s semantic value determines it: the format is a one-field record over `ℝ`. -/
private theorem fp32_val_inj {x y : FP32} (h : x.val = y.val) : x = y := by
  cases x; cases y; simpa using h

/-- **A nonzero binary32 total has a nonzero real value.** This is the executable half of the
mean's regularity, and it *is* implied by `WeightedCarving`'s field — because the field is a
statement about the rounded fold, which is the number the `div` node divides by. The other half
is not implied, which is why `specCarving` below takes it as an argument. -/
theorem fp32_val_ne_zero {x : FP32} (h : x ≠ Carrier.zero) : x.val ≠ 0 := by
  intro hv
  exact h (fp32_val_inj (by rw [hv]; exact IEEE32Exec.fp32Round_zero.symm))

/-- And conversely — so a carving's binary32 license can be established from arithmetic on its
semantic values, which is how a witness for the capstone below is built. -/
theorem fp32_ne_zero_of_val {x : FP32} (h : x.val ≠ 0) : x ≠ Carrier.zero := by
  intro hx
  exact h (by rw [hx]; exact IEEE32Exec.fp32Round_zero)

/-- **Forget a binary32 carving to the real carving it specifies — supplying the specification's
own license.** The hypothesis is an argument, not a field lookup, and that is the content: the
carving's `total_ne_zero` says the *rounded* total is nonzero, which neither implies nor is
implied by the *exact* total being nonzero. Weights whose exact sum is nonzero can round to a
zero total when a large one absorbs the rest — the absorption the adequacy carrier flags — and
weights whose exact sum is zero can total nonzero once the partial sums are snapped to the grid. -/
noncomputable def specCarving (c : WeightedCarving FP32 P)
    (hS : totalWeight (fun p => (c.weight p).val) c.parts ≠ Carrier.zero) :
    WeightedCarving ℝ P :=
  ⟨c.parts, fun p => (c.weight p).val, hS⟩

/-- The forgotten carving carves the same whole. -/
@[simp] theorem specCarving_parts (c : WeightedCarving FP32 P)
    (hS : totalWeight (fun p => (c.weight p).val) c.parts ≠ Carrier.zero) :
    (specCarving c hS).parts = c.parts := rfl

/-- With each part's weight forgotten to its real value. -/
@[simp] theorem specCarving_weight (c : WeightedCarving FP32 P)
    (hS : totalWeight (fun p => (c.weight p).val) c.parts ≠ Carrier.zero) (p : P) :
    (specCarving c hS).weight p = (c.weight p).val := rfl

/-! ## The capstone -/

/-- **The binary32 weighted mean is within the DAG's rounding budget of the exact one.** For a
carving carried at TorchLean's binary32 rounding spec, and given the specification carrier's own
nonzero-total license, the mean computed on the grid — forgotten to `ℝ` — differs from the exact
real mean of the same weights and values by at most `errBound` of the compiled mean DAG.

This is `dag_fp32_error_bound` at the one expression shape the aggregation modes could not reach:
`Extensivity`'s extensive mode is a fold and needs only `+`, while a mean multiplies, sums and
finally divides, and it is the division that makes the budget's quotient-rule factors — `1/|b|`
for the numerator's accumulated error, `|a|/|b|²` for the denominator's — the price of a small
total weight. A carving whose weights nearly cancel has a license, an exact mean, and a budget
that says how little the computed one is worth. -/
theorem mean_fp32_within_errBound (c : WeightedCarving FP32 P) (v : P → FP32) (ρ : ℕ → FP32)
    (hS : totalWeight (fun p => (c.weight p).val) c.parts ≠ Carrier.zero) :
    |(c.mean v).val - (specCarving c hS).mean (fun p => (v p).val)|
      ≤ errBound (meanExpr c.weight v c.parts) ρ := by
  have hreg : Regular (meanExpr c.weight v c.parts) ρ :=
    regular_meanExpr c.weight v c.parts ρ (fp32_val_ne_zero c.total_ne_zero) hS
  have h := dag_fp32_error_bound ρ (meanExpr c.weight v c.parts) hreg
  rw [evalFP32_meanExpr, evalExact_meanExpr] at h
  exact h

/-- **The budget is a budget**: nonnegative, so the bound above is never vacuous by sign. -/
theorem errBound_meanExpr_nonneg (w v : P → FP32) (d : Decomposition P) (ρ : ℕ → FP32) :
    0 ≤ errBound (meanExpr w v d) ρ :=
  errBound_nonneg ρ (meanExpr w v d)

end PropertyKindCalculus.Uncertainty.Adequacy
