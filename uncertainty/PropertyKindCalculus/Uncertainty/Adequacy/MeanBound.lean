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

## Nonnegative weights put the two licenses back together

Both failure directions need cancellation, so ruling cancellation out restores the equivalence:
`licenses_agree_of_nonneg` proves that for weights that are nonnegative and on the binary32 grid,
the rounded total is zero exactly when the exact total is. The floating-point content is one
lemma — `fp32Round_add_ge`, that a grid point does not shrink when a nonnegative is added to it
and the sum is rounded, which is monotonicity plus the fact that rounding fixes the grid.

That covers the weights metrology actually uses: masses, areas, durations, coverage fractions,
validity indicators. It is the *second*-best fix; the best is not to round the denominator at all
(`Aggregation.licenses_agree_of_exact`), which is available whenever the weights are counts.

Proved over `ℝ`/`FP32`, sorry-free.
-/
import PropertyKindCalculus.Uncertainty.Adequacy.DagBound
import PropertyKindCalculus.Aggregation
import PropertyKindCalculus.Torch.Fp32

namespace PropertyKindCalculus.Uncertainty.Adequacy

open TorchLean.Floats
open TorchLean.Floats.IEEE754
open FloatLib.Floats.Formats.Flocq (genericFormat)
open FloatLib.Numerics (binaryRadix)

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
  exact h (fp32_val_inj (by rw [hv]; exact fp32Round_zero.symm))

/-- And conversely — so a carving's binary32 license can be established from arithmetic on its
semantic values, which is how a witness for the capstone below is built. -/
theorem fp32_ne_zero_of_val {x : FP32} (h : x.val ≠ 0) : x ≠ Carrier.zero := by
  intro hx
  exact h (by rw [hx]; exact fp32Round_zero)

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

/-! ## Nonnegative weights: when the two licenses coincide after all

The independence above is a statement about *signed* weights — both witnesses need one weight to
cancel another. Metrology's weights are usually not signed, and this section proves that where
they are not, the two licenses are equivalent and the carving's own field is enough. -/

/-- **The one floating-point fact the positivity argument needs.** A grid point does not shrink
when a nonnegative quantity is added to it and the sum is rounded: rounding is monotone
(`round32_mono`), and it fixes `x` because `x` is on the grid (`round32_fix`). Absorption can make
the sum return `x` unchanged — that is the whole phenomenon — but it cannot make it return anything
*smaller*.

The executable rung's rounding is the spec rung's: `IEEE32Exec.fp32Round` and `round32` are the same
function, so the grid lemmas of `Fp32Grounding` apply here with no transport. -/
theorem fp32Round_add_ge {x y : ℝ} (hx : genericFormat binaryRadix fexp32 x) (hy : 0 ≤ y) :
    x ≤ IEEE32Exec.fp32Round (x + y) := by
  calc x = IEEE32Exec.fp32Round x := (round32_fix hx).symm
    _ ≤ IEEE32Exec.fp32Round (x + y) := round32_mono (by linarith)

/-- The rounded fold stays on the grid when the weights do — at a leaf by hypothesis, at a join
because a rounded value is a grid value. -/
theorem totalWeight_onGrid (w : P → FP32) (hg : ∀ p, (w p).IsRepresentable) :
    ∀ d : Decomposition P, genericFormat binaryRadix fexp32 (totalWeight w d).val
  | .atom p => hg p
  | .union _ _ => round32_representable _

/-- The rounded fold of nonnegative weights is nonnegative. -/
theorem totalWeight_fp32_nonneg (w : P → FP32) (hnn : ∀ p, 0 ≤ (w p).val) :
    ∀ d : Decomposition P, 0 ≤ (totalWeight w d).val
  | .atom p => hnn p
  | .union a b => by
      have ha := totalWeight_fp32_nonneg w hnn a
      have hb := totalWeight_fp32_nonneg w hnn b
      show (0:ℝ) ≤ IEEE32Exec.fp32Round ((totalWeight w a).val + (totalWeight w b).val)
      calc (0:ℝ) = IEEE32Exec.fp32Round 0 := fp32Round_zero.symm
        _ ≤ _ := round32_mono (by linarith)

/-- And so is the exact fold. -/
theorem totalWeight_exact_nonneg (w : P → FP32) (hnn : ∀ p, 0 ≤ (w p).val) :
    ∀ d : Decomposition P, 0 ≤ totalWeight (fun p => (w p).val) d
  | .atom p => hnn p
  | .union a b => by
      have ha := totalWeight_exact_nonneg w hnn a
      have hb := totalWeight_exact_nonneg w hnn b
      show (0:ℝ) ≤ totalWeight (fun p => (w p).val) a + totalWeight (fun p => (w p).val) b
      linarith

/-- **A positive exact total forces a positive rounded total, for nonnegative grid weights.** The
direction that fails in general — the absorption witness has exact total `1` and rounded total
`+0` — and the hypothesis that rules it out. At a join, one side's exact total is positive, so by
induction its rounded total is; the other side's rounded total is nonnegative; and
`fp32Round_add_ge` says the rounded sum is at least the positive one. -/
theorem totalWeight_fp32_pos (w : P → FP32) (hnn : ∀ p, 0 ≤ (w p).val)
    (hg : ∀ p, (w p).IsRepresentable) :
    ∀ d : Decomposition P, 0 < totalWeight (fun p => (w p).val) d → 0 < (totalWeight w d).val
  | .atom _ => fun h => h
  | .union a b => by
      intro h
      have hexa := totalWeight_exact_nonneg w hnn a
      have hexb := totalWeight_exact_nonneg w hnn b
      have h' : 0 < totalWeight (fun p => (w p).val) a + totalWeight (fun p => (w p).val) b := h
      show (0:ℝ) < IEEE32Exec.fp32Round ((totalWeight w a).val + (totalWeight w b).val)
      rcases lt_or_ge 0 (totalWeight (fun p => (w p).val) a) with hL | hL
      · have hLp := totalWeight_fp32_pos w hnn hg a hL
        have hRn := totalWeight_fp32_nonneg w hnn b
        have := fp32Round_add_ge (totalWeight_onGrid w hg a) hRn
        linarith
      · have hR : 0 < totalWeight (fun p => (w p).val) b := by linarith
        have hRp := totalWeight_fp32_pos w hnn hg b hR
        have hLn := totalWeight_fp32_nonneg w hnn a
        have hcomm : (totalWeight w a).val + (totalWeight w b).val
                   = (totalWeight w b).val + (totalWeight w a).val := by ring
        rw [hcomm]
        have := fp32Round_add_ge (totalWeight_onGrid w hg b) hLn
        linarith

/-- **And a zero exact total forces a zero rounded total.** The other direction — the witness with
exact total `0` and rounded total `-2` — ruled out because a sum of nonnegatives is zero only when
every summand is. -/
theorem totalWeight_fp32_eq_zero (w : P → FP32) (hnn : ∀ p, 0 ≤ (w p).val) :
    ∀ d : Decomposition P,
      totalWeight (fun p => (w p).val) d = 0 → (totalWeight w d).val = 0
  | .atom _ => fun h => h
  | .union a b => by
      intro h
      have hexa := totalWeight_exact_nonneg w hnn a
      have hexb := totalWeight_exact_nonneg w hnn b
      have h' : totalWeight (fun p => (w p).val) a + totalWeight (fun p => (w p).val) b = 0 := h
      have hfa := totalWeight_fp32_eq_zero w hnn a (by linarith)
      have hfb := totalWeight_fp32_eq_zero w hnn b (by linarith)
      show IEEE32Exec.fp32Round ((totalWeight w a).val + (totalWeight w b).val) = 0
      rw [hfa, hfb, add_zero]
      exact fp32Round_zero

/-- **The two licenses coincide on nonnegative grid weights.** So for masses, areas, durations,
coverage fractions and validity indicators, a `WeightedCarving FP32`'s own field *is* the
specification's precondition, and nothing further need be established.

Both hypotheses are needed and neither is idle. Nonnegativity rules out the cancellation both
counterexamples are built from. Grid membership is not automatic: `NF` is a bare record over `ℝ`
with representability a separate predicate, so "this is a binary32 number" has to be said — and
without it a weight below half the smallest subnormal would round away and the argument would
fail at exactly the leaf it starts from. -/
theorem licenses_agree_of_nonneg (w : P → FP32) (hnn : ∀ p, 0 ≤ (w p).val)
    (hg : ∀ p, (w p).IsRepresentable) (d : Decomposition P) :
    (totalWeight w d).val ≠ 0 ↔ totalWeight (fun p => (w p).val) d ≠ 0 := by
  constructor
  · intro hE hS; exact hE (totalWeight_fp32_eq_zero w hnn d hS)
  · intro hS
    exact (totalWeight_fp32_pos w hnn hg d
      (lt_of_le_of_ne (totalWeight_exact_nonneg w hnn d) (Ne.symm hS))).ne'

/-- **The carving a nonnegative weighting licenses**, built from the specification's condition
alone — the executable one follows. -/
noncomputable def carvingOfNonneg (w : P → FP32) (d : Decomposition P)
    (hnn : ∀ p, 0 ≤ (w p).val) (hg : ∀ p, (w p).IsRepresentable)
    (hpos : 0 < totalWeight (fun p => (w p).val) d) : WeightedCarving FP32 P :=
  ⟨d, w, fp32_ne_zero_of_val (totalWeight_fp32_pos w hnn hg d hpos).ne'⟩

/-- **The capstone with one hypothesis instead of two.** For nonnegative grid weights whose exact
total is positive, the binary32 mean is within the DAG's rounding budget of the exact real mean —
and the executable license, which the general statement asks for separately, is discharged by
positivity rather than assumed. This is the form a science kernel can actually use. -/
theorem mean_fp32_within_errBound_of_nonneg (w v : P → FP32) (d : Decomposition P)
    (ρ : ℕ → FP32) (hnn : ∀ p, 0 ≤ (w p).val) (hg : ∀ p, (w p).IsRepresentable)
    (hpos : 0 < totalWeight (fun p => (w p).val) d) :
    |((carvingOfNonneg w d hnn hg hpos).mean v).val
        - (specCarving (carvingOfNonneg w d hnn hg hpos) hpos.ne').mean (fun p => (v p).val)|
      ≤ errBound (meanExpr w v d) ρ :=
  mean_fp32_within_errBound (carvingOfNonneg w d hnn hg hpos) v ρ hpos.ne'

end PropertyKindCalculus.Uncertainty.Adequacy
