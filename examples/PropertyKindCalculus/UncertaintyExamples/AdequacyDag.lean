/-
# Worked example — Stage 3.1: the universal adequacy soundness theorem A3′ on a model DAG

The per-site verdict A3 (`AdequacyLadder`) certifies the carrier's flag at *one* addition; A3′
(`Adequacy.DagBound`) lifts it to a *whole* floating-point evaluation. Here that lift is instantiated
on concrete, nontrivial model DAGs across the full operator class `+`/`−`/`×`/`÷` — the three-input
accumulator `acc = (x₀ + x₁) + x₂`, a `sub`-bearing variant `mix = (x₀ + x₁) − x₂`, a deeper
five-input tree, a **product** `prod = (x₀ + x₁)·x₂` and a **quotient** `ratio = x₀/x₁` — and the
sorry-free axiom profile is confirmed.

  * **`dag_fp32_error_bound`** — the FP32 measurand differs from its exact `ℝ` value by at most the
    accumulated rounding budget `errBound e ρ`. On `acc` that is two half-ulps; on `prod` it is the
    product node's half-ulp *plus* the sum's error weighted by `|x₂|` (the `∂(ab)/∂a = b` factor).
  * **A3′ — `dag_fp32_box_faithful`.** For *any* two inputs `ρ`, `σ` (every input in a box), the FP32
    output variation reproduces the exact `ℝ` variation up to `errBound σ + errBound ρ`.
  * **A3′, flag-free — `dag_fp32_box_exact_of_flagFree`.** When no node rounds, the bound collapses to
    *equality*: the FP32 measurand's uncertainty over the box is exactly the `ℝ` one.

`add`/`sub`/`mul` DAGs are unconditional; a `div` DAG carries the `Regular` side condition (nonzero
denominator), here supplied for `ratio` from `(ρ 1).val ≠ 0`. These are `FP32`/`ℝ` proof terms (the
format is `noncomputable`, so — like `AdequacyLadder` — they are checked facts, not `#eval`s). The
module building under CI is what makes A3′ a theorem *over nontrivial model DAGs*, and the axiom
prints confirm no `sorryAx`. Mathlib- and TorchLean-backed.
-/
import PropertyKindCalculus.Uncertainty.Adequacy.DagBound

namespace PropertyKindCalculus.UncertaintyExamples.AdequacyDag

open PropertyKindCalculus.Uncertainty.Adequacy
open TorchLean.Floats

/-! ## Concrete model DAGs -/

/-- A three-input accumulator `(x₀ + x₁) + x₂` — two rounded (`add`) nodes. -/
def acc : Expr := .add (.add (.inp 0) (.inp 1)) (.inp 2)

/-- An add/sub model `(x₀ + x₁) − x₂` — the subtraction exercises the Sterbenz (A2) node. -/
def mix : Expr := .sub (.add (.inp 0) (.inp 1)) (.inp 2)

/-- A deeper five-input tree `((x₀ + x₁) + (x₂ + x₃)) − x₄` — four rounding nodes. -/
def deep : Expr := .sub (.add (.add (.inp 0) (.inp 1)) (.add (.inp 2) (.inp 3))) (.inp 4)

/-- A mixed `+`/`×` model `(x₀ + x₁)·x₂` — the product node exercises the nonlinear propagation
(the sum's error is weighted by `|x₂|`). -/
def prod : Expr := .mul (.add (.inp 0) (.inp 1)) (.inp 2)

/-- A quotient model `x₀/x₁` — the `div` node carries the `Regular` (nonzero-denominator) side
condition and the `1/|x₁|` propagation factor. -/
def ratio : Expr := .div (.inp 0) (.inp 1)

/-! ## The forward-error bound and A3′, instantiated on the DAGs

`Regular` is vacuous on the `÷`-free DAGs (`acc`/`mix`/`deep`/`prod`), discharged by `simp`. -/

/-- **Forward error on `acc`.** The FP32 accumulator tracks its exact `ℝ` value within the DAG's
rounding budget, for every input assignment. -/
theorem acc_error_bound (ρ : ℕ → FP32) :
    |(evalFP32 acc ρ).val - evalExact acc ρ| ≤ errBound acc ρ :=
  dag_fp32_error_bound ρ acc (by simp [Regular, acc])

/-- **A3′ on `acc`.** For every pair of inputs (every input in a box around `ρ`), the FP32 output
variation reproduces the exact `ℝ` variation up to the summed rounding budget. -/
theorem acc_box_faithful (ρ σ : ℕ → FP32) :
    |((evalFP32 acc σ).val - (evalFP32 acc ρ).val) - (evalExact acc σ - evalExact acc ρ)|
      ≤ errBound acc σ + errBound acc ρ :=
  dag_fp32_box_faithful acc ρ σ (by simp [Regular, acc]) (by simp [Regular, acc])

/-- **A3′ on the deeper `deep` tree** — the bound composes over four rounding nodes. -/
theorem deep_box_faithful (ρ σ : ℕ → FP32) :
    |((evalFP32 deep σ).val - (evalFP32 deep ρ).val) - (evalExact deep σ - evalExact deep ρ)|
      ≤ errBound deep σ + errBound deep ρ :=
  dag_fp32_box_faithful deep ρ σ (by simp [Regular, deep]) (by simp [Regular, deep])

/-- **Forward error on the product `prod`.** The nonlinear (`mul`) node contributes its own half-ulp
plus the operand errors weighted by the other operand's magnitude — a genuine bound, unconditionally
(a product has no domain restriction). -/
theorem prod_error_bound (ρ : ℕ → FP32) :
    |(evalFP32 prod ρ).val - evalExact prod ρ| ≤ errBound prod ρ :=
  dag_fp32_error_bound ρ prod (by simp [Regular, prod])

/-- **A3′ on the product `prod`** — the box-faithfulness lift over a `+`/`×` DAG. -/
theorem prod_box_faithful (ρ σ : ℕ → FP32) :
    |((evalFP32 prod σ).val - (evalFP32 prod ρ).val) - (evalExact prod σ - evalExact prod ρ)|
      ≤ errBound prod σ + errBound prod ρ :=
  dag_fp32_box_faithful prod ρ σ (by simp [Regular, prod]) (by simp [Regular, prod])

/-! ## The `div` node — the `Regular` (nonzero-denominator) side condition

For an *input* variable the FP32 and exact interpretations coincide (`evalFP32 (.inp 1) ρ = ρ 1`,
`evalExact (.inp 1) ρ = (ρ 1).val`), so both nonzero-denominator obligations of `ratio` collapse to
the single hypothesis `(ρ 1).val ≠ 0`. -/

/-- `ratio` is regular exactly when its denominator input is nonzero. -/
theorem ratio_regular (ρ : ℕ → FP32) (hden : (ρ 1).val ≠ 0) : Regular ratio ρ := by
  refine ⟨trivial, trivial, ?_, ?_⟩ <;> simpa [evalFP32, evalExact] using hden

/-- **Forward error on the quotient `ratio`** (nonzero denominator). The `div` node's error is the
quotient's half-ulp plus the numerator error scaled by `1/|x₁|` — the `∂(a/b)/∂a = 1/b` factor. -/
theorem ratio_error_bound (ρ : ℕ → FP32) (hden : (ρ 1).val ≠ 0) :
    |(evalFP32 ratio ρ).val - evalExact ratio ρ| ≤ errBound ratio ρ :=
  dag_fp32_error_bound ρ ratio (ratio_regular ρ hden)

/-- **A3′ on the quotient `ratio`** — the box-faithfulness lift over a `÷` DAG, for any two boxes
with nonzero denominators. -/
theorem ratio_box_faithful (ρ σ : ℕ → FP32) (hρ : (ρ 1).val ≠ 0) (hσ : (σ 1).val ≠ 0) :
    |((evalFP32 ratio σ).val - (evalFP32 ratio ρ).val) - (evalExact ratio σ - evalExact ratio ρ)|
      ≤ errBound ratio σ + errBound ratio ρ :=
  dag_fp32_box_faithful ratio ρ σ (ratio_regular ρ hρ) (ratio_regular σ hσ)

/-! ## The flag-free regime -/

/-- **A3′, flag-free case on `mix`.** When neither the two additions nor the (Sterbenz-regime,
A2) subtraction rounds — flag-free at both `ρ` and `σ` — the FP32 output variation is *exactly* the
exact `ℝ` variation: no input uncertainty is lost anywhere in the evaluation. -/
theorem mix_box_exact (ρ σ : ℕ → FP32) (hρ : FlagFree mix ρ) (hσ : FlagFree mix σ) :
    (evalFP32 mix σ).val - (evalFP32 mix ρ).val = evalExact mix σ - evalExact mix ρ :=
  dag_fp32_box_exact_of_flagFree mix ρ σ hρ hσ

/-- **A3′, flag-free case on the product `prod`.** Flag-freedom now includes the `mul` node being
exact; when it holds at both inputs, the FP32 product's uncertainty over the box is exactly the `ℝ`
one. -/
theorem prod_box_exact (ρ σ : ℕ → FP32) (hρ : FlagFree prod ρ) (hσ : FlagFree prod σ) :
    (evalFP32 prod σ).val - (evalFP32 prod ρ).val = evalExact prod σ - evalExact prod ρ :=
  dag_fp32_box_exact_of_flagFree prod ρ σ hρ hσ

/-- The DAG's rounding budget is a genuine nonnegative bound. -/
theorem acc_budget_nonneg (ρ : ℕ → FP32) : 0 ≤ errBound acc ρ :=
  errBound_nonneg ρ acc

/-! ## Sorry-free — the axiom profile of the A3′ theorems (all operators) -/

#print axioms dag_fp32_box_faithful
#print axioms dag_fp32_box_exact_of_flagFree
#print axioms acc_box_faithful
#print axioms prod_box_faithful
#print axioms ratio_error_bound

end PropertyKindCalculus.UncertaintyExamples.AdequacyDag
