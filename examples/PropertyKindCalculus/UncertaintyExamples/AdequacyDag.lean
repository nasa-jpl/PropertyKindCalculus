/-
# Worked example — Stage 3.1: the universal adequacy soundness theorem A3′ on a model DAG

The per-site verdict A3 (`AdequacyLadder`) certifies the carrier's flag at *one* addition; A3′
(`Adequacy.DagBound`) lifts it to a *whole* floating-point evaluation. Here that lift is instantiated
on a concrete, nontrivial model DAG — the three-input accumulator `acc = (x₀ + x₁) + x₂`, a
`sub`-bearing variant `mix = (x₀ + x₁) − x₂`, and a deeper five-input tree — and the sorry-free
axiom profile is confirmed.

  * **`dag_fp32_error_bound`** — the FP32 measurand of `acc` differs from its exact `ℝ` value by at
    most the accumulated rounding budget `errBound acc ρ` (two `+` nodes → two half-ulps).
  * **A3′ — `dag_fp32_box_faithful`.** For *any* two inputs `ρ`, `σ` (every input in a box), the FP32
    output variation of `acc`/`mix` reproduces the exact `ℝ` variation up to `errBound σ + errBound ρ`
    — the whole-evaluation lift.
  * **A3′, flag-free — `dag_fp32_box_exact_of_flagFree`.** When no node rounds, the bound collapses to
    *equality*: the FP32 measurand's uncertainty over the box is exactly the `ℝ` one.

These are `FP32`/`ℝ` proof terms (the format is `noncomputable`, so — like `AdequacyLadder` — they
are checked facts, not `#eval`s). The module building under CI is what makes A3′ a theorem *over a
nontrivial model DAG*, and the axiom prints confirm no `sorryAx`. Mathlib- and TorchLean-backed.
-/
import PropertyKindCalculus.Uncertainty.Adequacy.DagBound

namespace PropertyKindCalculus.UncertaintyExamples.AdequacyDag

open PropertyKindCalculus.Uncertainty.Adequacy
open TorchLean.Floats

/-! ## Three concrete model DAGs -/

/-- A three-input accumulator `(x₀ + x₁) + x₂` — two rounded (`add`) nodes. -/
def acc : Expr := .add (.add (.inp 0) (.inp 1)) (.inp 2)

/-- An add/sub model `(x₀ + x₁) − x₂` — the subtraction exercises the Sterbenz (A2) node. -/
def mix : Expr := .sub (.add (.inp 0) (.inp 1)) (.inp 2)

/-- A deeper five-input tree `((x₀ + x₁) + (x₂ + x₃)) − x₄` — four rounding nodes. -/
def deep : Expr := .sub (.add (.add (.inp 0) (.inp 1)) (.add (.inp 2) (.inp 3))) (.inp 4)

/-! ## The forward-error bound and A3′, instantiated on the DAGs -/

/-- **Forward error.** The FP32 accumulator tracks its exact `ℝ` value within the DAG's rounding
budget, for every input assignment. -/
theorem acc_error_bound (ρ : ℕ → FP32) :
    |(evalFP32 acc ρ).val - evalExact acc ρ| ≤ errBound acc ρ :=
  dag_fp32_error_bound ρ acc

/-- **A3′ on `acc`.** For every pair of inputs (every input in a box around `ρ`), the FP32 output
variation reproduces the exact `ℝ` variation up to the summed rounding budget — the FP32 measurand's
uncertainty equals the `ℝ` one up to a proven bound. -/
theorem acc_box_faithful (ρ σ : ℕ → FP32) :
    |((evalFP32 acc σ).val - (evalFP32 acc ρ).val) - (evalExact acc σ - evalExact acc ρ)|
      ≤ errBound acc σ + errBound acc ρ :=
  dag_fp32_box_faithful acc ρ σ

/-- **A3′ on the deeper `deep` tree** — the bound composes over four rounding nodes. -/
theorem deep_box_faithful (ρ σ : ℕ → FP32) :
    |((evalFP32 deep σ).val - (evalFP32 deep ρ).val) - (evalExact deep σ - evalExact deep ρ)|
      ≤ errBound deep σ + errBound deep ρ :=
  dag_fp32_box_faithful deep ρ σ

/-- **A3′, flag-free case on `mix`.** When neither the two additions nor the (Sterbenz-regime,
A2) subtraction rounds — flag-free at both `ρ` and `σ` — the FP32 output variation is *exactly* the
exact `ℝ` variation: no input uncertainty is lost anywhere in the evaluation. -/
theorem mix_box_exact (ρ σ : ℕ → FP32) (hρ : FlagFree mix ρ) (hσ : FlagFree mix σ) :
    (evalFP32 mix σ).val - (evalFP32 mix ρ).val = evalExact mix σ - evalExact mix ρ :=
  dag_fp32_box_exact_of_flagFree mix ρ σ hρ hσ

/-- The DAG's rounding budget is a genuine nonnegative bound. -/
theorem acc_budget_nonneg (ρ : ℕ → FP32) : 0 ≤ errBound acc ρ :=
  errBound_nonneg ρ acc

/-! ## Sorry-free — the axiom profile of the A3′ theorems -/

#print axioms dag_fp32_box_faithful
#print axioms dag_fp32_box_exact_of_flagFree
#print axioms acc_box_faithful

end PropertyKindCalculus.UncertaintyExamples.AdequacyDag
