/-
# Worked example — R18 coverage as checked coverage probabilities

The `ℝ`-level coverage theorems of `Uncertainty.Coverage` (R18), applied to concrete numbers and
verified sorry-free by `#print axioms`.

  * **Tier 2 — exact (uniform).** The central half `[-1, 1]` of a uniform distribution on
    `[-2, 2]` has coverage probability *exactly* `1/2` (`central_half_coverage`), and the whole
    support has coverage `1` (`full_support_coverage`) — closed-form, from the distribution's
    definition, tighter than the distribution-free Chebyshev bound of Tier 1. The witness
    distribution is the identity on `ℝ` under `volume` conditioned to the support
    (`Coverage.isUniform_id_cond`).

Everything is a **checked fact** (the module builds under CI); the axiom prints confirm no
`sorryAx`. Mathlib-backed.
-/
import PropertyKindCalculus.Uncertainty.Coverage

namespace PropertyKindCalculus.UncertaintyExamples.Coverage

open MeasureTheory PropertyKindCalculus.Uncertainty.Coverage

/-- Coverage of the central half `[-1, 1]` of a uniform on `[-2, 2]` is *exactly* `1/2` — an exact,
closed-form coverage probability (R18, Tier 2), tighter than the Chebyshev bound. -/
theorem central_half_coverage :
    (ProbabilityTheory.cond volume (Set.Icc ((0 : ℝ) - 2) (0 + 2)))
        ((id : ℝ → ℝ) ⁻¹' Set.Icc ((0 : ℝ) - 1) (0 + 1)) = ENNReal.ofReal (1 / 2) :=
  uniform_coverage_exact (m := 0) (δ := 2) (h := 1) (by norm_num)
    (isUniform_id_cond _) (by norm_num) (by norm_num)

/-- Coverage of the whole support `[-2, 2]` of the uniform is *exactly* `1` (`2/2`). -/
theorem full_support_coverage :
    (ProbabilityTheory.cond volume (Set.Icc ((0 : ℝ) - 2) (0 + 2)))
        ((id : ℝ → ℝ) ⁻¹' Set.Icc ((0 : ℝ) - 2) (0 + 2)) = ENNReal.ofReal (2 / 2) :=
  uniform_coverage_exact (m := 0) (δ := 2) (h := 2) (by norm_num)
    (isUniform_id_cond _) (by norm_num) (le_refl 2)

end PropertyKindCalculus.UncertaintyExamples.Coverage
