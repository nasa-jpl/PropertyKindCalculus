/-
`PropertyKindCalculus.Uncertainty.Coverage` — R18: the recorded variance certifies a coverage
interval, over Mathlib's `ℝ` (the proof carrier).

VIM 2.36–2.38 (coverage interval / coverage probability / coverage factor) sit above the
uncertainty *dispersion* of R14: once an output's uncertainty is a distribution, a *coverage
interval* is a probability attached to an interval around the mean. This module discharges R18 in
two tiers, matching how much the modeller is willing to assume about the distribution's shape:

  * **Tier 1 — distribution-free (Chebyshev).** For *any* distribution with finite variance, the
    interval `[m − k·u, m + k·u]` (`k` standard uncertainties `u = √variance` about the mean `m`)
    has coverage probability `≥ 1 − 1/k²`. This uses only the `variance` the descriptor already
    carries (`MomentData.variance = κ₂ = u²`) — no shape assumption. It is honest but
    conservative: `k = 2` gives `≥ 75%`, *not* the Gaussian 95%. `coverageBound` (half-width
    form) and `coverageBound_stdUnc` (coverage-factor form) are the theorems.

  * **Tier 2 — exact for a bounded family (uniform).** For a uniform distribution on
    `[m − δ, m + δ]`, the coverage of the centred interval `[m − h, m + h]` is *exactly* `h/δ`
    (`uniform_coverage_exact`) — tighter than Chebyshev, closed-form, from the distribution's
    definition. Ties to the `InputDist.uniform` value the library already builds; `isUniform_id_cond`
    exhibits a concrete witness so the hypothesis is non-vacuous.

Deliberately out of scope (the paper's roadmap): exact *normal* coverage (the 95% ↔ k ≈ 1.96
statement), which needs the Gaussian CDF / error function Mathlib does not provide; and any bridge
to the executable `Float` `invCDF` sampler (that is the R15 exec↔spec pattern, a different axis).

Axiom profile: `[propext, Classical.choice, Quot.sound]` — the standard classical trio, matching
R14/R15 (Mathlib measure theory is classical).
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory ENNReal

namespace PropertyKindCalculus.Uncertainty.Coverage

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Tier 1 — the distribution-free Chebyshev coverage bound -/

/-- **R18, Tier 1 (half-width form).** For a probability measure, the coverage of the interval of
half-width `c` about the mean is at least `1 − variance/c²`. This is the complement of Chebyshev's
inequality. -/
theorem coverageBound {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : Measurable X) (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal (variance X μ / c ^ 2) ≤ μ {ω | |X ω - μ[X]| < c} := by
  have hA : MeasurableSet {ω | c ≤ |X ω - μ[X]|} :=
    measurableSet_le measurable_const (Measurable.abs (hXm.sub_const _))
  have hcompl : {ω : Ω | |X ω - μ[X]| < c} = {ω | c ≤ |X ω - μ[X]|}ᶜ := by
    ext ω; simp [not_le]
  rw [hcompl, prob_compl_eq_one_sub hA]
  exact tsub_le_tsub_left (meas_ge_le_variance_div_sq hX hc) 1

/-- The **standard uncertainty** `u = √variance` (VIM 2.30). -/
noncomputable def stdUnc (X : Ω → ℝ) (μ : Measure Ω) : ℝ := Real.sqrt (variance X μ)

/-- **R18, Tier 1 (coverage-factor form).** The metrological headline: the interval of `k`
standard uncertainties about the mean has coverage probability `≥ 1 − 1/k²` (Chebyshev). Honest
and distribution-free; `k = 2 ⇒ ≥ 75%` (the Gaussian 95% is a *shape* assumption, out of scope).
Requires a genuine (positive) standard uncertainty. -/
theorem coverageBound_stdUnc {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : Measurable X) (hX : MemLp X 2 μ) {k : ℝ} (hk : 0 < k) (hv : 0 < variance X μ) :
    1 - ENNReal.ofReal (1 / k ^ 2) ≤ μ {ω | |X ω - μ[X]| < k * stdUnc X μ} := by
  have hu : 0 < stdUnc X μ := Real.sqrt_pos.mpr hv
  have hc : 0 < k * stdUnc X μ := mul_pos hk hu
  have hsq : (k * stdUnc X μ) ^ 2 = k ^ 2 * variance X μ := by
    rw [stdUnc, mul_pow, Real.sq_sqrt hv.le]
  have hfrac : variance X μ / (k * stdUnc X μ) ^ 2 = 1 / k ^ 2 := by
    rw [hsq, mul_comm (k ^ 2) (variance X μ), ← div_div, div_self hv.ne']
  calc 1 - ENNReal.ofReal (1 / k ^ 2)
      = 1 - ENNReal.ofReal (variance X μ / (k * stdUnc X μ) ^ 2) := by rw [hfrac]
    _ ≤ μ {ω | |X ω - μ[X]| < k * stdUnc X μ} := coverageBound hXm hX hc

/-! ## Tier 2 — exact coverage for the uniform family -/

/-- **R18, Tier 2 (uniform, exact).** For `X` uniform on `[m − δ, m + δ]` (`δ > 0`), the coverage
of the centred interval `[m − h, m + h]` (`0 ≤ h ≤ δ`) is *exactly* `h/δ` — closed-form, from the
uniform's definition, and tighter than the Chebyshev bound. -/
theorem uniform_coverage_exact {P : Measure Ω} {X : Ω → ℝ} {m δ : ℝ} (hδ : 0 < δ)
    (hu : pdf.IsUniform X (Set.Icc (m - δ) (m + δ)) P)
    {h : ℝ} (_hh0 : 0 ≤ h) (hhδ : h ≤ δ) :
    P (X ⁻¹' Set.Icc (m - h) (m + h)) = ENNReal.ofReal (h / δ) := by
  set s := Set.Icc (m - δ) (m + δ) with hs
  set A := Set.Icc (m - h) (m + h) with hA
  have hsub : A ⊆ s := Set.Icc_subset_Icc (by linarith) (by linarith)
  have hvols : volume s = ENNReal.ofReal (2 * δ) := by
    rw [hs, Real.volume_Icc]; congr 1; ring
  have hvolA : volume A = ENNReal.ofReal (2 * h) := by
    rw [hA, Real.volume_Icc]; congr 1; ring
  have hns : volume s ≠ 0 := by
    rw [hvols]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hnt : volume s ≠ ∞ := by rw [hvols]; exact ENNReal.ofReal_ne_top
  rw [hu.measure_preimage hns hnt measurableSet_Icc,
    Set.inter_eq_self_of_subset_right hsub, hvolA, hvols,
    ← ENNReal.ofReal_div_of_pos (show (0:ℝ) < 2 * δ by linarith)]
  congr 1
  rw [mul_div_mul_left h δ (two_ne_zero)]

/-- A concrete uniform witness: the identity on `ℝ`, under `volume` conditioned to `s`, is uniform
on `s`. Shows the R18 uniform hypothesis is inhabited (non-vacuous). -/
theorem isUniform_id_cond (s : Set ℝ) :
    pdf.IsUniform (id : ℝ → ℝ) s (ProbabilityTheory.cond volume s) volume := by
  unfold MeasureTheory.pdf.IsUniform
  exact Measure.map_id

end PropertyKindCalculus.Uncertainty.Coverage
