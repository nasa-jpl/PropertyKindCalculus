/-
# Requirement annotations reaching into the Uncertainty layer

R14 (uncertainty propagation as a provably nested method ladder) and R15
(numerical adequacy) are discharged in the `Uncertainty` workstream. Applied from
afar. These modules pull in Mathlib (via the `Ladder` rigor layer), so this module
is not Mathlib-free.
-/

import PropertyKindCalculus.Uncertainty.Combine
import PropertyKindCalculus.Uncertainty.Ladder
import PropertyKindCalculus.Uncertainty.Coverage
import PropertyKindCalculus.Uncertainty.QuasiExtensive
import PropertyKindCalculus.Uncertainty.Adequacy
import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
import PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32
import PropertyKindCalculus.Uncertainty.Adequacy.MeanBound
import PropertyKindCalculus.UncertaintyExamples.LadderNesting
import PropertyKindCalculus.UncertaintyExamples.AdequacyLadder
import PropertyKindCalculus.UncertaintyExamples.Coverage
import PropertyKindCalculus.Requirements.Attributes

namespace PropertyKindCalculus.Uncertainty

/-! ## R14 — the provably nested ladder GUM ⊂ Willink ⊂ SSPRC -/

attribute [requirement "R14" specifies "the (κ₂, κ₄) cumulant combine-monoid the ladder rests on"]
  Cumulants
attribute [requirement "R14" implements "GUM linearized combined standard uncertainty √(Σ cᵢ² uᵢ²)"]
  gumStdUnc
attribute [requirement "R14" implements "Willink cumulant combine → (u_Y, γ_Y)"] willinkCombine
attribute [requirement "R14" proves "T1 — independent contributions add: the cumulant-additivity law"]
  willinkCumulants_cons
attribute [requirement "R14" proves "T2 — the Willink combine's second cumulant is exactly the GUM variance"]
  willinkCumulants_kappa2
attribute [requirement "R14" proves "the ladder nests: GUM is the faithful κ₄ = 0 restriction of Willink"]
  gum_eq_willink_of_normal
attribute [requirement "R14" exemplifies "two Gaussian inputs (κ₄ = 0, c = 3, 4) where the GUM and Willink combines agree"]
  PropertyKindCalculus.UncertaintyExamples.LadderNesting.normalTerms

/-! ## R15 — numerical adequacy: no information loss at the scale of the input uncertainties -/

attribute [requirement "R15" specifies "the accumulated adequacy report (swamping + cancellation site counts)"]
  AdequacyReport
attribute [requirement "R15" implements "the executable numerical-adequacy carrier over Float"]
  Adequacy
attribute [requirement "R15" proves "the absorption flag is sound and complete: flag ⇔ the contribution is lost"]
  Adequacy.verdict_sound
attribute [requirement "R15" proves "at a cancellation site the relative uncertainty reaches ≥ 100%"]
  Adequacy.relUnc_amplifies
attribute [requirement "R15" exemplifies "a 1-perturbation of grid value 80 (ulp 8) is absorbed: fl(80 + 1) = 80"]
  PropertyKindCalculus.UncertaintyExamples.AdequacyLadder.a1_absorb
attribute [requirement "R15" exemplifies "the absorption verdict is exactly right on a concrete value (A3)"]
  PropertyKindCalculus.UncertaintyExamples.AdequacyLadder.a3_verdict_sound
attribute [requirement "R15" exemplifies "near-equal subtraction is Sterbenz-exact yet amplifies relative uncertainty to 100%"]
  PropertyKindCalculus.UncertaintyExamples.AdequacyLadder.a2_relunc

/-! ## R15 — the weighted mean at binary32: the mode's own numerical adequacy -/

attribute [requirement "R15" specifies "a weighted mean compiled into the evaluation DAG whose rounding the adequacy layer bounds"]
  Adequacy.meanExpr
attribute [requirement "R15" proves "the binary32 weighted mean is within the DAG's accumulated rounding budget of the exact real mean"]
  Adequacy.mean_fp32_within_errBound
attribute [requirement "R15" proves "the mean's regularity is two conditions, one per rung — the rounded total and the exact total"]
  Adequacy.regular_meanExpr
attribute [requirement "R15" specifies "forgetting a binary32 carving to the real carving it specifies, taking the specification's own license as an argument"]
  Adequacy.specCarving

/-! ## R18 — the recorded variance certifies a coverage interval (VIM 2.36–2.38) -/

attribute [requirement "R18" specifies "the standard uncertainty u = √variance the coverage interval is measured in"]
  Coverage.stdUnc
attribute [requirement "R18" proves "Tier 1 (half-width): coverage of the interval of half-width c is ≥ 1 − variance/c² (Chebyshev)"]
  Coverage.coverageBound
attribute [requirement "R18" proves "Tier 1 (coverage factor): the k-standard-uncertainty interval has coverage ≥ 1 − 1/k², distribution-free"]
  Coverage.coverageBound_stdUnc
attribute [requirement "R18" proves "Tier 2 (uniform): the centred interval [m−h, m+h] of a uniform on [m−δ, m+δ] has coverage exactly h/δ"]
  Coverage.uniform_coverage_exact
attribute [requirement "R18" exemplifies "the central half [-1,1] of a uniform on [-2,2] has coverage exactly 1/2"]
  PropertyKindCalculus.UncertaintyExamples.Coverage.central_half_coverage

/-! ## R9 — §13.5.2 quasiextensive: additivity to within a stated tolerance -/

attribute [requirement "R9" specifies "additivity to within a named per-join tolerance — §13.5.2, the branch of Bunge's four that is about measurement rather than mereology"]
  QuasiExtensive
attribute [requirement "R9" proves "the discrepancy over a whole carving is at most the join count times the tolerance"]
  quasiExtensive_leafSum
attribute [requirement "R9" proves "§13.5.1 is §13.5.2 at zero tolerance, in both directions"]
  extensive_iff_quasiExtensive_zero
attribute [requirement "R9" proves "a tolerance below the contraction is refuted: volume on mixing is not quasiextensive under 4 mL"]
  mixing_not_quasiExtensive
attribute [requirement "R18" proves "the per-join tolerance as a coverage statement: |D| < k·u holds with probability ≥ 1 − 1/k², distribution-free"]
  join_within_tolerance

end PropertyKindCalculus.Uncertainty
