/-
# Requirement annotations reaching into the Uncertainty layer

R14 (uncertainty propagation as a provably nested method ladder) and R15
(numerical adequacy) are discharged in the `Uncertainty` workstream. Applied from
afar. These modules pull in Mathlib (via the `Ladder` rigor layer), so this module
is not Mathlib-free.
-/

import PropertyKindCalculus.Uncertainty.Combine
import PropertyKindCalculus.Uncertainty.Ladder
import PropertyKindCalculus.Uncertainty.Adequacy
import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
import PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32
import PropertyKindCalculus.UncertaintyExamples.LadderNesting
import PropertyKindCalculus.UncertaintyExamples.AdequacyLadder
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

end PropertyKindCalculus.Uncertainty
