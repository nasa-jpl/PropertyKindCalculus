/-
# Worked example — the SSPRC ladder theorems T3/T4/T5 on concrete distributions

`Convolution.lean` proves, over `ℝ`, that convolution adds cumulants (T5), that the linearized-SSPRC
combined deviation has exactly the Willink combined cumulants (T3), and that an affine model's
combined deviation is centered so `E(Y) = R` (T4). This example *uses* those theorems as closed proof
terms on two concrete centered probability distributions — the reflection probe that keeps them
exercised and honest (a proof nobody applies can rot silently), and prints the axiom profile so the
sorry-freeness is visible.

The two inputs are symmetric discrete distributions with hand-computable cumulants:
`Z₁ = ½δ₋₁ + ½δ₁` (κ₂ = 1, κ₄ = −2) and `Z₂ = ¼δ₋₂ + ½δ₀ + ¼δ₂` (κ₂ = 2, κ₄ = −4), with
sensitivities `c₁ = 3`, `c₂ = 4`. Willink's combine then predicts
`κ₂(Y) = 3²·1 + 4²·2 = 41` and `κ₄(Y) = 3⁴·(−2) + 4⁴·(−4) = −1186`, and T3 says the convolved SSPRC
deviation reproduces exactly that. Mathlib-backed (the `ℝ` rung); TorchLean-free.
-/
import PropertyKindCalculus.Uncertainty.Convolution
import PropertyKindCalculus.Uncertainty

namespace PropertyKindCalculus.UncertaintyExamples.SsprcNesting

open PropertyKindCalculus.Uncertainty
open PropertyKindCalculus.Uncertainty.Dist

/-! ## Two concrete centered probability distributions and their declared moments -/

/-- `Z₁ = ½δ₋₁ + ½δ₁`: κ₂ = 1, κ₄ = 1 − 3·1² = −2. -/
noncomputable def Z1 : Dist := [(-1, 1/2), (1, 1/2)]
/-- `Z₂ = ¼δ₋₂ + ½δ₀ + ¼δ₂`: κ₂ = 2, κ₄ = 8 − 3·2² = −4. -/
noncomputable def Z2 : Dist := [(-2, 1/4), (0, 1/2), (2, 1/4)]

noncomputable def m1 : MomentData ℝ := { mean := 0, variance := 1, fourthCumulant := -2, thirdCumulant := 0 }
noncomputable def m2 : MomentData ℝ := { mean := 0, variance := 2, fourthCumulant := -4, thirdCumulant := 0 }

/-- The two sensitized inputs `(cᵢ, Zᵢ, mᵢ)` with `c₁ = 3`, `c₂ = 4`. -/
noncomputable def xs : List SensitizedInput := [(3, Z1, m1), (4, Z2, m2)]

/-! ## The per-input facts (each a concrete `ℝ` computation) -/

theorem Z1_prob : Z1.IsProb := by norm_num [Z1, IsProb, total]
theorem Z2_prob : Z2.IsProb := by norm_num [Z2, IsProb, total]
theorem Z1_cent : Z1.IsCentered := by norm_num [Z1, IsCentered, mean, expect]
theorem Z2_cent : Z2.IsCentered := by norm_num [Z2, IsCentered, mean, expect]
theorem Z1_k2 : Z1.kappa2 = m1.variance := by norm_num [Z1, m1, kappa2, rawMoment, expect]
theorem Z2_k2 : Z2.kappa2 = m2.variance := by norm_num [Z2, m2, kappa2, rawMoment, expect]
theorem Z1_k4 : Z1.kappa4 = m1.fourthCumulant := by norm_num [Z1, m1, kappa4, rawMoment, expect]
theorem Z2_k4 : Z2.kappa4 = m2.fourthCumulant := by norm_num [Z2, m2, kappa4, rawMoment, expect]

theorem xs_prob : ∀ t ∈ xs, (t.2.1 : Dist).IsProb := by
  intro t ht
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact Z1_prob
  · exact Z2_prob

theorem xs_cent : ∀ t ∈ xs, (t.2.1 : Dist).IsCentered := by
  intro t ht
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact Z1_cent
  · exact Z2_cent

theorem xs_k2 : ∀ t ∈ xs, (t.2.1 : Dist).kappa2 = t.2.2.variance := by
  intro t ht
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact Z1_k2
  · exact Z2_k2

theorem xs_k4 : ∀ t ∈ xs, (t.2.1 : Dist).kappa4 = t.2.2.fourthCumulant := by
  intro t ht
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact Z1_k4
  · exact Z2_k4

/-! ## The ladder theorems as closed proof terms -/

/-- **T5 (convolution adds cumulants).** For the two centered inputs, `κ₄(Z₁ ⋆ Z₂) = κ₄ Z₁ + κ₄ Z₂`. -/
example : (conv Z1 Z2).kappa4 = Z1.kappa4 + Z2.kappa4 :=
  kappa4_conv Z1 Z2 Z1_prob Z2_prob Z1_cent Z2_cent

/-- **T3 (Willink is the projection of the linearized SSPRC).** The convolved combined deviation's
cumulants equal the Willink combined cumulants of the `(cᵢ, mᵢ)` term list — exactly. -/
example : cumulantsOf (combinedDeviation xs) = willinkCumulants (termsOf xs) :=
  cumulantsOf_combinedDeviation xs xs_prob xs_cent xs_k2 xs_k4

/-- **T4 (affine reference = mean).** All inputs centered (a linear model) ⇒ the combined deviation
is centered, so `E(Y) = R` — no non-linearity offset. -/
example : (combinedDeviation xs).IsCentered :=
  combinedDeviation_isCentered xs xs_cent

/-- **T4 (the gap is `Σ cᵢ·E(Zᵢ)`).** The combined deviation's mean is the weighted sum of the
per-input deviation means (here all zero). -/
example : (combinedDeviation xs).mean = (xs.map (fun t => t.1 * t.2.1.mean)).sum :=
  mean_combinedDeviation xs xs_prob

/-- The Willink prediction is the concrete pair `(41, −1186)` — so T3 pins the SSPRC deviation's
cumulants to those numbers. -/
example : (willinkCumulants (termsOf xs)).kappa2 = 41 ∧ (willinkCumulants (termsOf xs)).kappa4 = -1186 := by
  constructor <;>
    simp only [termsOf, xs, m1, m2, willinkCumulants, termCumulants, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Cumulants.add_kappa2, Cumulants.add_kappa4, Cumulants.zero_kappa2,
      Cumulants.zero_kappa4] <;> norm_num

-- Sorry-free: the axiom profile is the usual `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`.
/-- info: 'PropertyKindCalculus.Uncertainty.cumulantsOf_combinedDeviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cumulantsOf_combinedDeviation
/-- info: 'PropertyKindCalculus.Uncertainty.Dist.kappa4_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kappa4_conv

end PropertyKindCalculus.UncertaintyExamples.SsprcNesting
