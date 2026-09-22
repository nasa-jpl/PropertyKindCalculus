/-
# Worked example — the GUM ⊂ Willink nesting theorems T1/T2 on a concrete term list

`Ladder.lean` proves, over `ℝ`, that GUM is the `κ₄ = 0` restriction of Willink (T2), resting on
cumulant additivity (T1). This example *uses* those theorems as closed proof terms on a small
concrete input list — the reflection probe that keeps them exercised and honest (a proof nobody
applies can rot silently), and prints the axiom profile so the sorry-freeness is visible.

It also shows the **executable shadow** over `Float`: for all-Gaussian inputs the `Combine.lean`
Willink 95% half-width equals `1.96 · u_c` exactly — the same collapse T2 proves over `ℝ`, now as
a `#guard` in the rounding carrier. Mathlib-backed (the `ℝ` rung); TorchLean-free.
-/

module

public import PropertyKindCalculus.Uncertainty.Ladder
meta import PropertyKindCalculus.Uncertainty.Ladder
public import PropertyKindCalculus.Uncertainty
meta import PropertyKindCalculus.Uncertainty

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.UncertaintyExamples.LadderNesting

open PropertyKindCalculus.Uncertainty

/-! ## T1 and T2 as proof terms over ℝ -/

/-- Two independent **Gaussian** inputs (`κ₄ = 0`), with sensitivities `c₁ = 3`, `c₂ = 4`. -/
def normalTerms : List (ℝ × MomentData ℝ) :=
  [ (3, { mean := 0, variance := 2, fourthCumulant := 0, thirdCumulant := 0 }),
    (4, { mean := 0, variance := 5, fourthCumulant := 0, thirdCumulant := 0 }) ]

/-- **T1 (additivity).** Prepending an input adds its cumulant contribution. -/
example (t : ℝ × MomentData ℝ) (ts : List (ℝ × MomentData ℝ)) :
    willinkCumulants (t :: ts) = termCumulants t + willinkCumulants ts :=
  willinkCumulants_cons t ts

/-- **T2 (variance agreement).** The `κ₂`-projection of the Willink combine is the GUM variance. -/
example : (willinkCumulants normalTerms).kappa2 = gumVariance normalTerms :=
  willinkCumulants_kappa2 normalTerms

/-- **T2 (capstone).** On all-Gaussian inputs the Willink 95% expanded-uncertainty half-width
equals the GUM Gaussian half-width — `gum = willink|κ₄=0` as a closed proof term. -/
example : willinkHalf95 normalTerms = gumHalf95 normalTerms :=
  gum_eq_willink_of_normal normalTerms (by intro t ht; fin_cases ht <;> rfl)

-- Sorry-free: the axiom profile is the usual `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`.
/-- info: 'PropertyKindCalculus.Uncertainty.gum_eq_willink_of_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gum_eq_willink_of_normal

/-! ## The executable shadow over `Float` -/

/-- The same two Gaussian inputs as `Float` moment data for the `Combine` layer. -/
def normalTermsF : List (Float × MomentData Float) :=
  [ (3.0, { mean := 0.0, variance := 2.0, fourthCumulant := 0.0, thirdCumulant := 0.0 }),
    (4.0, { mean := 0.0, variance := 5.0, fourthCumulant := 0.0, thirdCumulant := 0.0 }) ]

-- u_c = √(9·2 + 16·5) = √98 ≈ 9.8995 ;  γ_Y = 0 ⇒ k₀.₉₅ = 1.96.
#eval s!"GUM u_c = {gumStdUnc normalTermsF}   Willink 95% = {willinkHalfWidth95 normalTermsF}   (= 1.96·u_c)   γ_Y = {willinkExcess normalTermsF}   in fit range? {inPearsonFitDomain (willinkExcess normalTermsF)}"

-- T2's collapse point is `γ_Y = 0`, interior to the range eq. (6) is stated on
-- (`Ladder.zero_mem_pearsonFitDomain` is the `ℝ` statement of the same fact), so the
-- reporting form agrees with the unchecked one here rather than refusing.
#guard inPearsonFitDomain (willinkExcess normalTermsF)
#guard willinkHalfWidth95? normalTermsF == some (willinkHalfWidth95 normalTermsF)

-- All-Gaussian inputs ⇒ `γ_Y = 0` ⇒ the Willink 95% half-width is exactly `1.96 · u_c`:
-- the `Float` witness of T2's collapse.
#guard Float.abs (willinkHalfWidth95 normalTermsF - 1.96 * gumStdUnc normalTermsF) < 1e-9

end PropertyKindCalculus.UncertaintyExamples.LadderNesting

end -- pkc-blanket-expose
end -- pkc-blanket
