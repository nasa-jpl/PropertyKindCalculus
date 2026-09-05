/-
# Worked example — Willink (2005), the gauge-block calibration (GUM example H.1)

Reproduces the headline result of *R Willink, Metrologia 42 (2005) 329–343*
(`References/Willink_2005_Metrologia_42_329.pdf`), Appendix A / Table 4: the cumulants
("moment-based") evaluation of the calibration of a gauge block by comparison with a standard
(the same measurement as GUM example H.1).

Willink linearizes the model and absorbs each sensitivity coefficient into its error variable
(so `cᵢ = 1` throughout), then combines the **variance** and the **fourth cumulant** of the six
independent error variables. Their `(u²/nm², w/nm⁴)` are Table 4:

  1. calibration of the standard gauge      `(703.125,  211879.2)`
  2. repeated observations                   `(36.873,   407.9)`
  3. random effects of the comparator        `(25.214,   3814.5)`
  4. systematic effects of the comparator    `(45.370,   0)`
  5. difference in expansion coefficients     `(8.361,    -82.2)`
  6. difference in temperatures               `(298.481,  -60602.9)`

From these: `u_Y = √(Σ uᵢ²) = 33.4 nm`, `w_Y = Σ wᵢ`, excess `γ_Y = w_Y/u_Y⁴ = 0.124`, the 99%
Pearson coverage factor `k₀.₉₉(γ_Y) = 2.62`, and the expanded-uncertainty half-width
`h₀.₉₉ = k₀.₉₉·u_Y = 87.6 nm` (versus the GUM procedure's 93 nm — the cumulants method is
narrower because the negative-excess components make the tails of `E_Y` more normal).

This exercises the `MomentData` + `Combine` layer (the coarse rungs of the ladder) with no
sampling and no autograd — pure cumulant arithmetic reproducing a real paper number. It is the
Willink counterpart to `DegenhardtFictive`. Mathlib- and TorchLean-free.
-/
import PropertyKindCalculus.Uncertainty

namespace PropertyKindCalculus.UncertaintyExamples.WillinkGaugeBlock

open PropertyKindCalculus.Uncertainty

/-- The six error variables of Willink Table 4, as `(cᵢ = 1, MomentData)` terms (units: nm). -/
def terms : List (Float × MomentData Float) :=
  [ (1.0, { mean := 0.0, variance := 703.125, fourthCumulant := 211879.2, thirdCumulant := 0.0 }),
    (1.0, { mean := 0.0, variance := 36.873,  fourthCumulant := 407.9,    thirdCumulant := 0.0 }),
    (1.0, { mean := 0.0, variance := 25.214,  fourthCumulant := 3814.5,   thirdCumulant := 0.0 }),
    (1.0, { mean := 0.0, variance := 45.370,  fourthCumulant := 0.0,      thirdCumulant := 0.0 }),
    (1.0, { mean := 0.0, variance := 8.361,   fourthCumulant := -82.2,    thirdCumulant := 0.0 }),
    (1.0, { mean := 0.0, variance := 298.481, fourthCumulant := -60602.9, thirdCumulant := 0.0 }) ]

/-- `(u_Y, γ_Y)` — combined standard uncertainty and coefficient of excess. -/
def combined : Float × Float := willinkCombine terms
/-- 99% expanded-uncertainty half-width `h₀.₉₉`, reported through the domain check: this is
`some` exactly when the combined excess lies in the range Willink's eq. (7) is stated on. -/
def h99? : Option Float := willinkHalfWidth99? terms

/-- The same number without the check, for the `#guard`s below to compare against. -/
def h99 : Float := willinkHalfWidth99 terms

#eval s!"u_Y ≈ {combined.1} nm   γ_Y ≈ {combined.2}   in fit range? {inPearsonFitDomain combined.2}   k₀.₉₉ ≈ {willinkK99 combined.2}   h₀.₉₉ ≈ {h99} nm"

-- **The excess is inside the range eq. (7) is stated on**, so the quoted factor is a
-- coverage factor and not an extrapolation of the fit. This is the guard that makes the
-- three figures below quotable; without it they would be numbers of unknown standing.
#guard inPearsonFitDomain combined.2
#guard h99? == some h99

-- Willink's reported figures (Table 4): u_Y = 33.4 nm, γ_Y = 0.124, h₀.₉₉ = 87.6 nm.
#guard Float.abs (combined.1 - 33.4) < 0.1
#guard Float.abs (combined.2 - 0.124) < 0.005
#guard Float.abs (h99 - 87.6) < 0.2

-- **The check refuses, rather than clamping.** At an excess of 10 — outside eq. (7)'s
-- range — the fit still evaluates to a plausible-looking number, and the reporting form
-- returns nothing instead of quoting it.
#guard ¬ inPearsonFitDomain 10.0
#guard willinkK99? 10.0 == none

/-! The GUM procedure would quote a 99% half-width of 93 nm on the same data; the cumulants
method's 87.6 nm is ~5% narrower with the same 99% coverage, because the (mostly negative)
fourth cumulants pull the shape of `E_Y` toward normal. This narrowing is the informative
payoff of carrying `κ₄` — the difference between the GUM rung and the Willink rung. -/

end PropertyKindCalculus.UncertaintyExamples.WillinkGaugeBlock
