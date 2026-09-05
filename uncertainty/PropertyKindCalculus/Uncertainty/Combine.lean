/-
`PropertyKindCalculus.Uncertainty.Combine` — the linearized moment-combine methods (GUM & Willink).

Both take a list of `(cᵢ, MomentData)` terms — a sensitivity coefficient `cᵢ = ∂f/∂Xᵢ` paired
with the input's moments — and combine them under the independence-additivity of cumulants
(Willink 2005, eq. 3). Stage 0 supplies the `cᵢ` **explicitly**; Stage 1 sources them from
TorchLean autograd (`func.grad`), leaving these combine functions unchanged.

  * `gumStdUnc`   — GUM/LPU: `u_c = √(Σ cᵢ² uᵢ²)` (second cumulant only).
  * `willinkCombine` / `willinkHalfWidth99` — Willink's cumulants method: also combines the
    fourth cumulant, forms the excess `γ_Y`, and reads an expanded-uncertainty half-width off
    the Pearson family via the rational coverage-factor fits (eqs. 6/7). Those fits are stated
    on `-1.2 ≤ γ ≤ 6`; the `?`-suffixed forms carry that range in their return type and are
    what a report should use.

These are the coarse rungs of the GUM ⊂ Willink ⊂ SSPRC ladder; `gumStdUnc` is exactly the
`κ₂`-projection of `willinkCombine` (theorem T2, proved over `ℝ` in Stage 1). Mathlib-free.
-/
import PropertyKindCalculus.Uncertainty.InputDist

namespace PropertyKindCalculus.Uncertainty

/-- **GUM / law-of-propagation combined standard uncertainty:** `√(Σ cᵢ² uᵢ²)`. -/
def gumStdUnc (terms : List (Float × MomentData Float)) : Float :=
  Float.sqrt (terms.foldl (fun acc t => acc + t.1 * t.1 * t.2.variance) 0.0)

/-- **Willink cumulant combine** → `(u_Y, γ_Y)`: the combined standard uncertainty and the
coefficient of excess (kurtosis) `γ_Y = w_Y / u_Y⁴`, with `u_Y² = Σ cᵢ² uᵢ²` and
`w_Y = Σ cᵢ⁴ wᵢ`. -/
def willinkCombine (terms : List (Float × MomentData Float)) : Float × Float :=
  let uY2 := terms.foldl (fun acc t => acc + t.1 * t.1 * t.2.variance) 0.0
  let wY  := terms.foldl (fun acc t => acc + t.1 * t.1 * t.1 * t.1 * t.2.fourthCumulant) 0.0
  let uY  := Float.sqrt uY2
  (uY, wY / (uY2 * uY2))

/-! ## The Pearson coverage factors, and the excess range they are stated on

Willink's eqs. (6) and (7) are **rational fits** to the Pearson-family percentage points,
stated on `-1.2 ≤ γ ≤ 6`. Outside that range the fit is not the closure it approximates: both
denominators have negative discriminant, so nothing divides by zero and nothing signals — the
expression simply returns a number that is no longer a coverage factor.

That is a threshold that decides silently, so the domain is named here and carried in the
return type. `willinkK95`/`willinkK99` remain the fits themselves, total and available (T2's
collapse at `γ = 0` is a statement about the fit, and `Ladder.k95_zero` needs it
unconditionally). Every function that *reports* a coverage factor or a half-width is the
`?`-suffixed one, which returns `none` outside the domain rather than a plausible number.

Refusing rather than clamping is deliberate: clamping would return `k(6)` for `γ = 10` and
report it as the coverage factor for an excess of 10, which is the same silent substitution
one level further in. A caller that wants the clamped value can clamp its own `γ` and say so;
a caller that reads `none` is told that the method has nothing to say. -/

/-- The lower end of the excess range Willink's rational fits are stated on. -/
def pearsonFitLo : Float := -1.2

/-- The upper end of the excess range Willink's rational fits are stated on. -/
def pearsonFitHi : Float := 6.0

/-- **Is the coefficient of excess inside the range the fits are stated on?** `NaN` fails
this test, and so is refused with everything else outside the range. -/
def inPearsonFitDomain (g : Float) : Bool := pearsonFitLo ≤ g && g ≤ pearsonFitHi

/-- Willink eq. (6): the 95% Pearson coverage factor `k₀.₉₅(γ)`, the rational fit itself,
evaluated wherever it is asked. Use `willinkK95?` to report one. -/
def willinkK95 (g : Float) : Float :=
  (1.96 + 1.845*g + 0.47*g*g) / (1.0 + 0.906*g + 0.239*g*g)

/-- Willink eq. (7): the 99% Pearson coverage factor `k₀.₉₉(γ)`, the rational fit itself.
Use `willinkK99?` to report one. -/
def willinkK99 (g : Float) : Float :=
  (2.5758 + 2.6736*g + 0.7685*g*g) / (1.0 + 0.8864*g + 0.2362*g*g)

/-- **The 95% coverage factor where the fit is stated**, and `none` elsewhere. -/
def willinkK95? (g : Float) : Option Float :=
  if inPearsonFitDomain g then some (willinkK95 g) else none

/-- **The 99% coverage factor where the fit is stated**, and `none` elsewhere. -/
def willinkK99? (g : Float) : Option Float :=
  if inPearsonFitDomain g then some (willinkK99 g) else none

/-- Willink 95% expanded-uncertainty half-width `h₀.₉₅ = k₀.₉₅(γ_Y) · u_Y`, the fit applied
at whatever excess the combine produced. -/
def willinkHalfWidth95 (terms : List (Float × MomentData Float)) : Float :=
  let (uY, gY) := willinkCombine terms
  willinkK95 gY * uY

/-- Willink 99% expanded-uncertainty half-width `h₀.₉₉ = k₀.₉₉(γ_Y) · u_Y`. -/
def willinkHalfWidth99 (terms : List (Float × MomentData Float)) : Float :=
  let (uY, gY) := willinkCombine terms
  willinkK99 gY * uY

/-- **The 95% half-width where the combined excess is inside the fit's range**, and `none`
elsewhere — the form to report. -/
def willinkHalfWidth95? (terms : List (Float × MomentData Float)) : Option Float :=
  let (uY, gY) := willinkCombine terms
  (willinkK95? gY).map (· * uY)

/-- **The 99% half-width where the combined excess is inside the fit's range**, and `none`
elsewhere — the form to report. -/
def willinkHalfWidth99? (terms : List (Float × MomentData Float)) : Option Float :=
  let (uY, gY) := willinkCombine terms
  (willinkK99? gY).map (· * uY)

/-- The combined coefficient of excess, named so a caller can report it beside the verdict
rather than recomputing the combine. -/
def willinkExcess (terms : List (Float × MomentData Float)) : Float :=
  (willinkCombine terms).2

end PropertyKindCalculus.Uncertainty
