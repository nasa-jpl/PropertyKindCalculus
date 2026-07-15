/-
`PropertyKindCalculus.Uncertainty.Combine` — the linearized moment-combine methods (GUM & Willink).

Both take a list of `(cᵢ, MomentData)` terms — a sensitivity coefficient `cᵢ = ∂f/∂Xᵢ` paired
with the input's moments — and combine them under the independence-additivity of cumulants
(Willink 2005, eq. 3). Stage 0 supplies the `cᵢ` **explicitly**; Stage 1 sources them from
TorchLean autograd (`func.grad`), leaving these combine functions unchanged.

  * `gumStdUnc`   — GUM/LPU: `u_c = √(Σ cᵢ² uᵢ²)` (second cumulant only).
  * `willinkCombine` / `willinkHalfWidth99` — Willink's cumulants method: also combines the
    fourth cumulant, forms the excess `γ_Y`, and reads an expanded-uncertainty half-width off
    the Pearson family via the rational coverage-factor fits (eqs. 6/7).

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

/-- Willink eq. (6): the 95% Pearson coverage factor `k₀.₉₅(γ)` (valid `-1.2 ≤ γ ≤ 6`). -/
def willinkK95 (g : Float) : Float :=
  (1.96 + 1.845*g + 0.47*g*g) / (1.0 + 0.906*g + 0.239*g*g)

/-- Willink eq. (7): the 99% Pearson coverage factor `k₀.₉₉(γ)` (valid `-1.2 ≤ γ ≤ 6`). -/
def willinkK99 (g : Float) : Float :=
  (2.5758 + 2.6736*g + 0.7685*g*g) / (1.0 + 0.8864*g + 0.2362*g*g)

/-- Willink 95% expanded-uncertainty half-width `h₀.₉₅ = k₀.₉₅(γ_Y) · u_Y`. -/
def willinkHalfWidth95 (terms : List (Float × MomentData Float)) : Float :=
  let (uY, gY) := willinkCombine terms
  willinkK95 gY * uY

/-- Willink 99% expanded-uncertainty half-width `h₀.₉₉ = k₀.₉₉(γ_Y) · u_Y`. -/
def willinkHalfWidth99 (terms : List (Float × MomentData Float)) : Float :=
  let (uY, gY) := willinkCombine terms
  willinkK99 gY * uY

end PropertyKindCalculus.Uncertainty
