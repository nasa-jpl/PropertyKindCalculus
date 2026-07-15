/-
# Worked example — Degenhardt et al. (2025), the simple fictive measurement

Reproduces Experiment 1 of *Degenhardt et al., Metrologia 62 (2025) 025004* (the SSPRC paper),
`References/Degenhardt_2025_Metrologia_62_025004.pdf`, §3.1. The fictive, intentionally
non-linear measurement model is

    Y = (X₁ + X₂²) · X₃                                                   (paper eq. 12)

with three independent influence quantities:
  * `X₁ ~ Normal(μ=2, σ=0.2)`,
  * `X₂ ~ Uniform(μ=0.5, range R=0.9)`   ⇒ half-width δ=0.45, support [0.05, 0.95],
  * `X₃ ~ Triangular(μ=5, width R=0.6)`  ⇒ half-width δ=0.3,  support [4.7, 5.3].

Everything here is a **checked fact** (the module builds under CI). It exercises the Stage-0
layer end to end: the WO1 model over `[NumCarrier α]` at `Float`, the named input distributions
as values, the Monte Carlo reference propagator, and the GUM linearized cross-check.

Ground truth (independent high-`N` Monte Carlo): `E(Y) = 11.5875`, `u(Y) ≈ 1.691`. The reference
value `R = f(E(X)) = 11.25`; the gap `E(Y) − R = 0.3375` is the non-linearity signature of the
`X₂²` term (theorem T4 of `UNCERTAINTY.md`) — exactly what the linearized methods cannot see and
what SSPRC (Stage 2) will recover. Mathlib- and TorchLean-free.
-/
import PropertyKindCalculus.Uncertainty

namespace PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

open PropertyKindCalculus PropertyKindCalculus.Paradigm PropertyKindCalculus.Uncertainty

/-! ## The kinds and the input distributions -/

/-- The measurand kind. -/
def measurandY : KindOfProperty := { id := "fictive measurand Y", scale := .ratio }
/-- A generic influence-quantity kind (the three inputs are positionally distinct, same scale). -/
def influenceX : KindOfProperty := { id := "fictive influence quantity", scale := .ratio }

/-- `X₁ ~ Normal(2, 0.2)`. -/
def x1 : InputDist Float := InputDist.normal 2.0 0.2
/-- `X₂ ~ Uniform(0.5, δ=0.45)`  (paper range `R = 2δ = 0.9`). -/
def x2 : InputDist Float := InputDist.uniform 0.5 0.45
/-- `X₃ ~ Triangular(5, δ=0.3)`  (paper width `R = 2δ = 0.6`). -/
def x3 : InputDist Float := InputDist.triangular 5.0 0.3

/-! ## The model — written once over the branchless carrier, run at `Float`

`fictiveModel` is a genuine WO1 kernel: it type-checks against any `[NumCarrier α]`, so the same
source will later interpret at `ℝ` (proofs), `FP32` (rounding), and `CudaT`/`TapeBuilder`
(GPU/autograd). Here it runs at `Float`. -/

/-- `Y = (X₁ + X₂²) · X₃`, over any branchless numeric carrier. -/
def fictiveModel {α : Type} [NumCarrier α] (a b c : α) : α := (a + b * b) * c

/-- The model as the arity-3 `List Float → Float` the propagators consume. -/
def modelF : List Float → Float
  | [a, b, c] => fictiveModel a b c
  | _ => 0.0

-- The reference value `R = f(E(X))` reduces to `(2 + 0.25)·5 = 11.25` (prints `11.250000`).
#eval modelF [x1.moments.mean, x2.moments.mean, x3.moments.mean]
#guard Float.abs (modelF [x1.moments.mean, x2.moments.mean, x3.moments.mean] - 11.25) < 1e-9

/-! ## Monte Carlo reference propagation

20 000 joint draws. `E(Y)` and `u(Y)` must match the ground-truth `11.5875 / 1.691` to within
Monte Carlo error (standard error of the mean at this `N` is `≈ 0.012`). -/

/-- `(E(Y), u(Y))` from the Monte Carlo reference. -/
def mcm : Float × Float := Mcm.run modelF [x1, x2, x3] 20000 0x1234ABCD

-- Prints e.g. `MCM  E(Y) ≈ 11.58…   u(Y) ≈ 1.69…`.
#eval s!"MCM  E(Y) ≈ {mcm.1}   u(Y) ≈ {mcm.2}"
#guard Float.abs (mcm.1 - 11.5875) < 0.1
#guard Float.abs (mcm.2 - 1.691) < 0.15

/-! ## GUM linearized cross-check

Sensitivities at the means are `c₁ = ∂Y/∂X₁ = X₃ = 5`, `c₂ = ∂Y/∂X₂ = 2·X₂·X₃ = 5`,
`c₃ = ∂Y/∂X₃ = X₁ + X₂² = 2.25` — supplied explicitly here (Stage 1 will source them from
TorchLean autograd). GUM's `u_c = √(Σ cᵢ² uᵢ²) ≈ 1.662` slightly *under*-estimates the Monte
Carlo `1.691`: the linearization drops the curvature of the `X₂²` term. That gap is the whole
motivation for the Willink and SSPRC rungs. -/

/-- GUM combined standard uncertainty with hand-supplied sensitivities. -/
def gum : Float := gumStdUnc [(5.0, x1.moments), (5.0, x2.moments), (2.25, x3.moments)]

#eval s!"GUM  u_c(Y) ≈ {gum}   (Monte Carlo u(Y) ≈ {mcm.2}; gap = non-linearity)"
#guard Float.abs (gum - 1.662) < 0.01

end PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
