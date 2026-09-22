/-
`PropertyKindCalculus.Uncertainty.InputDist` — the input uncertainty descriptor (Axis U).

Two structures, matching the two consumers of an input's uncertainty (see `UNCERTAINTY.md`):

  * `MomentData R` — the **carrier-parametric** moments/cumulants (mean, variance = κ₂,
    fourth cumulant = κ₄ = w, third cumulant = κ₃). This is what the linearized methods
    (GUM, Willink) consume, and what the `ℝ`-level nesting theorems are stated about. It is a
    bare record over any `R`, so it exists at `ℝ` (proofs) and `Float` (execution) alike.

  * `InputDist R` — bundles the moments with a *support* (a rigorous range, later fed to the
    numerical-adequacy check) and an **inverse-CDF sampler** (`Float → Float`, the single
    primitive shared by Monte Carlo and systematic sampling).

Per PKC's representational convention (meta-concept → structure; specific instances → values),
the named distributions (`normal`, `uniform`, `triangular`, …) are *values* built by smart
constructors; the cumulant constants are Willink (2005) Table 1. Applications add their own.
Stage 0 provides the `Float` constructors; the `[NumCarrier R]`-generic forms arrive with the
proof layer in Stage 1.
-/

module

public import PropertyKindCalculus.Uncertainty.Sampling

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty

/-- **Carrier-parametric moment/cumulant data** for an input quantity. `variance` is `κ₂ = u²`;
`fourthCumulant` is `κ₄ = w` (Willink Table 1), zero for a normal; `thirdCumulant` is `κ₃`
(asymmetry, zero for the symmetric families). Consumed by the linearized methods and proved
about over `ℝ`. -/
structure MomentData (R : Type) where
  /-- Expected value `E(Xᵢ)`. -/
  mean : R
  /-- Variance `u²` (the second cumulant κ₂). -/
  variance : R
  /-- Fourth cumulant `w` (κ₄); `0` for a normal distribution. -/
  fourthCumulant : R
  /-- Third cumulant `κ₃` (asymmetry); `0` for symmetric distributions. (No default: `R` is an
  unconstrained carrier, so there is no generic `0` to default to — set it at each site.) -/
  thirdCumulant : R

/-- **The input uncertainty descriptor.** Carrier-parametric `moments`, an optional rigorous
`support` (for the numerical-adequacy check), and an `invCDF` sampler shared by MCM and SSPRC. -/
structure InputDist (R : Type) where
  /-- The carrier-parametric moments/cumulants. -/
  moments : MomentData R
  /-- Rigorous support `[lo, hi]`, when the distribution is bounded (feeds numerical adequacy). -/
  support : Option (R × R) := none
  /-- Inverse CDF: maps a probability `p ∈ (0,1)` to a sample. Random `p` ⇒ MCM; systematic
  `p = (j-0.5)/N` ⇒ SSPRC. Concrete `Float`: sampling yields concrete numbers. -/
  invCDF : Float → Float

/-- `Normal(μ, σ)`. Willink Table 1: `u² = σ²`, `w = 0`; unbounded support. -/
def InputDist.normal (μ σ : Float) : InputDist Float where
  moments := { mean := μ, variance := σ * σ, fourthCumulant := 0.0, thirdCumulant := 0.0 }
  support := none
  invCDF := fun p => μ + σ * Sampling.normalQuantile p

/-- `Uniform` on `[μ-δ, μ+δ]` (half-width `δ`; the paper's "range" is `R = 2δ`). Willink Table 1:
`u² = δ²/3`, `w = -4δ⁴/30`. -/
def InputDist.uniform (μ δ : Float) : InputDist Float where
  moments := { mean := μ, variance := δ*δ/3.0, fourthCumulant := -4.0*(δ*δ*δ*δ)/30.0,
               thirdCumulant := 0.0 }
  support := some (μ - δ, μ + δ)
  invCDF := Sampling.uniformQuantile μ δ

/-- Symmetric `Triangular` on `[μ-δ, μ+δ]` (mode `μ`, half-width `δ`). Willink Table 1:
`u² = δ²/6`, `w = -δ⁴/60`. -/
def InputDist.triangular (μ δ : Float) : InputDist Float where
  moments := { mean := μ, variance := δ*δ/6.0, fourthCumulant := -(δ*δ*δ*δ)/60.0,
               thirdCumulant := 0.0 }
  support := some (μ - δ, μ + δ)
  invCDF := Sampling.triangularQuantile μ δ

/-- `Arc-sine` on `[μ-δ, μ+δ]`. Willink Table 1: `u² = δ²/2`, `w = -3δ⁴/8`. -/
def InputDist.arcsine (μ δ : Float) : InputDist Float where
  moments := { mean := μ, variance := δ*δ/2.0, fourthCumulant := -3.0*(δ*δ*δ*δ)/8.0,
               thirdCumulant := 0.0 }
  support := some (μ - δ, μ + δ)
  invCDF := fun p => μ - δ * Float.cos (3.141592653589793 * p)  -- arcsine inverse CDF

end PropertyKindCalculus.Uncertainty

end -- pkc-blanket-expose
end -- pkc-blanket
