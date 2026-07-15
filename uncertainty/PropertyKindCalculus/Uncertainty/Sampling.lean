/-
`PropertyKindCalculus.Uncertainty.Sampling` — the deterministic pieces every sampler shares.

Two ingredients feed both propagation methods of `UNCERTAINTY.md`:

  * a small, self-contained **PRNG** (`splitmix64`) mapping a `UInt64` state to a uniform
    draw in `[0,1)` — used by the Monte Carlo reference (random probabilities) and, later, by
    the systematic sampler (SSPRC uses fixed probabilities `(j-0.5)/N`, so it needs no PRNG at
    all; the *inverse-CDF* below is the shared primitive);
  * **quantile functions** (inverse CDFs) that turn a probability `p ∈ (0,1)` into a sample of
    a named input distribution. The inverse-CDF is exactly the single primitive shared by MCM
    and SSPRC — MCM feeds it random `p`, SSPRC feeds it systematic `p`.

Everything here is concrete `Float`: sampling produces concrete numbers regardless of the
proof carrier `R`. The carrier-parametric *moment* data lives in `InputDist` and is what the
linearized methods and the `ℝ`-level proofs consume. Mathlib-free.
-/
namespace PropertyKindCalculus.Uncertainty.Sampling

/-! ## PRNG — splitmix64 -/

/-- One step of splitmix64: given state `s`, return `(uniformBits, nextState)`. A well-tested,
fully deterministic generator adequate for reference Monte Carlo; no external dependency. -/
def next (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  let z := z ^^^ (z >>> 31)
  (z, s)

/-- Map 64 random bits to a `Float` in `[0,1)` using the top 53 bits (the `Float` mantissa). -/
def toUnit (z : UInt64) : Float :=
  (z >>> 11).toNat.toFloat / 9007199254740992.0  -- 2^53

/-! ## Quantile functions (inverse CDFs) -/

/-- Inverse CDF of the standard normal (Acklam's rational approximation; absolute error
`< 1.15e-9` over `(0,1)`). `μ + σ * normalQuantile p` samples `Normal(μ, σ)`. -/
def normalQuantile (p : Float) : Float :=
  let a1 := -39.69683028665376
  let a2 := 220.9460984245205
  let a3 := -275.9285104469687
  let a4 := 138.3577518672690
  let a5 := -30.66479806614716
  let a6 := 2.506628277459239
  let b1 := -54.47609879822406
  let b2 := 161.5858368580409
  let b3 := -155.6989798598866
  let b4 := 66.80131188771972
  let b5 := -13.28068155288572
  let c1 := -0.007784894002430293
  let c2 := -0.3223964580411365
  let c3 := -2.400758277161838
  let c4 := -2.549732539343734
  let c5 := 4.374664141464968
  let c6 := 2.938163982698783
  let d1 := 0.007784695709041462
  let d2 := 0.3224671290700398
  let d3 := 2.445134137142996
  let d4 := 3.754408661907416
  let plow := 0.02425
  let phigh := 1.0 - plow
  if p < plow then
    let q := Float.sqrt (-2.0 * Float.log p)
    (((((c1*q+c2)*q+c3)*q+c4)*q+c5)*q+c6) / ((((d1*q+d2)*q+d3)*q+d4)*q+1.0)
  else if p ≤ phigh then
    let q := p - 0.5
    let r := q*q
    (((((a1*r+a2)*r+a3)*r+a4)*r+a5)*r+a6)*q / (((((b1*r+b2)*r+b3)*r+b4)*r+b5)*r+1.0)
  else
    let q := Float.sqrt (-2.0 * Float.log (1.0 - p))
    (0.0 - (((((c1*q+c2)*q+c3)*q+c4)*q+c5)*q+c6)) / ((((d1*q+d2)*q+d3)*q+d4)*q+1.0)

/-- Inverse CDF of a symmetric triangular distribution on `[μ-δ, μ+δ]` (mode `μ`). -/
def triangularQuantile (μ δ p : Float) : Float :=
  if p ≤ 0.5 then (μ - δ) + δ * Float.sqrt (2.0 * p)
  else (μ + δ) - δ * Float.sqrt (2.0 * (1.0 - p))

/-- Inverse CDF of a uniform distribution on `[μ-δ, μ+δ]`. -/
def uniformQuantile (μ δ p : Float) : Float := μ + δ * (2.0 * p - 1.0)

end PropertyKindCalculus.Uncertainty.Sampling
