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

module

@[expose] public section Blanket

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

/-- **CDF** of the standard normal, `Φ(x)` — Hart's double-precision rational algorithm (as given
by West, *Better approximations to cumulative normal functions*, Wilmott 2005), agreeing with a
`erfc`-based reference to full double precision on both sides of its `|x| = 7.0711` branch.

The forward direction, unlike every other function in this module, because a *risk* is a
probability read off an interval rather than a sample drawn from one: the conformity assessment
asks "given this estimate and this uncertainty, what is the probability the measurand is past the
limit?", which is `Φ` and not `Φ⁻¹`. Accuracy in the far tail is the whole requirement — a
consumer's risk of `1e-9` is a meaningful answer and an approximation with `1.5e-7` absolute
error (Abramowitz & Stegun 26.2.17, the usual quick one) cannot express it. -/
def normalCDF (x : Float) : Float :=
  let a := x.abs
  let tail :=
    if a > 37.0 then 0.0
    else
      let e := Float.exp (-(a * a) / 2.0)
      if a < 7.07106781186547 then
        let n := 3.52624965998911e-02 * a + 0.700383064443688
        let n := n * a + 6.37396220353165
        let n := n * a + 33.912866078383
        let n := n * a + 112.079291497871
        let n := n * a + 221.213596169931
        let n := n * a + 220.206867912376
        let d := 8.83883476483184e-02 * a + 1.75566716318264
        let d := d * a + 16.064177579207
        let d := d * a + 86.7807322029461
        let d := d * a + 296.564248779674
        let d := d * a + 637.333633378831
        let d := d * a + 793.826512519948
        let d := d * a + 440.413735824752
        e * n / d
      else
        -- Continued-fraction tail, where the rational form above loses its accuracy.
        let b := a + 0.65
        let b := a + 4.0 / b
        let b := a + 3.0 / b
        let b := a + 2.0 / b
        let b := a + 1.0 / b
        e / b / 2.506628274631
  if x > 0.0 then 1.0 - tail else tail

/-- Inverse CDF of a symmetric triangular distribution on `[μ-δ, μ+δ]` (mode `μ`). -/
def triangularQuantile (μ δ p : Float) : Float :=
  if p ≤ 0.5 then (μ - δ) + δ * Float.sqrt (2.0 * p)
  else (μ + δ) - δ * Float.sqrt (2.0 * (1.0 - p))

/-- Inverse CDF of a uniform distribution on `[μ-δ, μ+δ]`. -/
def uniformQuantile (μ δ p : Float) : Float := μ + δ * (2.0 * p - 1.0)

/-! ## Student's `t` — the distribution of an estimate whose `u` was itself estimated

The `t` enters wherever a standard uncertainty came from a *finite* number of indications: the
estimate is then not normally distributed, its tails are heavier, and a Gaussian coverage factor
under-covers by an amount that is largest in exactly the small-`n` regime a calibration loop
starts in. `Evidence.lean` is the consumer; the numerics live here beside the normal's.

The chain is the standard one: the `t` CDF is a regularized incomplete beta, the incomplete beta
is a Lentz continued fraction, and the quantile is a bisection on the CDF (derivative-free, and
the CDF is monotone, so it cannot land on a wrong root). The whole chain is validated against
GUM Table G.2 in the probes — 46 tabulated entries, reproduced to the digits the table prints. -/

/-- `log Γ(z)` for `z ≥ 0.5` — Lanczos, `g = 7`, nine coefficients. Only ever called at `ν/2`,
`1/2` and `(ν+1)/2`, all of which are `≥ 0.5` for `ν ≥ 1`, so the reflection formula for small
`z` is deliberately absent rather than untested. -/
def logGamma (z : Float) : Float :=
  let c : Array Float := #[0.99999999999980993, 676.5203681218851, -1259.1392167224028,
    771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012,
    9.9843695780195716e-6, 1.5056327351493116e-7]
  let z := z - 1.0
  let x := Id.run do
    let mut x := c[0]!
    for i in [1:9] do x := x + c[i]! / (z + i.toFloat)
    return x
  let t := z + 7.5
  -- `log √(2π)` = 0.9189385332046727
  0.9189385332046727 + (z + 0.5) * Float.log t - t + Float.log x

/-- The continued fraction of the incomplete beta function, evaluated by Lentz's method. Iterated
a fixed 200 times with an early exit at double-precision convergence: a bounded loop needs no
termination argument, and 200 is far beyond where this converges for the arguments the `t` CDF
supplies. -/
def betaContinuedFraction (a b x : Float) : Float := Id.run do
  let fpmin := 1e-300
  let qab := a + b
  let qap := a + 1.0
  let qam := a - 1.0
  let mut c := 1.0
  let mut d := 1.0 - qab * x / qap
  if d.abs < fpmin then d := fpmin
  d := 1.0 / d
  let mut h := d
  for m in [1:201] do
    let m2 := (2 * m).toFloat
    let mf := m.toFloat
    let aa := mf * (b - mf) * x / ((qam + m2) * (a + m2))
    d := 1.0 + aa * d; if d.abs < fpmin then d := fpmin
    c := 1.0 + aa / c; if c.abs < fpmin then c := fpmin
    d := 1.0 / d
    h := h * d * c
    let aa := -(a + mf) * (qab + mf) * x / ((a + m2) * (qap + m2))
    d := 1.0 + aa * d; if d.abs < fpmin then d := fpmin
    c := 1.0 + aa / c; if c.abs < fpmin then c := fpmin
    d := 1.0 / d
    let de := d * c
    h := h * de
    if (de - 1.0).abs < 3e-16 then break
  return h

/-- The **regularized incomplete beta function** `I_x(a, b)`. The continued fraction converges
quickly only on one side of `x = (a+1)/(a+b+2)`; the symmetry `I_x(a,b) = 1 − I_{1−x}(b,a)`
carries the other side. -/
def incompleteBeta (a b x : Float) : Float :=
  if x ≤ 0.0 then 0.0
  else if x ≥ 1.0 then 1.0
  else
    let bt := Float.exp (logGamma (a + b) - logGamma a - logGamma b
      + a * Float.log x + b * Float.log (1.0 - x))
    if x < (a + 1.0) / (a + b + 2.0) then bt * betaContinuedFraction a b x / a
    else 1.0 - bt * betaContinuedFraction b a (1.0 - x) / b

/-- **CDF of Student's `t`** with `ν` degrees of freedom: `P(T ≤ t)`. -/
def studentTCDF (t ν : Float) : Float :=
  let half := 0.5 * incompleteBeta (ν / 2.0) 0.5 (ν / (ν + t * t))
  if t ≥ 0.0 then 1.0 - half else half

/-- **Quantile of Student's `t`** with `ν` degrees of freedom: the `p` for which `P(T ≤ t) = p`.
Bisection on the monotone CDF, after bracketing the root by doubling; symmetric about zero, so
only the upper half is searched. A non-finite `ν` is the normal limit and is answered by
`normalQuantile` directly — the bisection would not converge there and the limit is exact. -/
def studentTQuantile (p ν : Float) : Float :=
  if !(ν < 1.0 / 0.0) then normalQuantile p
  else if p ≤ 0.5 then -(upperHalf (1.0 - p) ν) else upperHalf p ν
where
  /-- The quantile for `p ≥ 0.5`, where the root is at or above zero. -/
  upperHalf (p ν : Float) : Float := Id.run do
    let mut lo := 0.0
    let mut hi := 1.0
    for _ in [0:200] do
      if studentTCDF hi ν ≥ p then break else hi := hi * 2.0
    for _ in [0:200] do
      let mid := 0.5 * (lo + hi)
      if studentTCDF mid ν < p then lo := mid else hi := mid
    return 0.5 * (lo + hi)

end PropertyKindCalculus.Uncertainty.Sampling

end Blanket
