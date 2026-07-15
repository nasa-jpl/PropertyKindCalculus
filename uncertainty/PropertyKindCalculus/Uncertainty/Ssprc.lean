/-
`PropertyKindCalculus.Uncertainty.Ssprc` — the **executable SSPRC pipeline** over `Float`
(Degenhardt et al. 2025, *Metrologia* 62 025004; `UNCERTAINTY.md` §3.1, Stage 2).

SSPRC = **Systematic Sampling, Propagation, Reconstruction and Convolution** — a derivative-free
alternative to Monte Carlo that reaches the same output uncertainty at a fraction of the model
evaluations by sampling each input *systematically* and propagating each *separately*:

  1. **Systematic sampling** (`systematicSamples`, eq. 6). For input `Xᵢ` take `Nᵢ` samples at the
     equidistant cumulative probabilities `Pⱼ = (j − 0.5)/Nᵢ` and invert the CDF:
     `xᵢⱼ = CDF⁻¹(Pⱼ)`. This reuses the `InputDist.invCDF` shared with the Monte Carlo reference —
     MCM feeds it *random* probabilities, SSPRC *systematic* ones. No PRNG, fully deterministic.
  2. **Separated propagation** (`deviationDist`, eqs. 3–5). Vary only input `i`, holding the others
     at their means `E(Xₖ)`; the reference value is `R = f(E(X))` and the deviation samples are
     `aᵢⱼ = f(E(X₁),…,xᵢⱼ,…,E(Xₖ)) − R`. Because only one input moves, a real implementation reuses
     intermediate results and *simplified per-input models* — the source of the paper's ~70×
     per-evaluation speedup.
  3. **Reconstruction.** Each input's deviation distribution `Aᵢ` is the empirical distribution of
     its `aᵢⱼ` (here: equal weight `1/Nᵢ` per sample — a `FloatDist`). The paper refines this to a
     continuous **distance-density estimate** (DDE) for the *shape*; the empirical distribution
     already carries the *moments* exactly, which is all the combined `E(Y)`, `u(Y)` need.
  4. **Convolution** (`convolve`, `combinedDeviation`, eq. 11). The independent inputs' deviation
     distributions combine by convolution — the distribution of their sum — shifted back by `R`.
     (The paper uses an FFT for the same operation at scale; the direct discrete convolution here is
     its specification and is what the `ℝ`-level `Convolution` module proves the ladder theorems about.)

Because means and variances **add under convolution**, `run` reads `E(Y)` and `u(Y)` straight from
the per-input deviation distributions without materializing the (combinatorially large) convolution;
`runConv` performs the actual convolution and agrees with it, cross-validating the engine. Crucially,
systematic sampling recovers the *non-linear* mean — the reference `R` plus the non-zero means of the
deviation distributions — so SSPRC captures the very `E(Y) − R` gap the linearized GUM/Willink rungs
miss. The model is any `List Float → Float` (a WO1 `[NumCarrier α]` kernel at `Float`). Mathlib- and
TorchLean-free.
-/
import PropertyKindCalculus.Uncertainty.InputDist

namespace PropertyKindCalculus.Uncertainty.Ssprc

open PropertyKindCalculus.Uncertainty

/-! ## Step 1 — systematic sampling -/

/-- The equidistant cumulative probabilities `Pⱼ = (j − 0.5)/N`, `j = 1 … N` (Degenhardt eq. 6). -/
def probabilities (n : Nat) : List Float :=
  (List.range n).map (fun j => (j.toFloat + 0.5) / n.toFloat)

/-- **Systematic samples** of an input: `xⱼ = invCDF(Pⱼ)` at the equidistant probabilities. Fully
deterministic; the inverse-CDF is the primitive shared with the Monte Carlo reference. -/
def systematicSamples (d : InputDist Float) (n : Nat) : List Float :=
  (probabilities n).map d.invCDF

/-! ## Steps 2–3 — separated propagation and the empirical deviation distribution -/

/-- An empirical distribution as `(value, weight)` pairs — the `Float` shadow of `Convolution.Dist`. -/
abbrev FloatDist := List (Float × Float)

/-- Total weight. -/
def dtotal (d : FloatDist) : Float := (d.map (fun p => p.2)).foldl (· + ·) 0.0

/-- Weighted mean `Σ wⱼ·xⱼ` (an expectation when the total weight is `1`). -/
def dmean (d : FloatDist) : Float := (d.map (fun p => p.2 * p.1)).foldl (· + ·) 0.0

/-- Weighted (population) variance `Σ wⱼ·(xⱼ − mean)²`. -/
def dvar (d : FloatDist) : Float :=
  let m := dmean d
  (d.map (fun p => p.2 * (p.1 - m) * (p.1 - m))).foldl (· + ·) 0.0

/-- **Deviation distribution** of input `i`: vary only input `i` across its systematic samples,
holding the others at their means; each deviation `aᵢⱼ = f(…, xᵢⱼ, …) − R` carries equal weight
`1/Nᵢ`. This is the *separated* propagation — the heart of SSPRC's efficiency. -/
def deviationDist (model : List Float → Float) (means : List Float) (i : Nat)
    (d : InputDist Float) (n : Nat) (R : Float) : FloatDist :=
  (systematicSamples d n).map (fun x => (model (means.set i x) - R, 1.0 / n.toFloat))

/-- Every input's deviation distribution. `ns` gives the per-input sample count `Nᵢ` (SSPRC's freedom
to spend samples where they matter — `UNCERTAINTY.md` §3.2 item 3). -/
def deviationDists (model : List Float → Float) (inputs : List (InputDist Float))
    (ns : List Nat) : List FloatDist :=
  let means := inputs.map (fun d => d.moments.mean)
  let R := model means
  (List.range inputs.length).map (fun i =>
    match inputs[i]?, ns[i]? with
    | some d, some n => deviationDist model means i d n R
    | _, _ => [])

/-! ## Step 4 — convolution -/

/-- **Discrete convolution** of two empirical distributions — the distribution of the sum, every
pairwise sum weighted by the product of weights. The `Float` mirror of `Convolution.Dist.conv`; the
FFT of the paper is the `O(n log n)` optimization of this same operation. -/
def convolve (d1 d2 : FloatDist) : FloatDist :=
  d1.flatMap (fun p => d2.map (fun q => (p.1 + q.1, p.2 * q.2)))

/-- The combined deviation distribution: convolve all inputs' deviation distributions (identity: the
point mass at `0`). Sequential convolution, as the paper prescribes for `> 2` inputs. -/
def combinedDeviation (dists : List FloatDist) : FloatDist :=
  dists.foldr convolve [(0.0, 1.0)]

/-! ## The pipeline results -/

/-- **SSPRC combined uncertainty `(E(Y), u(Y))`** read directly from the per-input deviation
distributions. `E(Y) = R + Σ E(Aᵢ)` and `Var(Y) = Σ Var(Aᵢ)` — means and variances add under
convolution, so the (combinatorially large) convolution is not needed for the moments. The `Σ E(Aᵢ)`
term is the non-linearity correction the linearized rungs cannot produce. -/
def run (model : List Float → Float) (inputs : List (InputDist Float)) (ns : List Nat) :
    Float × Float :=
  let means := inputs.map (fun d => d.moments.mean)
  let R := model means
  let dists := deviationDists model inputs ns
  let eY := R + (dists.map dmean).foldl (· + ·) 0.0
  let varY := (dists.map dvar).foldl (· + ·) 0.0
  (eY, Float.sqrt varY)

/-- **SSPRC via the actual convolution**: build the combined deviation distribution and read its
moments (shifted by `R`). Agrees with `run` — a cross-check of the convolution engine — at the cost
of materializing the convolution (`∏ Nᵢ` points), so use it at modest `Nᵢ`. -/
def runConv (model : List Float → Float) (inputs : List (InputDist Float)) (ns : List Nat) :
    Float × Float :=
  let means := inputs.map (fun d => d.moments.mean)
  let R := model means
  let combined := combinedDeviation (deviationDists model inputs ns)
  (R + dmean combined, Float.sqrt (dvar combined))

/-- The **reference value** `R = f(E(X))` (Degenhardt eq. 4). -/
def reference (model : List Float → Float) (inputs : List (InputDist Float)) : Float :=
  model (inputs.map (fun d => d.moments.mean))

/-- Total **model evaluations** `N_s = Σ Nᵢ` (plus one for the reference) — the SSPRC efficiency
figure, additive rather than the Monte Carlo combinatorial cost. -/
def evalCount (ns : List Nat) : Nat := (ns.foldl (· + ·) 0) + 1

end PropertyKindCalculus.Uncertainty.Ssprc
