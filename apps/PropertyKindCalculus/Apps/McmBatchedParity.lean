/-
`mcm_batched_parity` — a self-checking harness for the **batched `CudaT` Monte Carlo propagator**
(`PropertyKindCalculus.Uncertainty.McmBatched`, Stage 4 of `UNCERTAINTY.md`).

`CudaT`'s device ops are `@[extern]` FFI with no interpreter fallback, and the TorchLean dependency
graph cannot be `precompileModules`-loaded into the elaborator (upstream `ProofWidgets`/`QuantumInfo`
`:shared` facets do not build), so the batched propagator's *numbers* cannot be checked with a
build-time `#guard` the way the pure-`Float`/`ℝ` examples are. A **compiled executable**, however,
links the native `CudaT` code directly — so this harness *runs* the batched propagator and asserts it
agrees with the Stage-0 scalar `Mcm.run`.

The comparison is meaningful because both sides consume the *same* draws: `McmBatched.sampleColumns`
reproduces `Mcm.run`'s interleaved PRNG order rather than filling each column from its own stream.
Two independent Monte Carlo runs of the same model would also agree to within sampling noise, and a
harness comparing those would pass while a structural bug — a transposed column, a dropped input, a
sample-variance-for-population-variance slip — went unnoticed. Here the only differences that remain
are float32 rounding and reduction order.

Run it with `lake exe mcm_batched_parity`. On the default build the `CudaT` ops are the portable CPU
**stub** (float32), so this checks parity without a GPU; a `-K cuda=true` build (in the
`torchlean-development-slim:gpu` container) runs the *same* harness on the device. It exits `0` on
parity, `1` on mismatch (so CI can gate on it as a `lake exe` step).
-/

module

public import PropertyKindCalculus.Uncertainty.McmBatched
public import PropertyKindCalculus.Uncertainty.Mcm
public import PropertyKindCalculus.Uncertainty.InputDist
public import PropertyKindCalculus.Uncertainty.Carriers

@[expose] public section Blanket

namespace PropertyKindCalculus.Apps.McmBatchedParity

open PropertyKindCalculus.Paradigm (NumCarrier)
open PropertyKindCalculus.Uncertainty

/-- Degenhardt's fictive measurement `Y = (X₁ + X₂²)·X₃`, written once over any `[NumCarrier α]` —
run here at both `Float` (the scalar reference) and `CudaT` (the batched device carrier). The same
kernel the SSPRC harness uses, so the two Stage-4 propagators are checked on one model. -/
def modelL {α : Type} [NumCarrier α] : List α → α
  | [a, b, c] => (a + b * b) * c
  | _         => 0

/-- The three independent influence quantities (Degenhardt §3.1). -/
def inputs : List (InputDist Float) :=
  [InputDist.normal 2.0 0.2, InputDist.uniform 0.5 0.45, InputDist.triangular 5.0 0.3]

/-- The number of joint draws. -/
def n : Nat := 4096

/-- The PRNG seed, so both sides draw the same stream. -/
def seed : UInt64 := 20260904

/-- Parity tolerance between the float32 batched run and the float64 scalar reference. Both sides
consume the *same* draws, so sampling noise is not a source of difference here — only float32
rounding and the reduction's summation order are, and at `n = 4096` those are what the tolerance has
to cover. Observed on the CPU stub: `|ΔE| ≈ 4e-6`, `|Δu| ≈ 4e-5`, so `1e-3` keeps ~25× margin for a
GPU's different reduction order while still gating tightly. Measured, not assumed: transposing input
columns `0` and `2` gives `|ΔE| = 0.94`, `|Δu| = 0.48` — four orders of magnitude outside this
tolerance, and the harness reports `PARITY FAILED` and exits `1`. -/
def tol : Float := 1e-3

def main : IO UInt32 := do
  let (ebB, ubB) := McmBatched.run modelL inputs n seed                  -- batched, over CudaT
  let (ebR, ubR) := Mcm.run (modelL (α := Float)) inputs n seed          -- scalar reference
  IO.println s!"batched (CudaT) : E(Y) = {ebB}   u(Y) = {ubB}"
  IO.println s!"scalar  (Float) : E(Y) = {ebR}   u(Y) = {ubR}"
  let dE := Float.abs (ebB - ebR)
  let dU := Float.abs (ubB - ubR)
  IO.println s!"|ΔE(Y)| = {dE}    |Δu(Y)| = {dU}    (tol {tol})"
  if dE < tol && dU < tol then
    IO.println "PARITY OK — the batched CudaT propagator matches the scalar MCM reference."
    return 0
  else
    IO.eprintln "PARITY FAILED — batched result diverges from the scalar MCM reference."
    return 1

end PropertyKindCalculus.Apps.McmBatchedParity

/-- The executable entry point. -/
def main : IO UInt32 := PropertyKindCalculus.Apps.McmBatchedParity.main

end Blanket
