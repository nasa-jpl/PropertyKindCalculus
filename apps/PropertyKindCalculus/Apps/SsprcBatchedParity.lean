/-
`ssprc_batched_parity` — a self-checking harness for the **batched `CudaT` SSPRC propagator**
(`PropertyKindCalculus.Uncertainty.SsprcBatched`, Stage 4 of `UNCERTAINTY.md`).

`CudaT`'s device ops are `@[extern]` FFI with no interpreter fallback, and the TorchLean dependency
graph cannot be `precompileModules`-loaded into the elaborator (upstream `ProofWidgets`/`QuantumInfo`
`:shared` facets do not build), so the batched propagator's *numbers* cannot be checked with a
build-time `#guard` the way the pure-`Float`/`ℝ` examples are. A **compiled executable**, however,
links the native `CudaT` code directly — so this harness *runs* the batched propagator and asserts it
agrees with the Stage-2 scalar `Ssprc.run`.

Run it with `lake exe ssprc_batched_parity` from a build that links TorchLean's LibTorch bridge.
`-K libtorch=true` with a CPU-only LibTorch SDK runs the `CudaT` ops on the host through ATen's CPU
kernels (float32, no GPU, no toolkit) — what CI does; `-K cuda=true` with a CUDA SDK (in the
`torchlean-development-slim:gpu` container) runs the *same* harness on the device. The default build
links TorchLean's "unavailable" backend, on which the first device op fails with an explanation. The
harness prints the device the bridge selected before its numbers. It exits `0` on parity, `1` on
mismatch (so CI can gate on it as a `lake exe` step).
-/

module

public import PropertyKindCalculus.Uncertainty.SsprcBatched
public import PropertyKindCalculus.Uncertainty.Ssprc
public import PropertyKindCalculus.Uncertainty.InputDist
public import PropertyKindCalculus.Uncertainty.Carriers
public import NN.Runtime.Autograd.Engine.LibTorch.Controls

@[expose] public section Blanket

namespace PropertyKindCalculus.Apps.SsprcBatchedParity

open PropertyKindCalculus.Paradigm (NumCarrier)
open PropertyKindCalculus.Uncertainty

/-- Degenhardt's fictive measurement `Y = (X₁ + X₂²)·X₃`, written once over any `[NumCarrier α]` —
run here at both `Float` (the scalar reference) and `CudaT` (the batched device carrier). -/
def modelL {α : Type} [NumCarrier α] : List α → α
  | [a, b, c] => (a + b * b) * c
  | _         => 0

/-- The three independent influence quantities (Degenhardt §3.1). -/
def inputs : List (InputDist Float) :=
  [InputDist.normal 2.0 0.2, InputDist.uniform 0.5 0.45, InputDist.triangular 5.0 0.3]

/-- Per-input systematic sample counts `Nᵢ`. -/
def ns : List Nat := [200, 200, 200]

/-- Parity tolerance between the float32 batched run and the float64 scalar reference. Observed
on the host (ATen's CPU kernels): `|ΔE|≈1e-6`, `|Δu|≈1e-6`; `1e-3` keeps three orders of magnitude for float32 rounding and a GPU's
different reduction/summation order, while still catching any structural (sampling/reduction) bug,
whose divergence is of order `0.1+`. -/
def tol : Float := 1e-3

def main : IO UInt32 := do
  -- Which device the bridge selected, said before any number: the same harness runs on the host
  -- (a CPU-only SDK, or `TORCHLEAN_LIBTORCH_DEVICE=cpu`) and on a CUDA device, and a parity line
  -- that does not say which it measured is a line nobody can compare. A build with no bridge, or
  -- a CUDA SDK with no visible device, is refused here with exit `2` — distinct from `1`, a
  -- parity failure — rather than left to the first device op's panic.
  match Runtime.Autograd.LibTorch.Buffer.runtimeStatus with
  | .notLinked =>
    IO.eprintln "CANNOT RUN — this build links no LibTorch bridge (TorchLean's default backend). \
Build with `-K libtorch=true -K libtorch_home=<CPU-only SDK>` (scripts/libtorch-cpu-sdk.sh) \
or `-K cuda=true` with a CUDA SDK."
    return 2
  | .nativeUnavailable =>
    IO.eprintln "CANNOT RUN — the LibTorch bridge is linked but selected no device (a CUDA SDK \
with no visible CUDA device; TORCHLEAN_LIBTORCH_DEVICE=cpu selects the host instead)."
    return 2
  | .nativeAvailable =>
    IO.println s!"LibTorch device : {match ← Runtime.Autograd.LibTorch.deviceKind with
      | .host => "host" | .cuda => "cuda"}"
  let (ebB, ubB) := SsprcBatched.run modelL inputs ns          -- batched, over CudaT
  let (ebR, ubR) := Ssprc.run (modelL (α := Float)) inputs ns   -- scalar reference, over Float
  IO.println s!"batched (CudaT) : E(Y) = {ebB}   u(Y) = {ubB}"
  IO.println s!"scalar  (Float) : E(Y) = {ebR}   u(Y) = {ubR}"
  let dE := Float.abs (ebB - ebR)
  let dU := Float.abs (ubB - ubR)
  IO.println s!"|ΔE(Y)| = {dE}    |Δu(Y)| = {dU}    (tol {tol})"
  if dE < tol && dU < tol then
    IO.println "PARITY OK — the batched CudaT propagator matches the scalar SSPRC reference."
    return 0
  else
    IO.eprintln "PARITY FAILED — batched result diverges from the scalar SSPRC reference."
    return 1

end PropertyKindCalculus.Apps.SsprcBatchedParity

/-- The executable entry point. -/
def main : IO UInt32 := PropertyKindCalculus.Apps.SsprcBatchedParity.main

end Blanket
