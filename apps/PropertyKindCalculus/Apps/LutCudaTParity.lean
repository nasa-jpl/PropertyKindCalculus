/-
`lut_cudat_parity` — a self-checking harness for the **eager `CudaT` table lookup**
(`LutInterp (CudaT s)` in `paradigm.lut_carrier`) against the fp64 reference `LutTable.refFetch`.

`refFetch` sends a NaN coordinate to sample 0 and a NaN layer to layer 0; the `CudaT` instance
reaches the same answer through TorchLean's `Buffer.tableSegments`, whose clamp selects the lower
bound on NaN. Like `ssprc_batched_parity`, the `CudaT` numbers can only be checked by a compiled
executable linked against TorchLean's LibTorch bridge (`-K libtorch=true` with the CPU-only SDK
from `scripts/libtorch-cpu-sdk.sh`, or `-K cuda=true` on a GPU). The probes cover NaN, ±∞,
out-of-range and interior coordinates and layers. Exits `0` on parity, `1` on mismatch, `2` when
no bridge is linked.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.LutCarrier
public import NN.Runtime.Autograd.Engine.LibTorch.Controls

@[expose] public section Blanket

namespace PropertyKindCalculus.Apps.LutCudaTParity

open PropertyKindCalculus.Paradigm
open Spec

/-- Two layers of four samples, all exactly representable in float32, distinct per layer. -/
def table : LutTable :=
  { name := "probe", width := 4, layers := 2,
    values := #[1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0, 128.0] }

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0

/-- `(layer, u)` probes: NaN, ±∞ and out-of-range in each argument, plus interior points. -/
def probes : Array (Float × Float) :=
  #[(0.0, 0.0), (0.0, 1.5), (1.0, 2.25), (1.0, 3.0),
    (0.0, nan), (1.0, nan), (nan, 1.5), (nan, nan),
    (0.0, -2.0), (1.0, 7.0), (-1.0, 1.5), (5.0, 1.5),
    (0.0, inf), (0.0, -inf), (inf, 1.5), (-inf, 1.5)]

/-- The probes' shape: one element per probe. -/
abbrev s : Shape := .dim probes.size .scalar

/-- Float32 rounding of exactly representable samples and dyadic weights is exact; the slack only
absorbs a backend that lerps as `a·(1−f) + b·f`. -/
def tol : Float := 1e-5

def main : IO UInt32 := do
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
  let layers : CudaCarrier.CudaT s := .ofFloatArray ⟨probes.map (·.1)⟩
  let coords : CudaCarrier.CudaT s := .ofFloatArray ⟨probes.map (·.2)⟩
  let got := (LutInterp.lutFetch table layers coords).toFloatArray
  let mut bad := 0
  for i in [0:probes.size] do
    let (l, u) := probes[i]!
    let want := table.refFetch l u
    let out := got.get! i
    let ok := !out.isNaN && Float.abs (out - want) ≤ tol
    IO.println s!"{if ok then "ok  " else "FAIL"} layer={l} u={u}  CudaT={out}  refFetch={want}"
    unless ok do bad := bad + 1
  if got.size != probes.size then
    IO.eprintln s!"PARITY FAILED — CudaT returned {got.size} values for {probes.size} probes."
    return 1
  if bad == 0 then
    IO.println "PARITY OK — the CudaT lookup matches refFetch, NaN probes included."
    return 0
  else
    IO.eprintln s!"PARITY FAILED — {bad} probe(s) differ from refFetch."
    return 1

end PropertyKindCalculus.Apps.LutCudaTParity

/-- The executable entry point. -/
def main : IO UInt32 := PropertyKindCalculus.Apps.LutCudaTParity.main

end Blanket
