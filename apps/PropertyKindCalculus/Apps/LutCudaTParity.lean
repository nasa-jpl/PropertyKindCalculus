/-
`lut_cudat_parity` — a self-checking harness for the **table-fetch kernel**
(`LutTable.fetchProgram` in `paradigm.lut_carrier`) against the fp64 reference `LutTable.refFetch`.

The kernel is a TorchLean `Kernel.Program Float32`. The harness always evaluates it in Lean on the
CPU (`Program.run`). When a LibTorch bridge with a CUDA device is linked (`-K cuda=true`) it also
runs the generated CUDA, once through `Program.run` and once on resident `CudaT` buffers
(`CudaT.lutFetchIO`). The probes cover NaN, ±∞, out-of-range and interior coordinates and layers;
`refFetch` and the kernel both return NaN on a NaN coordinate or layer. Exits `0` on parity and
`1` on mismatch.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.LutCarrier
public import TorchLean.CUDA.LibTorch.Controls

@[expose] public section Blanket

namespace PropertyKindCalculus.Apps.LutCudaTParity

open PropertyKindCalculus.Paradigm
open TorchLean

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
abbrev s : Shape := [probes.size]

/-- The table's samples as a float32 tensor. -/
def samples : Tensor Float32 [table.values.size] :=
  Tensor.ofFn fun i => table.values[i.val]!.toFloat32

/-- Float32 rounding of exactly representable samples and dyadic weights is exact; the slack only
absorbs a backend that lerps as `a·(1−f) + b·f`. -/
def tol : Float := 1e-5

/-- Count the probes whose `got` value differs from `refFetch`, printing each comparison. -/
def check (label : String) (got : Nat → Float) : IO Nat := do
  let mut bad := 0
  for i in [0:probes.size] do
    let (l, u) := probes[i]!
    let want := table.refFetch l u
    let out := got i
    let ok := if want.isNaN then out.isNaN else !out.isNaN && Float.abs (out - want) ≤ tol
    IO.println s!"{if ok then "ok  " else "FAIL"} {label} layer={l} u={u}  got={out}  refFetch={want}"
    unless ok do bad := bad + 1
  return bad

def main : IO UInt32 := do
  let layers : Tensor Float32 s := Tensor.ofFn fun i => probes[i.val]!.1.toFloat32
  let coords : Tensor Float32 s := Tensor.ofFn fun i => probes[i.val]!.2.toFloat32
  let inputs : TensorPack Float32 [s, s, [table.values.size]] :=
    .cons layers (.cons coords (.cons samples .nil))
  let read (t : Tensor Float32 s) (i : Nat) : Float :=
    if h : i < probes.size then t[(⟨i, h⟩ : Fin probes.size)].toFloat else 0.0 / 0.0
  let cpu ← table.program.run inputs s
  let mut bad ← check "cpu   " (read cpu)
  let cuda ← match ← TorchLean.LibTorch.Buffer.RuntimeStatus.query with
    | .nativeAvailable => do
      match ← TorchLean.LibTorch.deviceKind with
      | .cuda => pure true
      | .host => pure false
    | _ => pure false
  if cuda then
    let gpu ← table.program.run inputs s (device := .cuda)
    bad := bad + (← check "cuda  " (read gpu))
    let l : CudaCarrier.CudaT s := .ofFloatArray ⟨probes.map (·.1)⟩
    let u : CudaCarrier.CudaT s := .ofFloatArray ⟨probes.map (·.2)⟩
    let got := (← CudaCarrier.CudaT.lutFetchIO table l u).toFloatArray
    if got.size != probes.size then
      IO.eprintln s!"PARITY FAILED — CudaT returned {got.size} values for {probes.size} probes."
      return 1
    bad := bad + (← check "CudaT " (fun i => got.get! i))
  else
    IO.println "No CUDA device is linked: the generated CUDA was not run, only the CPU evaluation."
  if bad == 0 then
    IO.println "PARITY OK — the fetch kernel matches refFetch, NaN probes included."
    return 0
  else
    IO.eprintln s!"PARITY FAILED — {bad} comparison(s) differ from refFetch."
    return 1

end PropertyKindCalculus.Apps.LutCudaTParity

/-- The executable entry point. -/
def main : IO UInt32 := PropertyKindCalculus.Apps.LutCudaTParity.main

end Blanket
