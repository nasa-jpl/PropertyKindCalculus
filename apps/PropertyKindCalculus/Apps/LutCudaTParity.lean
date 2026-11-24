/-
`lut_cudat_parity` — a self-checking harness for the **table-fetch kernel**
(`LutTable.fetchProgram` in `paradigm.lut_carrier`) against the fp64 reference `LutTable.refFetch`.

The kernel is a TorchLean `Kernel.Program Float32`. The harness always evaluates it in Lean on the
CPU (`Program.run`). When a LibTorch bridge with a CUDA device is linked (`-K cuda=true`) it also
runs the generated CUDA, once through `Program.run` and once on resident `CudaT` buffers
(`CudaT.lutFetchIO`). The probes cover NaN, ±∞, out-of-range and interior coordinates and layers;
`refFetch` and the kernel both return NaN on a NaN coordinate or layer. Further tables check grid points,
clamped endpoints and interior points: NaN and infinite samples, finite neighbour differences that
overflow float32, a flat segment, cancelling opposite-sign samples and `-0.0` samples. `pins` fixes
`refFetch` itself on the cases where the lerp forms differ. Exits `0` on parity and `1` on mismatch.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.LutCarrier
public import TorchLean.CUDA.LibTorch.Controls

@[expose] public section Blanket

namespace PropertyKindCalculus.Apps.LutCudaTParity

open PropertyKindCalculus.Paradigm
open TorchLean

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0

/-- Two layers of four samples, all exactly representable in float32, distinct per layer. -/
def table : LutTable :=
  { name := "probe", width := 4, layers := 2,
    values := #[1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0, 128.0] }

/-- `(layer, u)` probes: NaN, ±∞ and out-of-range in each argument, plus interior points. -/
def probes : Array (Float × Float) :=
  #[(0.0, 0.0), (0.0, 1.5), (1.0, 2.25), (1.0, 3.0),
    (0.0, nan), (1.0, nan), (nan, 1.5), (nan, nan),
    (0.0, -2.0), (1.0, 7.0), (-1.0, 1.5), (5.0, 1.5),
    (0.0, inf), (0.0, -inf), (inf, 1.5), (-inf, 1.5)]

/-- A table with non-finite samples: `refFetch` multiplies the neighbour by weight zero too, so a
NaN or infinite neighbour gives NaN at a grid point. -/
def edgeTable : LutTable :=
  { name := "edge", width := 4, layers := 2,
    values := #[2.0, nan, inf, 1.0, 1.0, 2.0, 3.0, inf] }

/-- Grid points and clamped endpoints of `edgeTable`, plus one interior point per layer. -/
def edgeProbes : Array (Float × Float) :=
  #[(0.0, 0.0), (0.0, -2.0), (0.0, -inf), (0.0, 1.0), (0.0, 2.0), (0.0, 2.5), (0.0, 3.0),
    (0.0, 7.0), (1.0, 0.0), (1.0, 1.5), (1.0, 2.0), (1.0, 3.0), (1.0, inf)]

/-- `2¹²⁷`, finite in float32; the difference of `big` and `-big` overflows float32. -/
def big : Float := Float.scaleB 1.0 127

/-- The largest finite float32. -/
def fmax : Float := Float.scaleB (2.0 - Float.scaleB 1.0 (-23)) 127

/-- Finite samples whose neighbour differences overflow float32, then two at the float32 maximum:
the lerp weights opposite-sign samples separately, so it stays finite where `a + f·(b − a)` would not. -/
def overflowTable : LutTable :=
  { name := "overflow", width := 6, layers := 1, values := #[big, -big, -big, big, fmax, fmax] }

/-- Grid points, clamped endpoints and dyadic interior points of `overflowTable`. -/
def overflowProbes : Array (Float × Float) :=
  #[(0.0, 0.0), (0.0, -2.0), (0.0, -inf), (0.0, 1.0), (0.0, 2.0), (0.0, 3.0), (0.0, 4.0),
    (0.0, 5.0), (0.0, 7.0), (0.0, 0.25), (0.0, 0.5), (0.0, 1.5), (0.0, 2.75), (0.0, 4.5)]

/-- `199.900009…`, a float32 value that a lerp weighting each sample separately, `a·(1−f) + a·f`,
exceeds at `f = 55/64`. -/
def flat : Float := 13100647.0 / 65536.0

/-- A flat segment between two rising ones: the lerp returns the sample across it. -/
def flatTable : LutTable :=
  { name := "flat", width := 4, layers := 1, values := #[1.0, flat, flat, 300.0] }

/-- Interior points of the flat segment of `flatTable`, and its two ends. -/
def flatProbes : Array (Float × Float) :=
  #[(0.0, 1.0), (0.0, 1.25), (0.0, 1.5), (0.0, 1.859375), (0.0, 2.0)]

/-- Opposite-sign samples that nearly cancel: the midpoint is exactly `0.5`. -/
def cancelTable : LutTable :=
  { name := "cancel", width := 2, layers := 1, values := #[8388608.0, -8388607.0] }

def cancelProbes : Array (Float × Float) := #[(0.0, 0.0), (0.0, 0.5), (0.0, 1.0)]

/-- A single sample: every coordinate reads it as both neighbours. -/
def oneTable : LutTable := { name := "one", width := 1, layers := 1, values := #[-3.0] }

def oneProbes : Array (Float × Float) := #[(0.0, -1.0), (0.0, 0.0), (0.0, 0.5), (0.0, 2.0)]

/-- `-0.0` samples before a negative, a positive and a `-0.0` neighbour. -/
def zeroTable : LutTable :=
  { name := "zero", width := 6, layers := 1, values := #[-0.0, -1.0, -0.0, 1.0, -0.0, -0.0] }

def zeroProbes : Array (Float × Float) :=
  #[(0.0, -1.0), (0.0, 0.0), (0.0, 2.0), (0.0, 4.0), (0.0, 4.5), (0.0, 5.0), (0.0, 9.0)]

/-- Infinite samples with finite neighbours of the opposite sign. -/
def infTable : LutTable :=
  { name := "inf", width := 4, layers := 1, values := #[inf, -1.0, -inf, 1.0] }

def infProbes : Array (Float × Float) :=
  #[(0.0, 0.0), (0.0, 0.5), (0.0, 1.5), (0.0, 2.0), (0.0, 2.5)]

/-- NaN matches NaN; any other value matches bit for bit, so the two zeros differ. -/
def same (x y : Float) : Bool := if x.isNaN then y.isNaN else x.toBits == y.toBits

/-- `(table, layer, u, value)`: the value `refFetch` must return. An infinite sample gives NaN as
the left neighbour or at weight zero, and itself as the right neighbour of a finite sample in the
interior. `-0.0` survives weight zero only before a negative neighbour. -/
def pins : Array (LutTable × Float × Float × Float) :=
  #[(edgeTable, 0.0, 2.0, nan), (edgeTable, 0.0, 2.5, nan), (edgeTable, 1.0, 3.0, nan),
    (infTable, 0.0, 0.0, nan), (infTable, 0.0, 0.5, nan), (infTable, 0.0, 1.5, -inf),
    (infTable, 0.0, 2.5, nan),
    (overflowTable, 0.0, 0.0, big), (overflowTable, 0.0, 0.5, 0.0), (overflowTable, 0.0, 4.5, fmax),
    (flatTable, 0.0, 1.859375, flat), (cancelTable, 0.0, 0.5, 0.5),
    (zeroTable, 0.0, 0.0, -0.0), (zeroTable, 0.0, 2.0, 0.0), (zeroTable, 0.0, 4.0, 0.0)]

/-- Count the pins `refFetch` misses, printing each. -/
def checkPins : IO Nat := do
  let mut bad := 0
  for (tbl, l, u, want) in pins do
    let out := tbl.refFetch l u
    let ok := same out want
    IO.println s!"{if ok then "ok  " else "FAIL"} pin    {tbl.name} layer={l} u={u}  refFetch={out}  pinned={want}"
    unless ok do bad := bad + 1
  return bad

/-- Float32 rounding of exactly representable samples and dyadic weights is exact, so the slack
absorbs nothing on these probes. -/
def tol : Float := 1e-5

/-- Count the probes whose `got` value differs from `refFetch`, printing each comparison. -/
def check (tbl : LutTable) (ps : Array (Float × Float)) (label : String) (got : Nat → Float) :
    IO Nat := do
  let mut bad := 0
  for i in [0:ps.size] do
    let (l, u) := ps[i]!
    let want := tbl.refFetch l u
    let out := got i
    -- A zero must match in sign.
    let ok := if want.isNaN || want == 0 then same out want
      else out == want || Float.abs (out - want) ≤ tol
    IO.println s!"{if ok then "ok  " else "FAIL"} {label} {tbl.name} layer={l} u={u}  got={out}  refFetch={want}"
    unless ok do bad := bad + 1
  return bad

/-- Whether a LibTorch bridge with a CUDA device is linked. -/
def cudaLinked : IO Bool := do
  match ← TorchLean.LibTorch.Buffer.RuntimeStatus.query with
  | .nativeAvailable => do
    match ← TorchLean.LibTorch.deviceKind with
    | .cuda => pure true
    | .host => pure false
  | _ => pure false

/-- Run every probe of one table through the kernel; the number of mismatches with `refFetch`. -/
def runTable (tbl : LutTable) (ps : Array (Float × Float)) (cuda : Bool) : IO Nat := do
  let s : Shape := [ps.size]
  let layers : Tensor Float32 s := Tensor.ofFn fun i => ps[i.val]!.1.toFloat32
  let coords : Tensor Float32 s := Tensor.ofFn fun i => ps[i.val]!.2.toFloat32
  let samples : Tensor Float32 [tbl.values.size] :=
    Tensor.ofFn fun i => tbl.values[i.val]!.toFloat32
  let inputs : TensorPack Float32 [s, s, [tbl.values.size]] :=
    .cons layers (.cons coords (.cons samples .nil))
  let read (t : Tensor Float32 s) (i : Nat) : Float :=
    if h : i < ps.size then t[(⟨i, h⟩ : Fin ps.size)].toFloat else 0.0 / 0.0
  let cpu ← tbl.program.run inputs s
  let mut bad ← check tbl ps "cpu   " (read cpu)
  if cuda then
    let gpu ← tbl.program.run inputs s (device := .cuda)
    bad := bad + (← check tbl ps "cuda  " (read gpu))
    let l : CudaCarrier.CudaT s := .ofFloatArray ⟨ps.map (·.1)⟩
    let u : CudaCarrier.CudaT s := .ofFloatArray ⟨ps.map (·.2)⟩
    let got := (← CudaCarrier.CudaT.lutFetchIO tbl l u).toFloatArray
    if got.size != ps.size then
      IO.eprintln s!"CudaT returned {got.size} values for {ps.size} probes."
      return bad + 1
    bad := bad + (← check tbl ps "CudaT " (fun i => got.get! i))
  return bad

def main : IO UInt32 := do
  let cuda ← cudaLinked
  unless cuda do
    IO.println "No CUDA device is linked: the generated CUDA was not run, only the CPU evaluation."
  let bad := (← runTable table probes cuda) + (← runTable edgeTable edgeProbes cuda)
    + (← runTable overflowTable overflowProbes cuda) + (← runTable flatTable flatProbes cuda)
    + (← runTable cancelTable cancelProbes cuda) + (← runTable zeroTable zeroProbes cuda)
    + (← runTable infTable infProbes cuda) + (← runTable oneTable oneProbes cuda) + (← checkPins)
  if bad == 0 then
    IO.println "PARITY OK — the fetch kernel matches refFetch, NaN probes and non-finite samples included."
    return 0
  else
    IO.eprintln s!"PARITY FAILED — {bad} comparison(s) differ from refFetch."
    return 1

end PropertyKindCalculus.Apps.LutCudaTParity

/-- The executable entry point. -/
def main : IO UInt32 := PropertyKindCalculus.Apps.LutCudaTParity.main

end Blanket
