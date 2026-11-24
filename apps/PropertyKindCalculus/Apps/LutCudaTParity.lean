/-
`lut_cudat_parity` — a self-checking harness for the **table-fetch kernel**
(`LutTable.fetchProgram` in `paradigm.lut_carrier`) against the fp64 reference `LutTable.refFetch`.

The kernel is a TorchLean `Kernel.Program Float` on binary32 tensors. The harness always evaluates
it in Lean on the CPU (`Program.runBinary32`). When a LibTorch bridge with a CUDA device is linked
(`-K cuda=true`) it also runs the generated CUDA, once through `Program.runBinary32` and once on
resident `CudaT` buffers
(`CudaT.lutFetchIO`). The probes cover NaN, ±∞, out-of-range and interior coordinates and layers;
`refFetch` and the kernel both return NaN on a NaN coordinate or layer. Further tables check grid points,
clamped endpoints and interior points: NaN and infinite samples, finite neighbour differences that
overflow float32, a flat segment, cancelling opposite-sign samples and `-0.0` samples. The kernel
must equal `refFetch` on the float32 inputs, rounded once to float32, bit for bit. `pins` fixes
`refFetch` itself on the cases where float32 lerp forms differ. The same probes run through the
emitted `tl_lutfetch` helpers: the C stub when `cc` is on the path, and both Julia methods on
`Float32` data when `julia` is. The CUDA texture helper runs only inside a generated kernel on a
device, so no probe here executes it. `--require-emitted` fails when `cc` or Julia is missing
(`--julia PATH` names the Julia). Exits `0` on parity and `1` on mismatch.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.LutCarrier
public import PropertyKindCalculus.Torch.Paradigm.TapeCodegenJulia
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
the lerp is in float64, so it stays finite where `a + f·(b − a)` in float32 would not. -/
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

/-- Opposite-sign samples that nearly cancel: `0.5` at the midpoint of the first segment, and
`-0.25` at weight `0.375` of the last, where float32 products of the samples round to `0`. -/
def cancelTable : LutTable :=
  { name := "cancel", width := 4, layers := 1,
    values := #[8388608.0, -8388607.0, 4194299.0, -6990499.0] }

def cancelProbes : Array (Float × Float) :=
  #[(0.0, 0.0), (0.0, 0.5), (0.0, 1.0), (0.0, 2.0), (0.0, 2.375), (0.0, 3.0)]

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
    (cancelTable, 0.0, 2.375, -0.25),
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

/-- The table with each sample rounded to float32, as the kernel reads it. -/
def rounded (tbl : LutTable) : LutTable :=
  { tbl with values := tbl.values.map fun v => v.toFloat32.toFloat }

/-- Count the probes whose `got` value is not `refFetch` on the float32 inputs, rounded once to
float32, printing each comparison. -/
def check (tbl : LutTable) (ps : Array (Float × Float)) (label : String) (got : Nat → Float) :
    IO Nat := do
  let mut bad := 0
  for i in [0:ps.size] do
    let (l, u) := ps[i]!
    let want := ((rounded tbl).refFetch l.toFloat32.toFloat u.toFloat32.toFloat).toFloat32.toFloat
    let out := got i
    let ok := same out want
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
  let cpu ← tbl.program.runBinary32 inputs s
  let mut bad ← check tbl ps "cpu   " (read cpu)
  if cuda then
    let gpu ← tbl.program.runBinary32 inputs s (device := .cuda)
    bad := bad + (← check tbl ps "cuda  " (read gpu))
    let l : CudaCarrier.CudaT s := .ofFloatArray ⟨ps.map (·.1)⟩
    let u : CudaCarrier.CudaT s := .ofFloatArray ⟨ps.map (·.2)⟩
    let got := (← CudaCarrier.CudaT.lutFetchIO tbl l u).toFloatArray
    if got.size != ps.size then
      IO.eprintln s!"CudaT returned {got.size} values for {ps.size} probes."
      return bad + 1
    bad := bad + (← check tbl ps "CudaT " (fun i => got.get! i))
  return bad

def hex8 (b : UInt32) : String :=
  String.ofList <| (List.range 8).map fun i => Nat.digitChar ((b.toNat / 2 ^ (28 - 4 * i)) % 16)

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- A float32 printed as eight hex digits, widened to `Float`. -/
def ofHex8? (s : String) : Option Float :=
  if s.length != 8 then none else
  (s.toList.foldlM (fun n c => (hexDigit? c).map (n * 16 + ·)) 0).map fun n =>
    (Float32.ofBits n.toUInt32).toFloat

def f32Hex (x : Float) : String := hex8 x.toFloat32.toBits

/-- Whether `cmd` runs. -/
def hasTool (cmd : String) : IO Bool := do
  try return (← IO.Process.output { cmd, args := #["--version"] }).exitCode == 0
  catch _ => return false

/-- Compare one emitted helper's printed results with `refFetch`: `cols` hex words per probe. -/
def checkEmitted (tbl : LutTable) (ps : Array (Float × Float)) (labels : List String)
    (res : IO.Process.Output) : IO Nat := do
  if res.exitCode != 0 then
    IO.eprintln s!"{labels} {tbl.name}: the emitted helper failed to run:\n{res.stderr}"
    return 1
  let rows := (res.stdout.splitOn "\n").filter (· ≠ "") |>.map (·.splitOn " ") |>.toArray
  if rows.size != ps.size then
    IO.eprintln s!"{labels} {tbl.name}: {rows.size} result rows for {ps.size} probes."
    return 1
  let mut bad := 0
  for (label, c) in labels.zipIdx do
    bad := bad + (← check tbl ps label fun i => ((rows[i]!)[c]? >>= ofHex8?).getD 0.0)
  return bad

/-- Run every probe of one table through the emitted point-mode `tl_lutfetch` helpers on float32
data: the C stub, and the `Float32` and generic (`Float64`) Julia methods. -/
def runEmitted (dir : System.FilePath) (tbl : LutTable) (ps : Array (Float × Float))
    (cc : Bool) (julia : Option String) : IO Nat := do
  let tab := tbl.values.toList.map f32Hex
  let ls := ps.toList.map (f32Hex ·.1)
  let us := ps.toList.map (f32Hex ·.2)
  let mut bad := 0
  if cc then
    let cg : TapeCodegen.Codegen :=
      { inputs := #[], numOutputs := 0, body := #[], outLines := #[], tables := #[tbl] }
    let arr (nm : String) (xs : List String) :=
      s!"static const uint32_t {nm}[] = \{" ++ String.intercalate ", " (xs.map ("0x" ++ ·)) ++ "};"
    let src := String.intercalate "\n"
      [ "#include <math.h>", "#include <stdint.h>", "#include <stdio.h>", "#include <string.h>"
      , TapeCodegen.lutHelperStub cg
      , arr "tabBits" tab, arr "lBits" ls, arr "uBits" us
      , "int main(void) {"
      , s!"  float tab[{tab.length}]; memcpy(tab, tabBits, sizeof tab);"
      , s!"  for (int i = 0; i < {ps.size}; i++) \{"
      , "    float l, u; memcpy(&l, &lBits[i], 4); memcpy(&u, &uBits[i], 4);"
      , s!"    float r = tl_lutfetch(tab, {tbl.width}, {tbl.layers}, l, u);"
      , "    uint32_t b; memcpy(&b, &r, 4); printf(\"%08x\\n\", b);"
      , "  }", "  return 0;", "}", "" ]
    let cFile := dir / s!"{tbl.name}.c"
    let exe := dir / s!"{tbl.name}.out"
    IO.FS.writeFile cFile src
    let build ← IO.Process.output
      { cmd := "cc", args := #["-O2", "-ffp-contract=off", "-o", exe.toString, cFile.toString, "-lm"] }
    if build.exitCode != 0 then
      IO.eprintln s!"C stub {tbl.name}: cc failed:\n{build.stderr}"
      bad := bad + 1
    else
      bad := bad + (← checkEmitted tbl ps ["C stub"] (← IO.Process.output { cmd := exe.toString }))
  if let some julia := julia then
    let cg : TapeCodegen.Julia.JuliaCodegen :=
      { inputs := #[], numOutputs := 0, body := #[], outLines := #[], tables := #[tbl] }
    let vec (nm : String) (xs : List String) :=
      s!"{nm} = reinterpret(Float32, UInt32[" ++ String.intercalate ", " (xs.map ("0x" ++ ·)) ++ "])"
    let src := String.intercalate "\n"
      [ TapeCodegen.Julia.lutHelperJulia cg
      , vec "tab" tab, vec "ls" ls, vec "us" us
      , "generic(l, u) = invoke(tl_lutfetch, Tuple{AbstractVector{T},Int,Int,T,T} where {T<:AbstractFloat}, "
          ++ s!"tab, {tbl.width}, {tbl.layers}, l, u)"
      , "hex(x) = string(reinterpret(UInt32, x); base = 16, pad = 8)"
      , "for (l, u) in zip(ls, us)"
      , s!"    println(hex(tl_lutfetch(tab, {tbl.width}, {tbl.layers}, l, u)), \" \", hex(generic(l, u)))"
      , "end", "" ]
    let jlFile := dir / s!"{tbl.name}.jl"
    IO.FS.writeFile jlFile src
    bad := bad + (← checkEmitted tbl ps ["jl F32", "jl F64"]
      (← IO.Process.output { cmd := julia, args := #["--startup-file=no", jlFile.toString] }))
  return bad

/-- `--julia PATH` names the Julia to run (default `julia` on the path); `--require-emitted` makes a
missing `cc` or Julia a failure instead of a skip. -/
def main (args : List String) : IO UInt32 := do
  let rec parse : List String → String × Bool → Except String (String × Bool)
    | [], o => .ok o
    | "--julia" :: p :: rest, (_, req) =>
      if p.isEmpty || p.startsWith "-" then .error s!"--julia needs a path, got '{p}'"
      else parse rest (p, req)
    | "--require-emitted" :: rest, (j, _) => parse rest (j, true)
    | a :: _, _ => .error s!"unknown argument: {a} (usage: lut_cudat_parity [--julia PATH] [--require-emitted])"
  let (juliaCmd, required) ← match parse args ("julia", false) with
    | .ok o => pure o
    | .error e => do IO.eprintln e; return 2
  let cuda ← cudaLinked
  unless cuda do
    IO.println "No CUDA device is linked: the generated CUDA was not run, only the CPU evaluation."
  let bad := (← runTable table probes cuda) + (← runTable edgeTable edgeProbes cuda)
    + (← runTable overflowTable overflowProbes cuda) + (← runTable flatTable flatProbes cuda)
    + (← runTable cancelTable cancelProbes cuda) + (← runTable zeroTable zeroProbes cuda)
    + (← runTable infTable infProbes cuda) + (← runTable oneTable oneProbes cuda) + (← checkPins)
  let cc ← hasTool "cc"
  let julia := if (← hasTool juliaCmd) then some juliaCmd else none
  unless cc do IO.println "No cc on the path: the emitted C stub helper was not run."
  if julia.isNone then IO.println s!"{juliaCmd} does not run: the emitted Julia helpers were not run."
  if required && !(cc && julia.isSome) then
    IO.eprintln "PARITY FAILED — --require-emitted, and an emitted helper could not be run."
    return 1
  let dir : System.FilePath := "_out/lut-parity"
  IO.FS.createDirAll dir
  let mut bad := bad
  for (tbl, ps) in [(table, probes), (edgeTable, edgeProbes), (overflowTable, overflowProbes),
      (flatTable, flatProbes), (cancelTable, cancelProbes), (zeroTable, zeroProbes),
      (infTable, infProbes), (oneTable, oneProbes)] do
    bad := bad + (← runEmitted dir tbl ps cc julia)
  if bad == 0 then
    IO.println "PARITY OK — the fetch kernel matches refFetch, NaN probes and non-finite samples included."
    return 0
  else
    IO.eprintln s!"PARITY FAILED — {bad} comparison(s) differ from refFetch."
    return 1

end PropertyKindCalculus.Apps.LutCudaTParity

/-- The executable entry point. -/
def main (args : List String) : IO UInt32 := PropertyKindCalculus.Apps.LutCudaTParity.main args

end Blanket
