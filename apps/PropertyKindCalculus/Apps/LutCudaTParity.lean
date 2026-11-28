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
(`--julia PATH` names the Julia). The C stub reads its table from `lutDataDecl`, so baked samples go
through `floatLit`. `runExtrema` runs `fmin`/`fmax` at every NaN, `±0`, `±1`, `±∞` pair: as an emitted
C stub kernel with baked NaN and `±∞` constants, and on `CudaT` when a LibTorch bridge is linked.
`runPower` runs `x ^ y` at the same pairs and at ordinary operands against C `pow`'s written-out rules,
within 4 ulps: `evalTape`, the emitted C stub, the emitted Julia at both precisions, and `CudaT`.
Exits `0` on parity and `1` on mismatch.
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
      , TapeCodegen.lutDataDecl tbl, arr "lBits" ls, arr "uBits" us
      , "int main(void) {"
      , s!"  for (int i = 0; i < {ps.size}; i++) \{"
      , "    float l, u; memcpy(&l, &lBits[i], 4); memcpy(&u, &uBits[i], 4);"
      , s!"    float r = tl_lutfetch(lut_{tbl.name}_data, {tbl.width}, {tbl.layers}, l, u);"
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

/-- NaN, `±0`, `±1` and `±∞`: the operands of the extrema probes, taken in every ordered pair. -/
def specials : Array Float := #[nan, 0.0, -0.0, 1.0, -1.0, inf, -inf]

/-- `fmin` and `fmax` on two inputs, then against baked NaN and `±∞` constants: six outputs. -/
def recordExtrema : Except String (CpuTape Float × List Nat) := do
  let leaf (nm : String) : TapeBuilder Shape.scalar :=
    ⟨TapeM.leaf (Tensor.full Shape.scalar 0.0) (name := some nm)⟩
  let x := leaf "x"
  let y := leaf "y"
  let outs : List (TapeBuilder Shape.scalar) :=
    [.fmin x y, .fmax x y, .fmax (.const nan) x, .fmin x (.const nan), .fmin (.const inf) x,
     .fmax (.const (-inf)) x]
  let (ids, t) ← TapeM.run (TorchLean.Tape.empty : CpuTape Float) (outs.mapM (·.run))
  pure (t, ids)

/-- IEEE 754-2019 `minimumNumber` written out, independent of the tape and of `Context.fmin`. -/
def fminRef (a b : Float) : Float :=
  if b.isNaN then a else if a.isNaN then b
  else if a < b || (a == b && a.toBits >>> 63 == 1) then a else b

/-- IEEE 754-2019 `maximumNumber` written out, independent of the tape and of `Context.fmax`. -/
def fmaxRef (a b : Float) : Float :=
  if b.isNaN then a else if a.isNaN then b
  else if a > b || (a == b && a.toBits >>> 63 == 0) then a else b

/-- What `recordExtrema`'s six outputs must be at `(x, y)`, stated without the tape. -/
def extremaWant (x y : Float) : List Float :=
  [fminRef x y, fmaxRef x y, x, x, if x.isNaN then inf else x, if x.isNaN then -inf else x]

/-- Run `recordExtrema` as the emitted C stub kernel (`cc`), and `fmin`/`fmax` on `CudaT` buffers
when a LibTorch bridge is linked; each, and `evalTape`, against `extremaWant`. The number of mismatches. -/
def runExtrema (dir : System.FilePath) (cc : Bool) : IO Nat := do
  let (t, ids) ← IO.ofExcept recordExtrema
  let pairs := specials.flatMap fun a => specials.map fun b => (a, b)
  let want := pairs.map fun (a, b) => extremaWant a b
  let report (label : String) (p j : Nat) (out : Float) : IO Nat := do
    let ok := same out ((want[p]!).getD j 0.0)
    let (a, b) := pairs[p]!
    unless ok do IO.println s!"FAIL {label} output {j} x={a} y={b}  got={out}  expected={(want[p]!).getD j 0.0}"
    return if ok then 0 else 1
  let mut bad := 0
  for p in [0:pairs.size] do
    let (a, b) := pairs[p]!
    let vals ← IO.ofExcept (TapeCodegen.evalTape (fun nm => if nm == "x" then a else b) t)
    for (id, j) in ids.zipIdx do
      bad := bad + (← report "evalTape" p j (vals.getD id 0.0))
  if cc then
    let cg ← IO.ofExcept (TapeCodegen.gen t ids)
    let arr (nm : String) (xs : Array Float) :=
      s!"static const uint32_t {nm}Bits[] = \{" ++ String.intercalate ", " (xs.toList.map ("0x" ++ f32Hex ·)) ++ "};"
    let n := pairs.size
    let src := String.intercalate "\n"
      [ "#include <math.h>", "#include <stdint.h>", "#include <stdio.h>", "#include <string.h>"
      , TapeCodegen.emitStub "extrema" cg
      , arr "x" (pairs.map (·.1)), arr "y" (pairs.map (·.2))
      , "int main(void) {"
      , s!"  float x[{n}], y[{n}], out[{ids.length * n}];"
      , "  memcpy(x, xBits, sizeof x); memcpy(y, yBits, sizeof y);"
      , s!"  extrema_stub({n}, {String.intercalate ", " cg.inputs.toList}, out);"
      , s!"  for (int i = 0; i < {ids.length * n}; i++) \{ uint32_t b; memcpy(&b, &out[i], 4); printf(\"%08x\\n\", b); }"
      , "  return 0;", "}", "" ]
    let cFile := dir / "extrema.c"
    let exe := dir / "extrema.out"
    IO.FS.writeFile cFile src
    let build ← IO.Process.output
      { cmd := "cc", args := #["-O2", "-ffp-contract=off", "-o", exe.toString, cFile.toString, "-lm"] }
    let res ← if build.exitCode != 0 then pure build else IO.Process.output { cmd := exe.toString }
    let words := (res.stdout.splitOn "\n").filter (· ≠ "") |>.toArray
    if res.exitCode != 0 || words.size != ids.length * n then
      IO.eprintln s!"C stub extrema: cc or the kernel failed ({words.size} results):\n{res.stderr}"
      bad := bad + 1
    else
      for j in [0:ids.length] do
        for p in [0:n] do
          bad := bad + (← report "C stub" p j ((ofHex8? words[j * n + p]!).getD 0.0))
    IO.println s!"extrema C stub: {ids.length * n} outputs compared with the stated expectations."
  if (← TorchLean.LibTorch.Buffer.RuntimeStatus.query) matches .nativeAvailable then
    let s : Shape := [pairs.size]
    let a : CudaCarrier.CudaT s := .ofFloatArray ⟨pairs.map (·.1)⟩
    let b : CudaCarrier.CudaT s := .ofFloatArray ⟨pairs.map (·.2)⟩
    for (j, got) in [(0, (CudaCarrier.CudaT.fmin a b).toFloatArray), (1, (CudaCarrier.CudaT.fmax a b).toFloatArray)] do
      for p in [0:pairs.size] do
        bad := bad + (← report "CudaT " p j (got.get! p))
    IO.println s!"extrema CudaT: {2 * pairs.size} outputs compared with the stated expectations."
  else
    IO.println "No LibTorch bridge is linked: CudaT fmin/fmax were not run."
  return bad

/-- Whether a finite `y` is an odd integer. -/
def isOddInt (y : Float) : Bool := y.isFinite && y.floor == y && (y / 2).floor != y / 2

/-- C `pow` (ISO C Annex F.10.4.4) where the standard fixes the result, written out without the tape
or `Float.pow`; `none` on finite operands whose result is a rounded real power. -/
def powRef (x y : Float) : Option Float :=
  if y == 0.0 || x == 1.0 then some 1.0
  else if x.isNaN || y.isNaN then some nan
  else if y == inf then some (if x.abs == 1.0 then 1.0 else if x.abs < 1.0 then 0.0 else inf)
  else if y == -inf then some (if x.abs == 1.0 then 1.0 else if x.abs < 1.0 then inf else 0.0)
  else if x == inf then some (if y < 0.0 then 0.0 else inf)
  else if x == -inf then
    some (if isOddInt y then (if y < 0.0 then -0.0 else -inf) else (if y < 0.0 then 0.0 else inf))
  else if x == 0.0 then
    let neg := x.toBits >>> 63 == 1 && isOddInt y
    some (if y < 0.0 then (if neg then -inf else inf) else (if neg then -0.0 else 0.0))
  else if x < 0.0 && y.floor != y then some nan
  else if y == 1.0 then some x
  else if y == -1.0 then some (1.0 / x)
  else none

/-- Ordinary operands `(x, y, x ^ y)`, each exact in binary32, the power stated by hand
(`Float.sqrt` is correctly rounded). -/
def powOrdinary : Array (Float × Float × Float) :=
  #[(2.0, 3.0, 8.0), (2.0, 0.5, Float.sqrt 2.0), (4.0, -0.5, 0.5), (-2.0, 3.0, -8.0), (-2.0, 2.0, 4.0),
    (-2.0, 0.5, nan), (9.0, 0.5, 3.0), (10.0, -2.0, 0.01), (0.5, -1.5, Float.sqrt 8.0),
    (1.5, 2.0, 2.25), (-0.5, -3.0, -8.0), (0.25, 0.5, 0.5), (-8.0, 0.25, nan), (3.0, 4.0, 81.0),
    (2.0, 10.0, 1024.0), (0.5, 2.0, 0.25), (-1.5, -2.5, nan),
    -- finite operands whose power underflows or overflows: the sign is the odd-integer rule's
    (-0.0625, 513.0, -0.0), (-0.0625, 512.0, 0.0), (-0.0625, -513.0, -inf), (-16.0, 513.0, -inf),
    (-16.0, -513.0, -0.0), (0.0625, 513.0, 0.0)]

/-- The power probes `(x, y, x ^ y)`: every ordered pair of `specials` by `powRef`, then `powOrdinary`. -/
def powProbes : Except String (Array (Float × Float × Float)) := do
  let sp ← (specials.flatMap fun a => specials.map fun b => (a, b)).mapM fun (a, b) =>
    match powRef a b with
    | some w => pure (a, b, w)
    | none => throw s!"powRef leaves pow({a}, {b}) unstated"
  pure (sp ++ powOrdinary)

/-- `x ^ y` on two inputs, then with baked NaN and `±∞` constants as base or exponent: four outputs. -/
def recordPower : Except String (CpuTape Float × List Nat) := do
  let leaf (nm : String) : TapeBuilder Shape.scalar :=
    ⟨TapeM.leaf (Tensor.full Shape.scalar 0.0) (name := some nm)⟩
  let x := leaf "x"
  let y := leaf "y"
  let outs : List (TapeBuilder Shape.scalar) :=
    [x ^ y, (.const nan : TapeBuilder Shape.scalar) ^ x, x ^ (.const inf : TapeBuilder Shape.scalar),
     (.const (-inf) : TapeBuilder Shape.scalar) ^ x]
  let (ids, t) ← TapeM.run (TorchLean.Tape.empty : CpuTape Float) (outs.mapM (·.run))
  pure (t, ids)

/-- What `recordPower`'s four outputs must be at a probe, stated without the tape. -/
def powerWant (p : Float × Float × Float) : Except String (List Float) := do
  let ref (a b : Float) : Except String Float :=
    match powRef a b with
    | some w => pure w
    | none => throw s!"powRef leaves pow({a}, {b}) unstated"
  pure [p.2.2, ← ref nan p.1, ← ref p.1 inf, ← ref (-inf) p.1]

/-- The parity rule of a libm call: NaN, zeros and infinities exactly (sign included), any other
value within `tol` units in the last place of the lane's format (`f32`: binary32). -/
def ulpNear (f32 : Bool) (got want : Float) (tol : Nat := 4) : Bool :=
  let (g, w) := if f32 then (got.toFloat32.toFloat, want.toFloat32.toFloat) else (got, want)
  let bits (v : Float) : Nat := if f32 then v.toFloat32.toBits.toNat else v.toBits.toNat
  if w.isNaN || g.isNaN then w.isNaN && g.isNaN
  else if !w.isFinite || w == 0.0 || !g.isFinite || g == 0.0 then bits g == bits w
  else (g < 0.0) == (w < 0.0) && (if bits g ≥ bits w then bits g - bits w else bits w - bits g) ≤ tol

def ofHex16? (s : String) : Option Float :=
  if s.length != 16 then none else
  (s.toList.foldlM (fun n c => (hexDigit? c).map (n * 16 + ·)) 0).map fun n => Float.ofBits n.toUInt64

/-- Run `recordPower` through `evalTape`, the emitted C stub (`cc`), the emitted Julia function at
`Float32` and `Float64`, and `^` on `CudaT` buffers when a LibTorch bridge is linked; each against
`powerWant` under `ulpNear`. The number of mismatches. -/
def runPower (dir : System.FilePath) (cc : Bool) (julia : Option String) : IO Nat := do
  let (t, ids) ← IO.ofExcept recordPower
  let probes ← IO.ofExcept powProbes
  let want ← IO.ofExcept (probes.mapM powerWant)
  let n := probes.size
  let k := ids.length
  let report (label : String) (f32 : Bool) (p j : Nat) (out : Float) : IO Nat := do
    let w := (want[p]!).getD j 0.0
    let ok := ulpNear f32 out w
    let (a, b, _) := probes[p]!
    unless ok do IO.println s!"FAIL {label} power output {j} x={a} y={b}  got={out}  expected={w}"
    return if ok then 0 else 1
  let mut bad := 0
  for p in [0:n] do
    let (a, b, _) := probes[p]!
    let vals ← IO.ofExcept (TapeCodegen.evalTape (fun nm => if nm == "x" then a else b) t)
    for (id, j) in ids.zipIdx do
      bad := bad + (← report "evalTape" false p j (vals.getD id 0.0))
  if cc then
    let cg ← IO.ofExcept (TapeCodegen.gen t ids)
    let arr (nm : String) (xs : Array Float) :=
      s!"static const uint32_t {nm}Bits[] = \{" ++ String.intercalate ", " (xs.toList.map ("0x" ++ f32Hex ·)) ++ "};"
    let src := String.intercalate "\n"
      [ "#include <math.h>", "#include <stdint.h>", "#include <stdio.h>", "#include <string.h>"
      , TapeCodegen.emitStub "power" cg
      , arr "x" (probes.map (·.1)), arr "y" (probes.map (·.2.1))
      , "int main(void) {"
      , s!"  float x[{n}], y[{n}], out[{k * n}];"
      , "  memcpy(x, xBits, sizeof x); memcpy(y, yBits, sizeof y);"
      , s!"  power_stub({n}, {String.intercalate ", " cg.inputs.toList}, out);"
      , s!"  for (int i = 0; i < {k * n}; i++) \{ uint32_t b; memcpy(&b, &out[i], 4); printf(\"%08x\\n\", b); }"
      , "  return 0;", "}", "" ]
    let cFile := dir / "power.c"
    let exe := dir / "power.out"
    IO.FS.writeFile cFile src
    let build ← IO.Process.output
      { cmd := "cc", args := #["-O2", "-ffp-contract=off", "-o", exe.toString, cFile.toString, "-lm"] }
    let res ← if build.exitCode != 0 then pure build else IO.Process.output { cmd := exe.toString }
    let words := (res.stdout.splitOn "\n").filter (· ≠ "") |>.toArray
    if res.exitCode != 0 || words.size != k * n then
      IO.eprintln s!"C stub power: cc or the kernel failed ({words.size} results):\n{res.stderr}"
      bad := bad + 1
    else
      for j in [0:k] do
        for p in [0:n] do
          match ofHex8? words[j * n + p]! with
          | some v => bad := bad + (← report "C stub" true p j v)
          | none => IO.eprintln s!"C stub power: unreadable result {words[j * n + p]!}"; bad := bad + 1
      IO.println s!"power C stub: {k * n} outputs compared with the stated expectations."
  if let some julia := julia then
    let cg ← IO.ofExcept (TapeCodegen.Julia.genJulia t ids)
    let vec (nm : String) (xs : Array Float) :=
      s!"{nm} = reinterpret(Float32, UInt32[" ++ String.intercalate ", " (xs.toList.map ("0x" ++ f32Hex ·)) ++ "])"
    let args := String.intercalate ", " (cg.inputs.toList.map fun nm => s!"T.({nm})")
    let src := String.intercalate "\n"
      [ TapeCodegen.Julia.emitJulia "power" cg
      , vec "x" (probes.map (·.1)), vec "y" (probes.map (·.2.1))
      , "for T in (Float32, Float64)"
      , s!"    out = Matrix\{T}(undef, {n}, {k})"
      , s!"    power!(out, {args})"
      , s!"    for p in 1:{n}, j in 1:{k}"
      , "        println(string(reinterpret(UInt64, Float64(out[p, j])); base = 16, pad = 16))"
      , "    end"
      , "end", "" ]
    let jlFile := dir / "power.jl"
    IO.FS.writeFile jlFile src
    let res ← IO.Process.output { cmd := julia, args := #["--startup-file=no", jlFile.toString] }
    let words := (res.stdout.splitOn "\n").filter (· ≠ "") |>.toArray
    if res.exitCode != 0 || words.size != 2 * k * n then
      IO.eprintln s!"Julia power: the kernel failed ({words.size} results):\n{res.stderr}"
      bad := bad + 1
    else
      for (label, f32, base) in [("jl F32", true, 0), ("jl F64", false, k * n)] do
        for p in [0:n] do
          for j in [0:k] do
            match ofHex16? words[base + p * k + j]! with
            | some v => bad := bad + (← report label f32 p j v)
            | none => IO.eprintln s!"Julia power: unreadable result {words[base + p * k + j]!}"; bad := bad + 1
      IO.println s!"power Julia: {2 * k * n} outputs compared with the stated expectations."
  if (← TorchLean.LibTorch.Buffer.RuntimeStatus.query) matches .nativeAvailable then
    let s : Shape := [n]
    let a : CudaCarrier.CudaT s := .ofFloatArray ⟨probes.map (·.1)⟩
    let b : CudaCarrier.CudaT s := .ofFloatArray ⟨probes.map (·.2.1)⟩
    let got := (a ^ b).toFloatArray
    for p in [0:n] do
      bad := bad + (← report "CudaT " true p 0 (got.get! p))
    IO.println s!"power CudaT: {n} outputs compared with the stated expectations."
  else
    IO.println "No LibTorch bridge is linked: CudaT power was not run."
  return bad

/-- `--julia PATH` names the Julia to run (default `julia` on the path); `--require-emitted` makes a
missing `cc` or Julia a failure instead of a skip. -/
def main (args : List String) : IO UInt32 := do
  let rec parse : List String → String × Bool → Except String (String × Bool)
    | [], o => .ok o
    | "--julia" :: p :: rest, (_, req) =>
      if p.isEmpty || p == "--julia" || p == "--require-emitted" then .error s!"--julia needs a path, got '{p}'"
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
  bad := bad + (← runExtrema dir cc)
  bad := bad + (← runPower dir cc julia)
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
