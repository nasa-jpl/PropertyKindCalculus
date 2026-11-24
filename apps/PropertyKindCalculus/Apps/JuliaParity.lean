/-
`apps.julia_parity` — **the emitted Julia kernel against `evalTape`, bit for bit.**

`paradigm.tape_codegen_julia` renders a recorded tape as a Julia function; the rendering-table
theorems say it renders the whole alphabet, and `examples.tape_codegen_julia_demo` `#guard`s the
coverage and the ABI on the concrete tapes. What no `#guard` can do is run Julia. This executable
does: for each recorded case it writes the emitted `.jl`, a driver and a file of input pixels,
runs `julia` at `Float64`, and compares every output of every pixel with `evalTape` on the same
tape and the same inputs.

The verdict is two-tiered, by the cone of each output (`transCone`):

  * an output whose backward cone contains no `exp`/`log` node must be **bit-identical** — the raw
    bit patterns compared, so a `-0.0`/`+0.0` or a NaN-payload difference fails — because
    `+ − × ÷ √ |·| min max` and the table fetch are IEEE-exact and `Float64` is Lean's `Float`, so
    any difference is a rendering bug, not a libm;
  * an output whose cone reaches `exp`/`log` is compared in **ulps** (`--max-ulp`, default 4):
    Julia's `exp`/`log` are pure-Julia `Base.Math`, Lean's are glibc's; the two are correctly
    rounded or nearly so, and the gap is the one the C stub / CUDA pair already carries.

Exit codes: `0` every comparison within its tier; `1` a parity failure (reported per output);
`2` cannot run — `julia` not found (`--allow-missing-julia` turns that into `0` with a
"skipped" line, for a CI lane that has no Julia), or a recording/codegen failure.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCodegenJulia
public import PropertyKindCalculus.Examples.TapeCodegenDemo
public import PropertyKindCalculus.Examples.LmStepCodegenDemo
public import PropertyKindCalculus.Examples.TapeCodegenLut

@[expose] public section Blanket

open PropertyKindCalculus.Paradigm (TapeM CpuTape CpuNode)
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Paradigm.TapeCodegen.Julia
open PropertyKindCalculus.Paradigm (LutTable LutInterp)
open PropertyKindCalculus.Examples (TapeCodegenLut.inLeafV TapeCodegenLut.TB TapeCodegenLut.demoLut)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)

namespace PropertyKindCalculus.Apps.JuliaParity

/-! ### Options -/

structure Opts where
  outDir : String := "_out/julia-parity"
  julia : Option String := none
  pixels : Nat := 64
  maxUlp : Nat := 4
  allowMissing : Bool := false
  ka : Bool := false
  kaRtol : Float := 1e-9
  kaRtolText : String := "1e-9"
  deriving Repr

def usage : String := String.intercalate "\n"
  [ "julia_parity — run the Julia kernels paradigm.tape_codegen_julia emits against evalTape."
  , ""
  , "usage: lake exe julia_parity [options]"
  , ""
  , "  -o, --out-dir DIR          where the .jl files, inputs and outputs go (default _out/julia-parity)"
  , "  -j, --julia PATH           the julia executable (default: $JULIA, else `julia` on PATH)"
  , "  -n, --pixels N             input pixels per case, deterministic (default 64)"
  , "  -u, --max-ulp N            tolerance for outputs whose cone reaches exp/log (default 4)"
  , "  -a, --allow-missing-julia  exit 0 with a `skipped` line when julia is not found (default: exit 2)"
  , "  -k, --ka                   also run the KernelAbstractions.jl twin on the CPU backend (needs the package);"
  , "                             tolerance-only — a backend may contract a*b+c to an FMA, so every output is"
  , "                             compared by relative error (the ulp figure is reported, not gated)"
  , "  -r, --ka-rtol X            relative tolerance for the KernelAbstractions twin (default 1e-9)"
  , "  -V, --version              print the Lean toolchain this was built with"
  , "  -h, --help                 this text"
  , ""
  , "Cases: avs_resjac (Examples.TapeCodegenDemo), lm_step (Examples.LmStepCodegenDemo),"
  , "       lut_model (Examples.TapeCodegenLut: a lutfetch + arithmetic tape, against evalTapeT)."
  , "Verdict: bit-identical on outputs with no exp/log in their cone; within --max-ulp otherwise;"
  , "the KernelAbstractions twin (--ka) within --ka-rtol relative error on every output." ]

/-- A decimal or scientific literal (`1e-9`, `0.5`, `2`) as a `Float`. -/
def parseFloat? (x : String) : Option Float :=
  let (mant, ex) := match x.splitOn "e" with
    | [m, e] => (m, e.toInt?)
    | [m] => (m, some 0)
    | _ => (x, none)
  match ex with
  | none => none
  | some e =>
    let (ip, fp) := match mant.splitOn "." with
      | [i, f] => (i, f)
      | [i] => (i, "")
      | _ => ("x", "")
    let neg := ip.startsWith "-"
    let ip := if neg then (ip.drop 1).toString else ip
    match (ip ++ fp).toNat? with
    | none => none
    | some digits =>
      let scale : Int := e - fp.length
      let v := Float.ofNat digits
      let p := Float.ofNat (10 ^ scale.natAbs)
      let r := if scale ≥ 0 then v * p else v / p
      some (if neg then -r else r)

partial def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | ("-o" :: d :: rest), o | ("--out-dir" :: d :: rest), o => parseArgs rest { o with outDir := d }
  | ("-j" :: j :: rest), o | ("--julia" :: j :: rest), o => parseArgs rest { o with julia := some j }
  | ("-n" :: n :: rest), o | ("--pixels" :: n :: rest), o =>
      match n.toNat? with
      | some k => if k == 0 then .error "--pixels must be positive" else parseArgs rest { o with pixels := k }
      | none => .error s!"--pixels: not a number: {n}"
  | ("-u" :: n :: rest), o | ("--max-ulp" :: n :: rest), o =>
      match n.toNat? with
      | some k => parseArgs rest { o with maxUlp := k }
      | none => .error s!"--max-ulp: not a number: {n}"
  | ("-a" :: rest), o | ("--allow-missing-julia" :: rest), o => parseArgs rest { o with allowMissing := true }
  | ("-k" :: rest), o | ("--ka" :: rest), o => parseArgs rest { o with ka := true }
  | ("-r" :: x :: rest), o | ("--ka-rtol" :: x :: rest), o =>
      match parseFloat? x with
      | some r => parseArgs rest { o with kaRtol := r, kaRtolText := x }
      | none => .error s!"--ka-rtol: not a number: {x}"
  | (a :: _), _ => .error s!"unknown argument `{a}` (try --help)"

/-! ### Bits in and out -/

def hexOfBits (b : UInt64) : String :=
  let n := b.toNat
  String.ofList <| (List.range 16).map fun i => Nat.digitChar ((n / 2 ^ (60 - 4 * i)) % 16)

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def bitsOfHex? (s : String) : Option UInt64 :=
  s.toList.foldlM (init := (0 : Nat)) (fun acc c => (hexDigit? c).map (acc * 16 + ·)) |>.map UInt64.ofNat

/-- ulp distance between two finite doubles of the same sign, for the **tolerant** tiers; `none`
when they are not comparable that way (sign differs, or one is NaN/Inf and the other is not). Both
NaN, or `±0.0` against `∓0.0`, count as distance 0 — numerically equivalent, so acceptable under a
tolerance; the exact tier never consults this, it compares the raw bits. -/
def ulpDist (x y : Float) : Option Nat :=
  if x.isNaN && y.isNaN then some 0
  else if x.isNaN || y.isNaN then none
  else if !x.isFinite || !y.isFinite then (if x == y then some 0 else none)
  else
    let bx := x.toBits.toNat
    let byy := y.toBits.toNat
    let sx := bx / 2 ^ 63
    let sy := byy / 2 ^ 63
    if sx != sy then (if x == 0.0 && y == 0.0 then some 0 else none)
    else some (if bx ≥ byy then bx - byy else byy - bx)

/-! ### The cone classification -/

/-- `transCone t` marks each node whose backward cone contains an `exp` or `log` node (parents
precede children in a tape, so one forward pass suffices). -/
def transCone (t : CpuTape Float) : Array Bool := Id.run do
  let mut marks : Array Bool := Array.mkEmpty t.nodes.size
  for n in t.nodes do
    let own := n.name == some "exp" || n.name == some "log"
    let inherited := n.parents.any (fun p => marks.getD p false)
    marks := marks.push (own || inherited)
  return marks

/-! ### Deterministic pixels -/

/-- A tiny LCG, so the inputs are the same on every run and every machine. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Pixel `k`'s environment: the demo's centre pixel, each input perturbed by a deterministic
δ ∈ [−0.1, 0.1] (relative when the centre is non-zero, absolute when it is zero). -/
def pixelEnv (centre : String → Float) (inputs : Array String) (k : Nat) : String → Float :=
  fun nm =>
    match inputs.idxOf? nm with
    | none => centre nm
    | some i =>
      let s := lcg (lcg (k * 7919 + i * 104729 + 17))
      let δ : Float := (Float.ofNat (s % 1000000)).div 1000000.0 * 0.2 - 0.1
      let c := centre nm
      if c == 0.0 then δ else c * (1.0 + δ)

/-! ### One case -/

structure Case where
  name : String
  record : Except String (CpuTape Float × List Nat)
  centre : String → Float
  /-- The lookup tables the tape's `lutfetch` nodes name (empty for pure-arithmetic tapes). -/
  tables : Array LutTable := #[]
  /-- Fixed pixels run instead of the perturbed centre (`--pixels` then does not apply). -/
  pixels : Option (List (String → Float)) := none

/-- `Examples.TapeCodegenLut`'s mixed fetch + arithmetic model, compacted — the case that exercises
`tl_lutfetch` and the table-extended interpreter `evalTapeT`. -/
def recordLut : Except String (CpuTape Float × List Nat) := do
  let (t, id) ← PropertyKindCalculus.Examples.TapeCodegenLut.lutRecord
  let (t', remap) := cseCompact t
  pure (t', [remap.getD id id])

/-- `min`, `max`, the clamp `max lo (min hi x)` and a table fetch, as four outputs: the ops whose
NaN and signed-zero results the renderings must reproduce. -/
def recordSpecial : Except String (CpuTape Float × List Nat) := do
  let x := TapeCodegenLut.inLeafV "x" 1.0
  let y := TapeCodegenLut.inLeafV "y" 2.0
  let fetch : TapeCodegenLut.TB := LutInterp.lutFetch TapeCodegenLut.demoLut x y
  let outs : List TapeCodegenLut.TB :=
    [Min.min x y, Max.max x y, Max.max (0 : TapeCodegenLut.TB) (Min.min (1 : TapeCodegenLut.TB) x), fetch]
  let (ids, t) ← TapeM.run (TorchLean.Tape.empty : CpuTape Float) (outs.mapM (·.run))
  pure (t, ids)

/-- Every ordered pair over NaN, `±0`, `±1` and `±∞`, as `(x, y)`. -/
def specialPixels : List (String → Float) :=
  let vs : List Float := [0.0 / 0.0, 0.0, -0.0, 1.0, -1.0, 1.0 / 0.0, -1.0 / 0.0]
  vs.flatMap fun a => vs.map fun b => fun nm => if nm == "x" then a else b

def cases : List Case :=
  [ { name := "avs_resjac", record := PropertyKindCalculus.Paradigm.TapeCodegen.Demo.recordResJac
    , centre := PropertyKindCalculus.Paradigm.TapeCodegen.Demo.env0 }
  , { name := "lm_step", record := PropertyKindCalculus.Examples.LmStepCodegenDemo.recordStep
    , centre := PropertyKindCalculus.Examples.LmStepCodegenDemo.env0 }
  , { name := "lut_model", record := recordLut
    , centre := PropertyKindCalculus.Examples.TapeCodegenLut.recordEnv
    , tables := #[PropertyKindCalculus.Examples.TapeCodegenLut.demoLut] }
  , { name := "nan_signed_zero", record := recordSpecial, centre := fun _ => 0.0
    , tables := #[PropertyKindCalculus.Examples.TapeCodegenLut.demoLut], pixels := some specialPixels } ]

/-- The tables of a case, keyed by name — `evalTapeT`'s table resolver. -/
def tableLookup (c : Case) : String → Option LutTable := fun tn => c.tables.find? (·.name == tn)

/-- Julia self-check of a table case: the `Float32` method of `tl_lutfetch` (integers, no `Float64`)
against the generic `Float64` method on the same `Float32` inputs, bit for bit. -/
def softFetchCheck : String := String.intercalate "\n"
  [ "let"
  , "    ref(tab, W, L, l, u) = invoke(tl_lutfetch, Tuple{AbstractVector{T},Int,Int,T,T} where {T<:AbstractFloat}, tab, W, L, l, u)"
  , "    same(x, y) = (isnan(x) && isnan(y)) || reinterpret(UInt32, x) == reinterpret(UInt32, y)"
  , "    sp = Float32[0, -0.0, 0.5, 1, 1.5, 2.375, 3, 4.25, 4.5, 5.859375, 7, 8.5, 9, 11, Inf32, -Inf32, NaN32, 1f-40, -1, 0.99999994f0, 0.49999997f0]"
  , "    tab = Float32[8388608, -8388607, 4194299, -6990499, 2f0^127, -2f0^127, floatmax(Float32), 199.900009f0, 199.900009f0, Inf32, -1, 1f-45,"
  , "                  -0.0, -1, -0.0, 1, NaN32, 2, -Inf32, 3f-39, -3.4f38, 3.3f38, 16777215, 0.1f0]"
  , "    seed = 0x2545f4914f6cdd1d"
  , "    bad = 0"
  , "    for t in 1:200000"
  , "        seed = seed * 0x5851f42d4c957f2d + 0x14057b7ef767814f"
  , "        r1 = (seed >> 40) % UInt32"
  , "        seed = seed * 0x5851f42d4c957f2d + 0x14057b7ef767814f"
  , "        r2 = (seed >> 40) % UInt32"
  , "        l = r1 % 8 == 0 ? sp[1 + r2 % length(sp)] : Float32(r1) / 2f0^24 * 3 - 1"
  , "        u = r2 % 8 == 1 ? sp[1 + r1 % length(sp)] : Float32(r2) / 2f0^24 * 14 - 1"
  , "        same(tl_lutfetch(tab, 12, 2, l, u), ref(tab, 12, 2, l, u)) || (bad += 1)"
  , "    end"
  , "    lerp(a, b, f) = Float32(Float64(a) + Float64(f) * (Float64(b) - Float64(a)))"
  , "    for t in 1:2000000"
  , "        seed = seed * 0x5851f42d4c957f2d + 0x14057b7ef767814f"
  , "        r1 = (seed >> 32) % UInt32"
  , "        seed = seed * 0x5851f42d4c957f2d + 0x14057b7ef767814f"
  , "        r2 = (seed >> 32) % UInt32"
  , "        seed = seed * 0x5851f42d4c957f2d + 0x14057b7ef767814f"
  , "        r3 = (seed >> 32) % UInt32"
  , "        a = reinterpret(Float32, r1)"
  , "        m = t % 4"
  , "        b = m == 0 ? reinterpret(Float32, r2) :"
  , "            m == 1 ? reinterpret(Float32, r1 ⊻ 0x80000000 ⊻ (r2 & 0x000000ff)) :"
  , "            m == 2 ? reinterpret(Float32, r1 ⊻ (r2 & 0x0000ffff)) : reinterpret(Float32, r1 ⊻ 0x80000000 ⊻ (r2 & 0x00ffffff))"
  , "        f = t % 3 == 0 ? reinterpret(Float32, r3 % 0x3f800000) : t % 3 == 1 ? reinterpret(Float32, r3 % 0x01000000) : Float32(r3 >> 8) / 2f0^24"
  , "        (isfinite(a) && isfinite(b)) || continue"
  , "        same(tl_lerp64(a, b, f), lerp(a, b, f)) || (bad += 1)"
  , "    end"
  , "    ev = Float32[0, -0.0, 1, -1, floatmax(Float32), -floatmax(Float32), floatmin(Float32), -floatmin(Float32), 1f-45, -1f-45,"
  , "                 2f0^127, -2f0^127, 8388608, -8388607, 4194299, -6990499, 199.900009f0, 1f-30, -1f-30, 1.2345678f-33, 3f-45,"
  , "                 16777216, 16777215, 16777218, -16777218, 1.0000001f0, 0.1f0, 3.3333334f-39, -7.7777f-36]"
  , "    ef = Float32[0, 0.5, 0.25, 0.75, 0.375, 0.99999994f0, 1f-45, 0.859375f0, 1f-30, 3f-41, 7.3f-40, 1.1754942f-38, 0.1f0, 5.4321f-39]"
  , "    for a in ev, b in ev, f in ef"
  , "        same(tl_lerp64(a, b, f), lerp(a, b, f)) || (bad += 1)"
  , "    end"
  , "    bad == 0 || error(\"tl_lutfetch: the Float32 method differs from the Float64 method on $bad probes\")"
  , "end" ]

/-- The Julia driver: reads the inputs file (names, then one hex row per pixel), runs the kernel at
`Float64`, prints one hex row per pixel. -/
def driver (name : String) (nOut : Nat) (tables : Array LutTable) (ka : Bool := false) : String :=
  let lutDefs := tables.toList.map fun tb =>
    s!"lut_{tb.name} = Float64[" ++ String.intercalate ", "
      (tb.values.toList.map (fun v => s!"reinterpret(Float64, 0x{hexOfBits v.toBits})")) ++ "]"
  let lutArgs := String.join (tables.toList.map (fun tb => s!", lut_{tb.name}"))
  String.intercalate "\n" <|
  [ (if ka then "using KernelAbstractions\n" else "") ++ s!"include(joinpath(@__DIR__, \"{name}{if ka then "_ka" else ""}.jl\"))"
  , "lines = readlines(ARGS[1])"
  , "names = split(lines[1])"
  , "P = length(lines) - 1"
  , "ins = [Vector{Float64}(undef, P) for _ in names]"
  , "for (k, ln) in enumerate(lines[2:end])"
  , "    for (i, tok) in enumerate(split(ln))"
  , "        ins[i][k] = reinterpret(Float64, parse(UInt64, tok; base = 16))"
  , "    end"
  , "end"
  , s!"out = Matrix\{Float64}(undef, P, {nOut})"
  ] ++ lutDefs ++ (if tables.isEmpty || ka then [] else [softFetchCheck]) ++
  [ (if ka then s!"{name}_kernel!(CPU())(out, ins...{lutArgs}; ndrange = P); KernelAbstractions.synchronize(CPU())"
     else s!"{name}!(out, ins...{lutArgs})")
  , "for p in 1:P"
  , s!"    println(join([string(reinterpret(UInt64, out[p, j]); base = 16, pad = 16) for j in 1:{nOut}], \" \"))"
  , "end"
  , "" ]

structure Verdict where
  compared : Nat := 0
  exactFailures : Nat := 0
  ulpFailures : Nat := 0
  maxUlpSeen : Nat := 0
  notes : Array String := #[]

/-- Run one emitted surface (`ka := false` the plain host kernel, bit-exact tier by cone; `ka := true`
the KernelAbstractions twin, ulp tier on every output) and compare with `evalTape`. -/
def compareSurface (o : Opts) (julia : String) (c : Case) (t : CpuTape Float) (outIds : List Nat)
    (cg : JuliaCodegen) (envs : List (String → Float)) (ka : Bool) : IO (Option Verdict) := do
  let dir : System.FilePath := o.outDir
  let surface := if ka then "ka" else "host"
  let drv := if ka then s!"{c.name}_parity_ka.jl" else s!"{c.name}_parity.jl"
  let res ← IO.Process.output
    { cmd := julia
    , args := #["--startup-file=no", (dir / drv).toString, (dir / s!"{c.name}_inputs.txt").toString] }
  if res.exitCode != 0 then
    IO.eprintln s!"[{c.name}/{surface}] julia failed (exit {res.exitCode}):\n{res.stderr}"
    return none
  IO.FS.writeFile (dir / s!"{c.name}_julia_out_{surface}.txt") res.stdout
  let marks := transCone t
  let outLines := (res.stdout.splitOn "\n").filter (· ≠ "")
  if outLines.length != envs.length then
    IO.eprintln s!"[{c.name}] expected {envs.length} output rows, got {outLines.length}"
    return none
  let mut v : Verdict := {}
  for (env, line, k) in (envs.zip outLines).zipIdx.map (fun ((e, l), k) => (e, l, k)) do
    match evalTapeT (tableLookup c) env t with
    | .error e => IO.eprintln s!"[{c.name}] evalTapeT failed at pixel {k}: {e}"; return none
    | .ok vals =>
      let toks := (line.splitOn " ").filter (· ≠ "")
      for (oid, j) in outIds.zipIdx do
        let lean := vals.getD oid 0.0
        let some bits := toks[j]? >>= bitsOfHex? | do
          IO.eprintln s!"[{c.name}] pixel {k} output {j}: unparsable `{toks[j]?.getD ""}`"; return none
        let jl := Float.ofBits bits
        v := { v with compared := v.compared + 1 }
        let trans := marks.getD oid false || ka
        let tier := if ka then "KernelAbstractions" else if trans then "exp/log cone" else "exact cone"
        let detail := s!"lean {hexOfBits lean.toBits} julia {hexOfBits bits}"
        if !trans then
          -- the exact tier: the raw bits, nothing weaker (a `-0.0`/`+0.0` or a NaN-payload
          -- difference is a rendering difference and fails here)
          if lean.toBits != bits then
            let note := s!"pixel {k} out {j} (exact cone): bits differ ({((ulpDist lean jl).map toString).getD "n/a"} ulp)  {detail}"
            v := { v with exactFailures := v.exactFailures + 1, notes := v.notes.push note }
        else
          match ulpDist lean jl with
          | none =>
            let note := s!"pixel {k} out {j} ({tier}): not comparable  {detail}"
            v := { v with ulpFailures := v.ulpFailures + 1, notes := v.notes.push note }
          | some d =>
            v := { v with maxUlpSeen := max v.maxUlpSeen d }
            if ka then
              let rel := if lean == jl then 0.0 else
                (Float.abs (lean - jl)) / (max (Float.abs lean) (Float.abs jl))
              if rel > o.kaRtol then
                let note := s!"pixel {k} out {j} ({tier}): rel {rel} > {o.kaRtolText} ({d} ulp)  {detail}"
                v := { v with ulpFailures := v.ulpFailures + 1, notes := v.notes.push note }
            else if d > o.maxUlp then
              let note := s!"pixel {k} out {j} ({tier}): {d} ulp, limit {o.maxUlp}  {detail}"
              v := { v with ulpFailures := v.ulpFailures + 1, notes := v.notes.push note }
  let nTrans := outIds.filter (fun oid => marks.getD oid false) |>.length
  let tolDesc := if ka then s!"relative tolerance {o.kaRtolText}" else s!"bit-exact outside exp/log cones, {o.maxUlp} ulp inside"
  IO.println s!"[{c.name}/{surface}] ({tolDesc}) nodes {t.nodes.size}, inputs {cg.inputs.size}, outputs {outIds.length} ({nTrans} in an exp/log cone), pixels {envs.length}: compared {v.compared}, exact failures {v.exactFailures}, ulp failures {v.ulpFailures}, max ulp seen {v.maxUlpSeen}"
  for n in v.notes.toList.take 20 do IO.println s!"    {n}"
  return some v

def runCase (o : Opts) (julia : String) (c : Case) : IO (Option Verdict) := do
  match c.record with
  | .error e => IO.eprintln s!"[{c.name}] record failed: {e}"; return none
  | .ok (t, outIds) =>
  match genJulia t outIds c.tables with
  | .error e => IO.eprintln s!"[{c.name}] codegen failed: {e}"; return none
  | .ok cg =>
  let dir : System.FilePath := o.outDir
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / s!"{c.name}.jl") (emitJulia c.name cg)
  IO.FS.writeFile (dir / s!"{c.name}_ka.jl") (emitJuliaKA c.name cg)
  IO.FS.writeFile (dir / s!"{c.name}_parity.jl") (driver c.name cg.numOutputs cg.tables)
  IO.FS.writeFile (dir / s!"{c.name}_parity_ka.jl") (driver c.name cg.numOutputs cg.tables (ka := true))
  let envs := c.pixels.getD ((List.range o.pixels).map (pixelEnv c.centre cg.inputs))
  let rows := envs.map fun env => String.intercalate " " (cg.inputs.toList.map (fun nm => hexOfBits (env nm).toBits))
  IO.FS.writeFile (dir / s!"{c.name}_inputs.txt")
    (String.intercalate "\n" (String.intercalate " " cg.inputs.toList :: rows) ++ "\n")
  let mut total : Verdict := {}
  for ka in (if o.ka then [false, true] else [false]) do
    match ← compareSurface o julia c t outIds cg envs ka with
    | none => return none
    | some v => total := { compared := total.compared + v.compared, exactFailures := total.exactFailures + v.exactFailures
                         , ulpFailures := total.ulpFailures + v.ulpFailures, maxUlpSeen := max total.maxUlpSeen v.maxUlpSeen
                         , notes := total.notes ++ v.notes }
  return some total

def findJulia (o : Opts) : IO (Option String) := do
  let cand ← match o.julia with
    | some j => pure j
    | none => do
      match (← IO.getEnv "JULIA") with
      | some j => pure j
      | none => pure "julia"
  try
    let r ← IO.Process.output { cmd := cand, args := #["--version"] }
    if r.exitCode == 0 then
      IO.println s!"julia: {cand} — {(r.stdout.splitOn "\n").headD ""}"
      return some cand
    else return none
  catch _ => return none

def main (args : List String) : IO UInt32 := do
  if args.contains "-h" || args.contains "--help" then IO.println usage; return 0
  if args.contains "-V" || args.contains "--version" then
    IO.println s!"julia_parity (PropertyKindCalculus apps) — Lean {Lean.versionString}"; return 0
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"julia_parity: {e}"; return 2
  let some julia ← findJulia o | do
    if o.allowMissing then
      IO.println "skipped: julia not found (--allow-missing-julia)"; return 0
    IO.eprintln "CANNOT RUN — julia not found. Install Julia, set $JULIA, or pass --julia PATH; \
--allow-missing-julia makes this a skip."
    return 2
  let mut failed := false
  let mut cannot := false
  for c in cases do
    match ← runCase o julia c with
    | none => cannot := true
    | some v => if v.exactFailures + v.ulpFailures > 0 then failed := true
  if cannot then return 2
  if failed then IO.println "PARITY FAILED"; return 1
  IO.println "PARITY OK"
  return 0

end PropertyKindCalculus.Apps.JuliaParity

def main (args : List String) : IO UInt32 := PropertyKindCalculus.Apps.JuliaParity.main args

end Blanket
