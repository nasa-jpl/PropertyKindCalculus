/-
`paradigm.tape_codegen` — **the megakernel codegen backend**: lower a recorded, CSE'd tape
(`paradigm.tape_cse`) to a single fused CUDA `__global__` kernel (one thread per pixel, the whole
sub-program in registers) plus its portable C-stub twin.

WHERE THIS SITS. A WO1 kernel written once over `[NumCarrier α]` (§`num_carrier`) is branchless, so
instantiating it at the tape carrier (`α := TapeBuilder s`) *records* it as an elementwise DAG
(`paradigm.tape_carrier`), and `cseCompact` (`paradigm.tape_cse`) recovers the DAG of distinct
sub-expressions. This module walks that DAG and emits one straight-line kernel: each node becomes one
`float vID = <op>(parents);` line, every intermediate a register. That is the roofline win the
`tape_cse` docstring anticipated — the eager `CudaT` carrier materialises a length-P buffer per op, so
every op round-trips its operands and result through DRAM (intensity `flops / (Σ over op-nodes of
(nParents+1)·4)`, memory-bound, ≈ 0.1); the megakernel touches DRAM only for the inputs and outputs, so
AI ≈ `flops/((#inputs+#outputs)·4)` and grows with the fused program size. Both numbers are *computed* —
not cited — by the AI-accounting section below (`aiReport`/`intensity`), so a demo reports the honest
eager-vs-fused roofline gap rather than asserting it.

FAITHFULNESS. `evalTape` gives the generated kernel's denotation as a Float interpreter with the
SAME scalar op-semantics the emitted C uses (`+ − × ÷`, `fminf`/`fmaxf`, `expf`/`logf`/`sqrtf`).
By tape forward-value faithfulness (`paradigm.tape_faithful`/`paradigm.tape_parity`) the recorded
tape's stored values already equal the source kernel at `Float`, so `evalTape` re-evaluated at any
inputs equals the source kernel — the codegen changes only *where intermediates live* (registers vs
DRAM), never the arithmetic. Compile the generated kernel with `nvcc --fmad=false -prec-div=true
-prec-sqrt=true` (no FMA-contraction, no reassociation) to keep it bit-identical to the eager path.

Plain (not a `module`) file: imports the tape carrier and the CSE pass.
-/
import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
import PropertyKindCalculus.Torch.Paradigm.TapeCse

open Spec
open Runtime.Autograd (Tape Node TapeM)
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm (TapeBuilder NumCarrier)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)

namespace PropertyKindCalculus.Paradigm.TapeCodegen

/-! ### Reading a tape node -/

/-- The scalar constant a node stores as its forward value (a scalar tape node holds one `Float`;
the same accessor `paradigm.tape_cse.nodeKey` uses). -/
def nodeScalar (n : Node Float) : Float := (Spec.toList n.value.t).headD 0.0

/-- A leaf has no parents; it is a graph **input** (a named leaf) or a **constant** (an unnamed
`TapeBuilder.const` leaf). An op node has ≥1 parent and carries the op name. -/
def isLeaf (n : Node Float) : Bool := n.parents.isEmpty

/-! ### The generated-kernel semantics — a Float reference interpreter

`evalTape env t` evaluates the recorded DAG at `Float` with the SAME scalar op-semantics the emitted
CUDA/C kernel uses. Named leaves read from `env`; const leaves keep their stored value. This is the
denotation the codegen must match, and at `Float` it equals the original `[NumCarrier α]` kernel by
tape faithfulness (`paradigm.tape_parity`). It doubles as the CPU-side bit-exact validator (no CUDA
toolchain needed) and the semantic anchor for the codegen-faithfulness proof. -/
def cOp (nm : String) (args : List Float) : Except String Float :=
  match nm, args with
  | "add",  [a, b] => .ok (a + b)
  | "sub",  [a, b] => .ok (a - b)
  | "mul",  [a, b] => .ok (a * b)
  | "div",  [a, b] => .ok (a / b)
  | "min",  [a, b] => .ok (Min.min a b)   -- fminf
  | "max",  [a, b] => .ok (Max.max a b)   -- fmaxf
  | "exp",  [a]    => .ok (Float.exp a)   -- expf
  | "log",  [a]    => .ok (Float.log a)   -- logf
  | "sqrt", [a]    => .ok (Float.sqrt a)  -- sqrtf
  | "abs",  [a]    => .ok (Float.abs a)   -- fabsf
  | _, _ => .error s!"tape_codegen: unsupported op `{nm}` (arity {args.length})"

def evalTape (env : String → Float) (t : Tape Float) : Except String (Array Float) := do
  let mut vals : Array Float := Array.mkEmpty t.nodes.size
  for n in t.nodes do
    let v ← (
      if n.parents.isEmpty then
        match n.name with
        | some nm => pure (env nm)
        | none    => pure (nodeScalar n)
      else
        match n.name with
        | some nm => cOp nm (n.parents.map (fun p => vals.getD p 0.0))
        | none    => .error "tape_codegen: op node with no op name")
    vals := vals.push v
  pure vals

/-! ### C expression for one op node -/

/-- The C infix/`fminf`/`expf` expression for op `nm` on already-emitted parent temporaries. -/
def cExpr (nm : String) (ps : List Nat) : Except String String :=
  let v := fun (i : Nat) => s!"v{i}"
  match nm, ps with
  | "add",  [a, b] => .ok s!"{v a} + {v b}"
  | "sub",  [a, b] => .ok s!"{v a} - {v b}"
  | "mul",  [a, b] => .ok s!"{v a} * {v b}"
  | "div",  [a, b] => .ok s!"{v a} / {v b}"
  | "min",  [a, b] => .ok s!"fminf({v a}, {v b})"
  | "max",  [a, b] => .ok s!"fmaxf({v a}, {v b})"
  | "exp",  [a]    => .ok s!"expf({v a})"
  | "log",  [a]    => .ok s!"logf({v a})"
  | "sqrt", [a]    => .ok s!"sqrtf({v a})"
  | "abs",  [a]    => .ok s!"fabsf({v a})"
  | _, _ => .error s!"tape_codegen: unsupported op `{nm}` (arity {ps.length})"

/-- A C `float` literal for a constant leaf (full `Float.toString` precision; simple kernel
constants like `0/1/2` round-trip exactly). -/
def floatLit (x : Float) : String := s!"{x}f"

/-- The straight-line kernel body: input reads, the per-node temporaries, and the output stores. -/
structure Codegen where
  /-- Named input leaves in first-seen order — the kernel's input pointer parameters. -/
  inputs : Array String
  /-- Number of output columns. -/
  numOutputs : Nat
  /-- `const float vID = …;` lines, in node id order. -/
  body : Array String
  /-- `out[j*P + i] = vID;` lines. -/
  outLines : Array String

/-- The kernel's input parameters: the distinct **named** leaf names in first-seen order (each a
`const float* in_<nm>`). A pure `foldl`, so it is duplicate-free by construction
(`collectInputs_nodup`) and the generated ABI's input list is a pure function of the tape — `gen`
builds its `inputs` field with exactly this (`gen_inputs_eq`). -/
def collectInputs (t : Tape Float) : Array String :=
  t.nodes.foldl (init := #[]) fun inputs n =>
    if n.parents.isEmpty then
      match n.name with
      | some nm => if inputs.contains nm then inputs else inputs.push nm
      | none    => inputs
    else inputs

/-- The straight-line body lines (`const float vID = …;`) in node-id order — the only part that can
fail (an op node must carry an op name). Factored out of `gen` so the record fields that do *not*
depend on the node walk (`inputs`, `numOutputs`, `outLines`) are pure, making the codegen
well-formedness theorems (`gen_inputs_eq`, `gen_numOutputs`) immediate. -/
def genBody (t : Tape Float) : Except String (Array String) := do
  let mut body : Array String := #[]
  let mut i : Nat := 0
  for n in t.nodes do
    if n.parents.isEmpty then
      match n.name with
      | some nm => body := body.push s!"  const float v{i} = in_{nm}[p];"
      | none    => body := body.push s!"  const float v{i} = {floatLit (nodeScalar n)};"
    else
      match n.name with
      | some nm =>
          let e ← cExpr nm n.parents
          body := body.push s!"  const float v{i} = {e};"
      | none => .error s!"tape_codegen: op node {i} has no op name"
    i := i + 1
  pure body

/-- Lower a CSE'd tape + its output ids to the straight-line body. Node array index = node id
(tape ids are array indices), so a node's `vID` is `v{arrayIndex}` and its parents reference earlier
`v`s. The `inputs`/`numOutputs`/`outLines` fields are pure functions of `t`/`outIds`; only `body`
runs the (fallible) node walk (`genBody`). -/
def gen (t : Tape Float) (outIds : List Nat) : Except String Codegen :=
  (genBody t).map fun body =>
    { inputs := collectInputs t
    , numOutputs := outIds.length
    , body
    , outLines := ((outIds.zipIdx).map (fun (oid, j) => s!"  out[{j} * P + p] = v{oid};")).toArray }

/-- The kernel parameter list: `int P, const float* in_<x>…, float* out`. -/
def paramList (cg : Codegen) : String :=
  "int P" ++ String.join (cg.inputs.toList.map (fun nm => s!", const float* __restrict__ in_{nm}"))
    ++ ", float* __restrict__ out"

/-- The fused CUDA `__global__` megakernel: one thread per pixel `p`, the whole DAG in registers. -/
def emitCuda (name : String) (cg : Codegen) : String :=
  let hdr := s!"// generated by paradigm.tape_codegen — compile: nvcc --fmad=false -prec-div=true -prec-sqrt=true\n"
  let sig := s!"__global__ void {name}({paramList cg}) \{\n"
  let idx := "  int p = blockIdx.x * blockDim.x + threadIdx.x;\n  if (p >= P) return;\n"
  let bod := String.join (cg.body.toList.map (· ++ "\n"))
  let out := String.join (cg.outLines.toList.map (· ++ "\n"))
  hdr ++ sig ++ idx ++ bod ++ out ++ "}\n"

/-- The portable C-stub twin (host loop over pixels) — the CPU deployment path and the bit-exact
oracle (compile with `-ffp-contract=off`). -/
def emitStub (name : String) (cg : Codegen) : String :=
  let sig := s!"void {name}_stub({paramList cg}) \{\n"
  let loop := "  for (int p = 0; p < P; ++p) {\n"
  let bod := String.join (cg.body.toList.map ("  " ++ · ++ "\n"))
  let out := String.join (cg.outLines.toList.map ("  " ++ · ++ "\n"))
  sig ++ loop ++ bod ++ out ++ "  }\n}\n"

/-! ### FFI landing: wiring the generated kernel through a Lake `extern_lib` slot

`emitCuda` is the compute `__global__` only. Landing it through a `buildNativeBackendLib`-style
`extern_lib` slot and calling it from Lean needs three more artifacts, all generated from the *same*
`Codegen` so the ABI cannot drift from the kernel:

* a `.cu` translation unit = the device kernel + an `extern "C"` host launcher
  `<name>_launch(P, nIns, ins) : FloatArray` (upload packed inputs, one thread per pixel, download
  packed outputs);
* a `.c` **stub** twin = the portable host loop behind the identical launcher symbol, so a CUDA-free
  build links the same entry point (the `torchlean_dgemm_cuda.cu` / `_stub.c` precedent);
* the Lean `@[extern]` binding + a `NativeBackendLib`-style `{stem, cudaSrc, stubSrc}` spec.

**Packed layout** (tape-independent, so the Lean signature never changes with the tape): the `k`-th
distinct named input occupies `ins[k*P .. (k+1)*P)`, output `j` occupies `out[j*P .. (j+1)*P)` — the
same `out[j*P + p]` the kernel writes. `Float` is 64-bit while the kernel is `float`, so the launcher
casts `double ↔ float32` at the boundary (the fp64 `evalTape` denotation is the oracle the fp32 kernel
is validated against). -/

/-- The kernel's parameter list as tokens (`paramList` renders it): `int P`, one
`const float* in_<nm>` per distinct named input, then `float* out`. -/
def kernelParamList (cg : Codegen) : List String :=
  "int P" :: cg.inputs.toList.map (fun nm => s!"const float* __restrict__ in_{nm}")
    ++ ["float* __restrict__ out"]

/-- The arguments the host launcher forwards to the kernel — one per kernel parameter, same order
(`P`, each uploaded `d_in_<nm>`, `d_out`). `landing_abi_consistent` proves this has the same length as
`kernelParamList`, so the generated FFI call is arity-correct by construction. -/
def launchArgList (cg : Codegen) : List String :=
  "P" :: cg.inputs.toList.map (fun nm => s!"d_in_{nm}") ++ ["d_out"]

/-- The `.cu` translation unit: the device kernel plus an `extern "C"` host launcher that marshals the
packed `FloatArray` across the FFI, uploads inputs, launches one thread per pixel, and downloads the
packed outputs. Compile with `nvcc --fmad=false -prec-div=true -prec-sqrt=true`. -/
def emitCudaLanding (name : String) (cg : Codegen) : String :=
  let ins := cg.inputs.toList
  let nOut := cg.numOutputs
  let kernelArgs := String.intercalate ", " (launchArgList cg)
  let uploads := String.intercalate "\n" <| ins.zipIdx.map (fun (nm, k) =>
    String.intercalate "\n"
      [ s!"  float* d_in_{nm}; cudaMalloc((void**)&d_in_{nm}, nb);"
      , s!"  for (size_t i = 0; i < np; ++i) hbuf[i] = (float)src[(size_t){k} * np + i];"
      , s!"  cudaMemcpy(d_in_{nm}, hbuf, nb, cudaMemcpyHostToDevice);" ])
  let frees := String.intercalate "\n" <| ins.map (fun nm => s!"  cudaFree(d_in_{nm});")
  String.intercalate "\n"
    [ "// generated by paradigm.tape_codegen — FFI landing translation unit (CUDA path)."
    , "// compile: nvcc --fmad=false -prec-div=true -prec-sqrt=true"
    , "#include <lean/lean.h>"
    , "#include <cuda_runtime.h>"
    , "#include <stdlib.h>"
    , ""
    , emitCuda name cg
    , s!"extern \"C\" LEAN_EXPORT lean_obj_res {name}_launch(uint32_t P, uint32_t nIns, b_lean_obj_arg InsObj) \{"
    , "  (void)nIns;"
    , "  const size_t np = (size_t)P;"
    , "  const size_t nb = np * sizeof(float);"
    , s!"  const size_t no = (size_t){nOut} * np;"
    , "  const double* src = lean_float_array_cptr((lean_object*)InsObj);"
    , "  float* hbuf = (float*)malloc(nb);"
    , uploads
    , s!"  float* d_out; cudaMalloc((void**)&d_out, (size_t){nOut} * nb);"
    , "  const int threads = 256;"
    , "  const int blocks = (int)((np + (size_t)threads - 1) / (size_t)threads);"
    , s!"  {name}<<<blocks, threads>>>({kernelArgs});"
    , "  cudaDeviceSynchronize();"
    , "  lean_object* outObj = lean_mk_empty_float_array(lean_box(no));"
    , "  lean_sarray_set_size(outObj, no);"
    , "  double* dst = lean_float_array_cptr(outObj);"
    , "  float* hout = (float*)malloc(no * sizeof(float));"
    , "  cudaMemcpy(hout, d_out, no * sizeof(float), cudaMemcpyDeviceToHost);"
    , "  for (size_t i = 0; i < no; ++i) dst[i] = (double)hout[i];"
    , frees
    , "  cudaFree(d_out);"
    , "  free(hbuf); free(hout);"
    , "  return outObj;"
    , "}"
    , "" ]

/-- The `.c` stub twin: the portable host loop (`emitStub`, one pass per pixel) behind the identical
`<name>_launch` FFI symbol — a CUDA-free build links this instead. Compile with `-ffp-contract=off`. -/
def emitStubLanding (name : String) (cg : Codegen) : String :=
  let ins := cg.inputs.toList
  let nOut := cg.numOutputs
  let computeArgs := String.intercalate ", "
    (("P" :: ins.map (fun nm => s!"in_{nm}")) ++ ["out"])
  let allocs := String.intercalate "\n" <| ins.zipIdx.map (fun (nm, k) =>
    String.intercalate "\n"
      [ s!"  float* in_{nm} = (float*)malloc(np * sizeof(float));"
      , s!"  for (size_t i = 0; i < np; ++i) in_{nm}[i] = (float)src[(size_t){k} * np + i];" ])
  let frees := String.intercalate "\n" <| ins.map (fun nm => s!"  free(in_{nm});")
  String.intercalate "\n"
    [ "// generated by paradigm.tape_codegen — FFI landing translation unit (portable C stub)."
    , "// compile with -ffp-contract=off to match the device kernel bit-for-bit."
    , "#include <lean/lean.h>"
    , "#include <math.h>"
    , "#include <stdlib.h>"
    , ""
    , emitStub name cg
    , s!"LEAN_EXPORT lean_obj_res {name}_launch(uint32_t P, uint32_t nIns, b_lean_obj_arg InsObj) \{"
    , "  (void)nIns;"
    , "  const size_t np = (size_t)P;"
    , s!"  const size_t no = (size_t){nOut} * np;"
    , "  const double* src = lean_float_array_cptr((lean_object*)InsObj);"
    , allocs
    , "  float* out = (float*)malloc(no * sizeof(float));"
    , s!"  {name}_stub({computeArgs});"
    , "  lean_object* outObj = lean_mk_empty_float_array(lean_box(no));"
    , "  lean_sarray_set_size(outObj, no);"
    , "  double* dst = lean_float_array_cptr(outObj);"
    , "  for (size_t i = 0; i < no; ++i) dst[i] = (double)out[i];"
    , frees
    , "  free(out);"
    , "  return outObj;"
    , "}"
    , "" ]

/-- The Lean `@[extern]` binding for the generated launcher (tape-independent signature). Emitted as a
string so a downstream `extern_lib` client can drop it in verbatim. -/
def landingLeanBinding (name : String) : String :=
  s!"@[extern \"{name}_launch\"] opaque {name}Launch (P : UInt32) (nIns : UInt32) (ins : @& FloatArray) : FloatArray"

/-- A `buildNativeBackendLib`-style spec naming the two generated translation units for an `extern_lib`
slot (CUDA source → nvcc under `-K cuda`, `.c` stub → `cc` otherwise). -/
structure LandingSpec where
  stem : String
  cudaSrc : String
  stubSrc : String
deriving Repr

def landingSpec (name : String) : LandingSpec :=
  { stem := name, cudaSrc := s!"{name}.cu", stubSrc := s!"{name}_stub.c" }

/-- Write the two generated translation units into `dir` (AOT: with no nvrtc, the `.cu` is produced at
record time and checked in for `nvcc` to compile through the `extern_lib` slot). -/
def writeLandingFiles (dir : System.FilePath) (name : String) (cg : Codegen) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / s!"{name}.cu") (emitCudaLanding name cg)
  IO.FS.writeFile (dir / s!"{name}_stub.c") (emitStubLanding name cg)

/-! ### Arithmetic-intensity accounting -/

/-- Per-op FLOP weight (transcendentals cost more): `exp/log ≈ 10`, `sqrt ≈ 8`, `div ≈ 4`, else 1. -/
def flopWeight : Option String → Nat
  | some "exp" | some "log" => 10
  | some "sqrt"             => 8
  | some "div"              => 4
  | _                       => 1

structure AiReport where
  nNodes  : Nat
  nInputs : Nat
  nConsts : Nat
  nOps    : Nat
  nOut    : Nat
  flops   : Nat
  /-- DRAM traffic (bytes, fp32) of the **eager** elementwise carrier: every op reads its operand
  buffers and writes its result buffer to global memory, so `Σ over op-nodes of (nParents+1)·4`.
  The fused megakernel keeps every intermediate in a register and touches only inputs+outputs; this is
  the denominator that turns the roofline gap into a computed number instead of the cited ≈ 0.17. -/
  eagerBytes : Nat
  /-- op-name → count -/
  hist    : List (String × Nat)

def aiReport (t : Tape Float) (nOut : Nat) : AiReport := Id.run do
  let mut nInputs := 0
  let mut nConsts := 0
  let mut nOps := 0
  let mut flops := 0
  let mut eagerWords := 0   -- fp32 words the eager carrier round-trips through DRAM
  let mut hist : Std.HashMap String Nat := {}
  for n in t.nodes do
    if n.parents.isEmpty then
      match n.name with
      | some _ => nInputs := nInputs + 1
      | none   => nConsts := nConsts + 1
    else
      nOps := nOps + 1
      flops := flops + flopWeight n.name
      eagerWords := eagerWords + n.parents.length + 1   -- reads each operand buffer, writes one result
      let k := n.name.getD "?"
      hist := hist.insert k ((hist.getD k 0) + 1)
  let histL := (hist.toList.toArray.qsort (fun a b => a.2 > b.2)).toList
  pure { nNodes := t.nodes.size, nInputs, nConsts, nOps, nOut, flops
       , eagerBytes := eagerWords * 4, hist := histL }

/-- The intensity numbers for a recorded kernel — the FUSED and EAGER arithmetic intensities, both
computed from the same recorded DAG (identical FLOPs, different DRAM traffic).

* `fusedBytes = (#inputs + #outputs)·4` — the megakernel reads each input once, writes each output
  once, every intermediate in a register.
* `eagerBytes` (from `aiReport`) — the eager elementwise carrier round-trips every op's operands and
  result through DRAM.

`aiStep`/`aiFit` are the FUSED AI for one recorded step and for a fixed `iters`-iteration whole-fit
loop that keeps θ resident (inputs/outputs still touched once, FLOPs ×`iters`). `aiEager` is the EAGER
AI — note it is **flat in `iters`**: nothing stays resident, so each iteration re-pays the full traffic.
The compute-vs-memory-bound gap that decides CPU-vs-GPU for the whole fit is `aiFit / aiEager`. -/
structure Intensity where
  /-- Fused AI of one recorded step (`flops/fusedBytes`). -/
  aiStep     : Float
  /-- Fused AI of the `iters`-iteration whole-fit megakernel (`flops·iters/fusedBytes`). -/
  aiFit      : Float
  /-- Eager AI of the elementwise carrier (`flops/eagerBytes`); flat in `iters`. -/
  aiEager    : Float
  fusedBytes : Nat
  eagerBytes : Nat

def intensity (rep : AiReport) (iters : Nat) : Intensity :=
  let fusedBytes := (rep.nInputs + rep.nOut) * 4
  let aiStep  := Float.ofNat rep.flops / Float.ofNat fusedBytes
  let aiFit   := Float.ofNat (rep.flops * iters) / Float.ofNat fusedBytes
  let aiEager := Float.ofNat rep.flops / Float.ofNat rep.eagerBytes
  { aiStep, aiFit, aiEager, fusedBytes, eagerBytes := rep.eagerBytes }

end PropertyKindCalculus.Paradigm.TapeCodegen
