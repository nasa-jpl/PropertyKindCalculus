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

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
public import PropertyKindCalculus.Torch.Paradigm.TapeCse
public import PropertyKindCalculus.Torch.Paradigm.LutCarrier

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Spec TorchLean
open Runtime.Autograd (Tape Node TapeM)
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm (TapeBuilder NumCarrier LutTable lutNodeName?)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)

namespace PropertyKindCalculus.Paradigm.TapeCodegen

/-! ### Reading a tape node -/

/-- The scalar constant a node stores as its forward value (a scalar tape node holds one `Float`;
the same accessor `paradigm.tape_cse.nodeKey` uses). -/
def nodeScalar (n : Node Float) : Float := (TorchLean.Storage.toArray n.value.tensor.buffer).toList.headD 0.0

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
        | some nm => cOp nm ((n.parents.map (fun p => vals.getD p 0.0)).toList)
        | none    => .error "tape_codegen: op node with no op name")
    vals := vals.push v
  pure vals

/-! ### The table-extended interpreter

`paradigm.lut_carrier`'s `lutFetch` records nodes named `lutfetch:<table>` with parents
`[layerId, uId]`. `cOpT`/`evalTapeT` extend the reference interpreter with that one case —
the fp64 `LutTable.refFetch` — resolving the table by the name baked into the node. `evalTape`
itself is untouched, and `evalTapeT` with no tables *is* `evalTape` (`cOpT` falls back to `cOp`,
including for unknown tables, so the two agree error-for-error) — every existing
`evalTape`-denotation proof is unaffected. -/

/-- `cOp` extended with the `lutfetch:<table>` alphabet entry: the fetch node re-interprets as
`LutTable.refFetch` (fp64 reference). An unresolvable table name falls through to `cOp`'s
standard unsupported-op error, so `cOpT (fun _ => none) = cOp` pointwise. -/
def cOpT (tables : String → Option LutTable) (nm : String) (args : List Float) :
    Except String Float :=
  match lutNodeName? nm with
  | some tn =>
      match tables tn, args with
      | some tbl, [l, u] => .ok (tbl.refFetch l u)
      | some _, _ => .error s!"tape_codegen: lutfetch `{tn}` expects [layer, u] (arity {args.length})"
      | none, _ => cOp nm args
  | none => cOp nm args

/-- `evalTape` with the table-extended alphabet (`cOpT`). The deployed megakernel's fp64
denotation when the recorded DAG contains `lutfetch` nodes. -/
def evalTapeT (tables : String → Option LutTable) (env : String → Float) (t : Tape Float) :
    Except String (Array Float) := do
  let mut vals : Array Float := Array.mkEmpty t.nodes.size
  for n in t.nodes do
    let v ← (
      if n.parents.isEmpty then
        match n.name with
        | some nm => pure (env nm)
        | none    => pure (nodeScalar n)
      else
        match n.name with
        | some nm => cOpT tables nm ((n.parents.map (fun p => vals.getD p 0.0)).toList)
        | none    => .error "tape_codegen: op node with no op name")
    vals := vals.push v
  pure vals

/-- With no tables, the extended alphabet degenerates to `cOp` — including on `lutfetch:*`
names, where the fallback reproduces `cOp`'s error. -/
theorem cOpT_none (nm : String) (args : List Float) : cOpT (fun _ => none) nm args = cOp nm args := by
  unfold cOpT
  cases lutNodeName? nm <;> rfl

/-- With no tables, `evalTapeT` *is* `evalTape` — the extension is conservative, so every
existing `evalTape`-denotation proof transfers verbatim. -/
theorem evalTapeT_none (env : String → Float) (t : Tape Float) :
    evalTapeT (fun _ => none) env t = evalTape env t := by
  unfold evalTapeT evalTape
  simp only [cOpT_none]

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

/-- Render a `Float` as an **exact** C literal (C99/C++17 hexadecimal float, e.g.
`0x1.51eb851eb851fp-7f`). The decimal printer is lossy (6 significant digits), which would
silently detune baked table samples and recorded constants; the hex form reproduces the double
bit-for-bit, and the compiler's compile-time `double → float` narrowing is round-to-nearest —
the same conversion the runtime upload paths perform. Zero renders as `0.0f`; NaN/Inf do not
occur in generated bodies (leaf constants and table samples are finite). -/
def floatLit (x : Float) : String :=
  let bits : Nat := x.toBits.toNat
  let sign := if bits / 2 ^ 63 == 1 then "-" else ""
  let expBits : Nat := (bits / 2 ^ 52) % 2 ^ 11
  let mant : Nat := bits % 2 ^ 52
  if expBits == 0 && mant == 0 then s!"{sign}0.0f"
  else
    let mantHex := String.ofList <| (List.range 13).map fun i =>
      Nat.digitChar ((mant / 2 ^ (48 - 4 * i)) % 16)
    if expBits == 0 then s!"{sign}0x0.{mantHex}p-1022f"          -- subnormal
    else s!"{sign}0x1.{mantHex}p{Int.ofNat expBits - 1023}f"

/-- How a generated kernel realises a `lutfetch` node (`paradigm.lut_carrier`).

* `point` — two texture point fetches + an explicit contraction-blocked fp32 lerp: bit-identical
  between the CUDA kernel and the C stub (the bit-exactness carrier).
* `hardware` — one hardware-filtered `tex1DLayered` fetch: zero ALU cost, but CUDA's 9-bit
  fixed-point lerp weight makes it tolerance-only (`≤ 2⁻⁸·|Δsample|` per fetch, stub emulated);
  it is excluded from the bit-exact claims. -/
inductive LutFilterMode where
  | point
  | hardware
deriving Repr, DecidableEq, Inhabited

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
  /-- Lookup tables referenced by `lutfetch` nodes, in first-seen order — each becomes one extra
  kernel parameter (`cudaTextureObject_t tex_<name>` on CUDA, `const float* lut_<name>` in the
  stub) with its data baked into the landing translation units. Empty for pure-arithmetic tapes. -/
  tables : Array LutTable := #[]
  /-- How `lutfetch` nodes are realised (irrelevant when `tables` is empty). -/
  lutMode : LutFilterMode := .point

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

/-- The distinct table names referenced by `lutfetch` op nodes, in first-seen order — the same
pure-`foldl` shape as `collectInputs`, so it is duplicate-free by construction
(`collectTableNames_nodup`) and the generated table ABI is a pure function of the tape
(`gen_tables_eq`). -/
def collectTableNames (t : Tape Float) : Array String :=
  t.nodes.foldl (init := #[]) fun tabs n =>
    if n.parents.isEmpty then tabs
    else
      match n.name.bind lutNodeName? with
      | some tn => if tabs.contains tn then tabs else tabs.push tn
      | none    => tabs

/-- Resolve the referenced table names against the caller-supplied tables: every referenced name
must be present, and the supplied tables must carry pairwise-distinct names (a duplicate would
make the node-name → table mapping — and hence the CSE key — ambiguous, the `nodeKey` docstring's
scalar-baking hazard). Returns the resolved tables in first-seen reference order. -/
def resolveTables (names : Array String) (avail : Array LutTable) :
    Except String (Array LutTable) := do
  if (avail.map (·.name)).toList.Nodup then
    names.foldlM (init := #[]) fun acc tn =>
      match avail.find? (·.name == tn) with
      | some tbl => .ok (acc.push tbl)
      | none => .error s!"tape_codegen: lutfetch references unknown table `{tn}`"
  else
    .error "tape_codegen: supplied tables must have pairwise-distinct names"

/-- The straight-line body lines (`const float vID = …;`) in node-id order — the only part that can
fail (an op node must carry an op name). Factored out of `gen` so the record fields that do *not*
depend on the node walk (`inputs`, `numOutputs`, `outLines`) are pure, making the codegen
well-formedness theorems (`gen_inputs_eq`, `gen_numOutputs`) immediate. -/
def genBody (t : Tape Float) (tables : Array LutTable := #[]) :
    Except String (Array String) := do
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
          match lutNodeName? nm with
          | some tn =>
              -- a `lutfetch:<table>` node: backend-neutral macro call; the CUDA/stub emitters
              -- prepend the matching `TL_LUTFETCH` definition (texture fetch vs array lerp).
              match tables.find? (·.name == tn), n.parents with
              | some tbl, #[l, u] =>
                  body := body.push
                    s!"  const float v{i} = TL_LUTFETCH({tbl.name}, {tbl.width}, {tbl.layers}, v{l}, v{u});"
              | some _, _ =>
                  .error s!"tape_codegen: lutfetch node {i} expects parents [layer, u] (got {n.parents.size})"
              | none, _ =>
                  .error s!"tape_codegen: lutfetch node {i} references unknown table `{tn}`"
          | none =>
              let e ← cExpr nm n.parents.toList
              body := body.push s!"  const float v{i} = {e};"
      | none => .error s!"tape_codegen: op node {i} has no op name"
    i := i + 1
  pure body

/-- Lower a CSE'd tape + its output ids to the straight-line body. Node array index = node id
(tape ids are array indices), so a node's `vID` is `v{arrayIndex}` and its parents reference earlier
`v`s. The `inputs`/`numOutputs`/`outLines` fields are pure functions of `t`/`outIds`; only `body`
runs the (fallible) node walk (`genBody`). -/
def gen (t : Tape Float) (outIds : List Nat) (tables : Array LutTable := #[])
    (lutMode : LutFilterMode := .point) : Except String Codegen :=
  (resolveTables (collectTableNames t) tables).bind fun resolved =>
    (genBody t tables).map fun body =>
      { inputs := collectInputs t
      , numOutputs := outIds.length
      , body
      , outLines := ((outIds.zipIdx).map (fun (oid, j) => s!"  out[{j} * P + p] = v{oid};")).toArray
      , tables := resolved
      , lutMode }

/-- The kernel parameter list: `int P, const float* in_<x>…, <table params…>, float* out`.
Table parameters differ per backend — `cudaTextureObject_t tex_<n>` on the device kernel,
`const float* lut_<n>` in the portable stub (`stub := true`); same arity either way. -/
def paramList (cg : Codegen) (stub : Bool := false) : String :=
  "int P" ++ String.join (cg.inputs.toList.map (fun nm => s!", const float* __restrict__ in_{nm}"))
    ++ String.join (cg.tables.toList.map (fun tb =>
        if stub then s!", const float* lut_{tb.name}" else s!", cudaTextureObject_t tex_{tb.name}"))
    ++ ", float* __restrict__ out"

/-- The CUDA-side `lutfetch` helper + the `TL_LUTFETCH` macro `genBody`'s neutral body lines call.
Point mode: two point fetches + a `__f*_rn` contraction-blocked fp32 lerp (bit-identical to the
stub). Hardware mode: one hardware-filtered fetch (9-bit weight, tolerance-only). Empty when the
kernel uses no tables. -/
def lutHelperCuda (cg : Codegen) : String :=
  if cg.tables.isEmpty then "" else
  let body := match cg.lutMode with
    | .point => String.intercalate "\n"
        [ "  float j = floorf(uc);"
        , "  float f = __fsub_rn(uc, j);"
        , "  float a = tex1DLayered<float>(tex, j + 0.5f, L);"
        , "  float b = tex1DLayered<float>(tex, fminf(j + 1.0f, wmax) + 0.5f, L);"
        , "  return __fadd_rn(a, __fmul_rn(f, __fsub_rn(b, a)));" ]
    | .hardware => "  return tex1DLayered<float>(tex, uc + 0.5f, L);"
  String.intercalate "\n"
    [ "__device__ __forceinline__ float tl_lutfetch(cudaTextureObject_t tex, int W, float layer, float u) {"
    , "  float wmax = (float)(W - 1);"
    , "  float uc = fminf(fmaxf(u, 0.0f), wmax);"
    , "  int L = (int)(layer + 0.5f);"
    , body
    , "}"
    , "#define TL_LUTFETCH(NAME, W, LAYERS, L, U) tl_lutfetch(tex_##NAME, W, L, U)"
    , "" ]

/-- The stub-side `lutfetch` helper + macro: the same clamp/floor/lerp as a host loop over the
baked table (point mode bit-identical to the device kernel; hardware mode emulates the 9-bit
weight, tolerance-only). Empty when the kernel uses no tables. -/
def lutHelperStub (cg : Codegen) : String :=
  if cg.tables.isEmpty then "" else
  let quant := match cg.lutMode with
    | .point => ""
    | .hardware => "  f = floorf(f * 256.0f + 0.5f) / 256.0f;\n"
  String.intercalate "\n"
    [ "static float tl_lutfetch(const float* tab, int W, int LAYERS, float layer, float u) {"
    , "  float wmax = (float)(W - 1);"
    , "  float uc = u < 0.0f ? 0.0f : (u > wmax ? wmax : u);"
    , "  long L = (long)(layer + 0.5f);"
    , "  if (L < 0) L = 0;"
    , "  if (L > (long)LAYERS - 1) L = (long)LAYERS - 1;"
    , "  float j = floorf(uc);"
    , s!"  float f = uc - j;\n{quant}  const float* row = tab + (long)L * (long)W;"
    , "  long j0 = (long)j;"
    , "  long j1 = j0 + 1 < (long)W ? j0 + 1 : (long)W - 1;"
    , "  float a = row[j0];"
    , "  float b = row[j1];"
    , "  float d = b - a;"
    , "  float fd = f * d;"
    , "  return a + fd;"
    , "}"
    , "#define TL_LUTFETCH(NAME, W, LAYERS, L, U) tl_lutfetch(lut_##NAME, W, LAYERS, L, U)"
    , "" ]

/-- The fused CUDA `__global__` megakernel: one thread per pixel `p`, the whole DAG in registers.
Tables (if any) arrive as `cudaTextureObject_t` parameters, fetched through `tl_lutfetch`. -/
def emitCuda (name : String) (cg : Codegen) : String :=
  let hdr := s!"// generated by paradigm.tape_codegen — compile: nvcc --fmad=false -prec-div=true -prec-sqrt=true\n"
  let sig := s!"__global__ void {name}({paramList cg}) \{\n"
  let idx := "  int p = blockIdx.x * blockDim.x + threadIdx.x;\n  if (p >= P) return;\n"
  let bod := String.join (cg.body.toList.map (· ++ "\n"))
  let out := String.join (cg.outLines.toList.map (· ++ "\n"))
  hdr ++ lutHelperCuda cg ++ sig ++ idx ++ bod ++ out ++ "}\n"

/-- The portable C-stub twin (host loop over pixels) — the CPU deployment path and the bit-exact
oracle (compile with `-ffp-contract=off`). Tables arrive as `const float*` parameters. -/
def emitStub (name : String) (cg : Codegen) : String :=
  let sig := s!"void {name}_stub({paramList cg (stub := true)}) \{\n"
  let loop := "  for (int p = 0; p < P; ++p) {\n"
  let bod := String.join (cg.body.toList.map ("  " ++ · ++ "\n"))
  let out := String.join (cg.outLines.toList.map ("  " ++ · ++ "\n"))
  lutHelperStub cg ++ sig ++ loop ++ bod ++ out ++ "  }\n}\n"

/-! ### FFI landing: wiring the generated kernel through a Lake `extern_lib` slot

`emitCuda` is the compute `__global__` only. Landing it through a `buildNativeBackendLib`-style
`extern_lib` slot and calling it from Lean needs three more artifacts, all generated from the *same*
`Codegen` so the ABI cannot drift from the kernel:

* a `.cu` translation unit = the device kernel + an `extern "C"` host launcher
  `<name>_launch(P, nIns, cols) : FloatArray` (upload one column per slot, one thread per pixel,
  download packed outputs);
* a `.c` **stub** twin = the portable host loop behind the identical launcher symbol, so a CUDA-free
  build links the same entry point (the `torchlean_dgemm_cuda.cu` / `_stub.c` precedent);
* the Lean `@[extern]` binding + a `NativeBackendLib`-style `{stem, cudaSrc, stubSrc}` spec.

**Layout: columns in, packed out** (tape-independent, so the Lean signature never changes with the
tape). The `k`-th distinct named input arrives as `cols[k]`, its own `P`-element `FloatArray`;
output `j` occupies `out[j*P .. (j+1)*P)` — the same `out[j*P + p]` the kernel writes. `Float` is
64-bit while the kernel is `float`, so the launcher casts `double ↔ float32` at the boundary (the
fp64 `evalTape` denotation is the oracle the fp32 kernel is validated against).

**Why the inputs are columns and the outputs are not.** The landing's first act is to narrow each
slot to `float` in its own buffer — one `for` loop per slot, and unavoidable, since the kernel is
fp32 and a `FloatArray` is fp64. Given a *packed* input the caller must first concatenate its
slots into one `nIns*P` buffer for that loop to read out of again: a full copy of the inputs, on
the host, whose only consumer immediately undoes it. Given *columns* the same loop reads the
caller's own arrays and the concatenation never happens. Measured in a deploying application on a
7-slot 11.9 Mpx tile, as a paired A/B: that copy is ~256 ms and a 669 MB allocation, and removing
it takes 250 ms off the marshal and 278 MB off peak RSS. It does not move that executable's wall,
whose single launch is 7.9 s — a term can be worth removing on shape while being invisible in the
job that contains it.

It also costs the caller nothing to supply. A generated kernel's slot order is a by-product of
CSE, so a caller that owns its data by *name* must permute; with columns that permutation moves
seven pointers, and with a packed buffer it moves every element. The outputs stay packed because
the reverse argument does not hold: the landing allocates them, so there is no caller-side buffer
for it to write into and nothing to un-copy. -/

/-- The kernel's parameter list as tokens (`paramList` renders it): `int P`, one
`const float* in_<nm>` per distinct named input, one `cudaTextureObject_t tex_<nm>` per referenced
table, then `float* out`. -/
def kernelParamList (cg : Codegen) : List String :=
  "int P" :: (cg.inputs.toList.map (fun nm => s!"const float* __restrict__ in_{nm}")
    ++ cg.tables.toList.map (fun tb => s!"cudaTextureObject_t tex_{tb.name}")
    ++ ["float* __restrict__ out"])

/-- The stub kernel's parameter list as tokens: identical to `kernelParamList` except each table
slot is a `const float* lut_<nm>` (the portable build has no texture objects) — same arity, so the
two translation units stay call-compatible position-for-position. -/
def stubParamList (cg : Codegen) : List String :=
  "int P" :: (cg.inputs.toList.map (fun nm => s!"const float* in_{nm}")
    ++ cg.tables.toList.map (fun tb => s!"const float* lut_{tb.name}")
    ++ ["float* out"])

/-- The arguments the host launcher forwards to the kernel — one per kernel parameter, same order
(`P`, each uploaded `d_in_<nm>`, each table's created-once `tex_<nm>`, `d_out`).
`landing_abi_consistent` proves this has the same length as `kernelParamList`, so the generated FFI
call is arity-correct by construction. -/
def launchArgList (cg : Codegen) : List String :=
  "P" :: (cg.inputs.toList.map (fun nm => s!"d_in_{nm}")
    ++ cg.tables.toList.map (fun tb => s!"tex_{tb.name}")
    ++ ["d_out"])

/-- The baked table data for one `LutTable` — a `static const float` array in the generated
translation unit (AOT, checked-in; a 20 KB table is one array literal). fp64 sample values render
through `floatLit`; the C compiler's compile-time `double→float` narrowing is round-to-nearest,
the same conversion the runtime upload paths perform. -/
def lutDataDecl (tbl : LutTable) : String :=
  s!"static const float lut_{tbl.name}_data[{tbl.width * tbl.layers}] = \{ "
    ++ String.intercalate ", " (tbl.values.toList.map floatLit) ++ " };"

/-- The create-once texture getter for one table in the CUDA landing TU: first call builds the
layered `cudaArray`, uploads the baked data, and creates the texture object (filter mode per the
generation's `LutFilterMode`); later calls return the cached handle — tables are immutable, so
per-launch creation cost is paid once per process. -/
def lutTexGetter (mode : LutFilterMode) (tbl : LutTable) : String :=
  let filt := match mode with
    | .point => "cudaFilterModePoint"
    | .hardware => "cudaFilterModeLinear"
  String.intercalate "\n"
    [ s!"static cudaTextureObject_t tl_tex_{tbl.name} = 0;"
    , s!"static cudaTextureObject_t tl_get_tex_{tbl.name}(void) \{"
    , s!"  if (tl_tex_{tbl.name}) return tl_tex_{tbl.name};"
    , "  cudaChannelFormatDesc desc = cudaCreateChannelDesc<float>();"
    , "  cudaArray_t arr = NULL;"
    , s!"  cudaMalloc3DArray(&arr, &desc, make_cudaExtent({tbl.width}, 0, {tbl.layers}), cudaArrayLayered);"
    , "  cudaMemcpy3DParms cp; memset(&cp, 0, sizeof(cp));"
    , s!"  cp.srcPtr = make_cudaPitchedPtr((void*)lut_{tbl.name}_data, {tbl.width} * sizeof(float), {tbl.width}, 1);"
    , s!"  cp.dstArray = arr; cp.extent = make_cudaExtent({tbl.width}, 1, {tbl.layers}); cp.kind = cudaMemcpyHostToDevice;"
    , "  cudaMemcpy3D(&cp);"
    , "  cudaResourceDesc res; memset(&res, 0, sizeof(res));"
    , "  res.resType = cudaResourceTypeArray; res.res.array.array = arr;"
    , "  cudaTextureDesc td; memset(&td, 0, sizeof(td));"
    , "  td.addressMode[0] = cudaAddressModeClamp; td.addressMode[1] = cudaAddressModeClamp;"
    , s!"  td.filterMode = {filt}; td.readMode = cudaReadModeElementType; td.normalizedCoords = 0;"
    , s!"  cudaCreateTextureObject(&tl_tex_{tbl.name}, &res, &td, NULL);"
    , s!"  return tl_tex_{tbl.name};"
    , "}"
    ]

/-! ### The device clock

A host stopwatch around `<name>_launch` reads the *whole* landing: upload, kernel, download. That
is the right number for a deployment — the transfers are paid — and the wrong number for a time
model of the kernel, and until now it was the only number there was, so a device time model had
no readings it could be fitted from at all.

So the landing carries a **CUDA event bracket** around the launch itself and exposes the last
reading through a second symbol, `<name>_device_seconds`. Beside, never instead: both numbers are
wanted, and their difference is the transfer path — the one term §2.3 of the deployment's own
analysis could only infer from a bytes-over-bandwidth fit.

Three details that are decisions rather than mechanics. It reports **seconds**, because that is
the unit `Platform.elapsedTime` is stated in and a conversion left to a caller is a conversion
some caller gets wrong; `cudaEventElapsedTime` answers milliseconds and the generated line divides
once, here. It answers **−1.0** when no launch has been timed, which is the portable stub's answer
always: a negative elapsed time is not a reading any clock can produce, so it cannot be confused
with a fast kernel the way `0` could. And it takes an ignored `token`, the pattern the CUDA
allocator counters already use — the value changes between calls, so a Lean binding must not be
free to treat two reads of it as one pure expression. -/

/-- The device-clock state and accessor for the CUDA landing TU: the last bracketed launch's
elapsed time in seconds, `-1.0` before the first. -/
def deviceClockDecls (name : String) : String :=
  String.intercalate "\n"
    [ s!"static double tl_{name}_device_seconds = -1.0;"
    , s!"extern \"C\" LEAN_EXPORT double {name}_device_seconds(uint32_t token) \{"
    , "  (void)token;"
    , s!"  return tl_{name}_device_seconds;"
    , "}" ]

/-- The same accessor in the portable stub: a build with no device has no device clock, and says
so with the one value a clock cannot return. -/
def deviceClockStubDecls (name : String) : String :=
  String.intercalate "\n"
    [ s!"LEAN_EXPORT double {name}_device_seconds(uint32_t token) \{"
    , "  (void)token;"
    , "  return -1.0;   /* no device clock in a portable build */"
    , "}" ]

/-- The `.cu` translation unit: the device kernel plus an `extern "C"` host launcher that reads one
`FloatArray` column per slot across the FFI, narrows and uploads each, launches one thread per
pixel, and downloads the packed outputs. Tables (if any) are baked as `static const float` data with create-once texture
getters. The launch itself is bracketed by CUDA events, readable through `<name>_device_seconds`.
Compile with `nvcc --fmad=false -prec-div=true -prec-sqrt=true`. -/
def emitCudaLanding (name : String) (cg : Codegen) : String :=
  let ins := cg.inputs.toList
  let nOut := cg.numOutputs
  let kernelArgs := String.intercalate ", " (launchArgList cg)
  let uploads := String.intercalate "\n" <| ins.zipIdx.map (fun (nm, k) =>
    String.intercalate "\n"
      [ s!"  float* d_in_{nm}; cudaMalloc((void**)&d_in_{nm}, nb);"
      , s!"  \{ const double* src = lean_float_array_cptr(cols[{k}]);"
      , "    for (size_t i = 0; i < np; ++i) hbuf[i] = (float)src[i]; }"
      , s!"  cudaMemcpy(d_in_{nm}, hbuf, nb, cudaMemcpyHostToDevice);" ])
  let tableDecls := String.intercalate "\n" <| cg.tables.toList.map (fun tb =>
    lutDataDecl tb ++ "\n" ++ lutTexGetter cg.lutMode tb)
  let texGets := String.intercalate "\n" <| cg.tables.toList.map (fun tb =>
    s!"  cudaTextureObject_t tex_{tb.name} = tl_get_tex_{tb.name}();")
  let frees := String.intercalate "\n" <| ins.map (fun nm => s!"  cudaFree(d_in_{nm});")
  String.intercalate "\n"
    [ "// generated by paradigm.tape_codegen — FFI landing translation unit (CUDA path)."
    , "// compile: nvcc --fmad=false -prec-div=true -prec-sqrt=true"
    , "#include <lean/lean.h>"
    , "#include <cuda_runtime.h>"
    , "#include <stdlib.h>"
    , "#include <string.h>"
    , ""
    , tableDecls
    , emitCuda name cg
    , deviceClockDecls name
    , s!"extern \"C\" LEAN_EXPORT lean_obj_res {name}_launch(uint32_t P, uint32_t nIns, b_lean_obj_arg ColsObj) \{"
    , "  (void)nIns;"
    , "  const size_t np = (size_t)P;"
    , "  const size_t nb = np * sizeof(float);"
    , s!"  const size_t no = (size_t){nOut} * np;"
    , "  lean_object * const * cols = lean_array_cptr((lean_object*)ColsObj);"
    , "  float* hbuf = (float*)malloc(nb);"
    , uploads
    , texGets
    , s!"  float* d_out; cudaMalloc((void**)&d_out, (size_t){nOut} * nb);"
    , "  const int threads = 256;"
    , "  const int blocks = (int)((np + (size_t)threads - 1) / (size_t)threads);"
    , "  cudaEvent_t tl_ev0, tl_ev1;"
    , "  cudaEventCreate(&tl_ev0); cudaEventCreate(&tl_ev1);"
    , "  cudaEventRecord(tl_ev0);"
    , s!"  {name}<<<blocks, threads>>>({kernelArgs});"
    , "  cudaEventRecord(tl_ev1);"
    , "  cudaDeviceSynchronize();"
    , "  float tl_ms = 0.0f; cudaEventElapsedTime(&tl_ms, tl_ev0, tl_ev1);"
    , s!"  tl_{name}_device_seconds = (double)tl_ms / 1000.0;"
    , "  cudaEventDestroy(tl_ev0); cudaEventDestroy(tl_ev1);"
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
`<name>_launch` FFI symbol — a CUDA-free build links this instead. Tables are baked as the same
`static const float` data and passed directly. Compile with `-ffp-contract=off`. -/
def emitStubLanding (name : String) (cg : Codegen) : String :=
  let ins := cg.inputs.toList
  let nOut := cg.numOutputs
  let computeArgs := String.intercalate ", "
    (("P" :: ins.map (fun nm => s!"in_{nm}"))
      ++ cg.tables.toList.map (fun tb => s!"lut_{tb.name}_data")
      ++ ["out"])
  let tableDecls := String.intercalate "\n" <| cg.tables.toList.map lutDataDecl
  let allocs := String.intercalate "\n" <| ins.zipIdx.map (fun (nm, k) =>
    String.intercalate "\n"
      [ s!"  float* in_{nm} = (float*)malloc(np * sizeof(float));"
      , s!"  \{ const double* src = lean_float_array_cptr(cols[{k}]);"
      , s!"    for (size_t i = 0; i < np; ++i) in_{nm}[i] = (float)src[i]; }" ])
  let frees := String.intercalate "\n" <| ins.map (fun nm => s!"  free(in_{nm});")
  String.intercalate "\n"
    [ "// generated by paradigm.tape_codegen — FFI landing translation unit (portable C stub)."
    , "// compile with -ffp-contract=off to match the device kernel bit-for-bit."
    , "#include <lean/lean.h>"
    , "#include <math.h>"
    , "#include <stdlib.h>"
    , ""
    , tableDecls
    , emitStub name cg
    , deviceClockStubDecls name
    , s!"LEAN_EXPORT lean_obj_res {name}_launch(uint32_t P, uint32_t nIns, b_lean_obj_arg ColsObj) \{"
    , "  (void)nIns;"
    , "  const size_t np = (size_t)P;"
    , s!"  const size_t no = (size_t){nOut} * np;"
    , "  lean_object * const * cols = lean_array_cptr((lean_object*)ColsObj);"
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

/-- The Lean `@[extern]` bindings for the generated launcher and its device clock
(tape-independent signatures). Emitted as a string so a downstream `extern_lib` client can drop
them in verbatim.

The clock's `token` is ignored by the C side and exists only to keep Lean from treating two reads
as one pure expression — the same reason `Cuda.allocatorStatsWithToken` takes one. A call site
that reads it once per launch passes something that varies per launch, and gets an answer about
the launch it just made rather than about the first one of the process. -/
def landingLeanBinding (name : String) : String :=
  s!"@[extern \"{name}_launch\"] opaque {name}Launch (P : UInt32) (nIns : UInt32) (cols : @& Array FloatArray) : FloatArray\n" ++
  s!"@[extern \"{name}_device_seconds\"] opaque {name}DeviceSeconds (token : UInt32) : Float"

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

/-- Per-op FLOP weight (transcendentals cost more): `exp/log ≈ 10`, `sqrt ≈ 8`, `div ≈ 4`,
`lutfetch:* ≈ 4` (clamp + floor + lerp around the fetch), else 1. -/
def flopWeight : Option String → Nat
  | some "exp" | some "log" => 10
  | some "sqrt"             => 8
  | some "div"              => 4
  | some nm                 => if (lutNodeName? nm).isSome then 4 else 1
  | none                    => 1

/-- Peak number of simultaneously-live node buffers when the recorded DAG is evaluated by the
**eager** elementwise carrier in tape order, freeing each buffer immediately after its last
consumer. Named input leaves are live from launch (they are marshaled to the carrier before
the kernel runs, wherever their leaf id happens to sit); unnamed const leaves allocate at
their tape position; terminal nodes (nothing ever consumes them — the outputs) stay live to
the end. Ids are append-order and parents always lower, so one ascending pass yields each
node's last consumer.

This is the `perElement` multiplier of the affine memory model `bytes(P) = fixed +
perElement·P`: peak eager residency of a `P`-pixel batch is `maxLiveNodes t · P · 4` bytes
(fp32 buffers), where `eagerBytes` is the *traffic* of the same walk. It is an idealized
**lower bound** — GC-finalizer lag delays frees, and a loop-with-carry driver holds carry
state across recorded steps — so it is the static *prior* a measured probe calibrates,
never the authority. -/
def maxLiveNodes (t : Tape Float) : Nat := Id.run do
  let n := t.nodes.size
  if n == 0 then return 0
  -- last consumer of each node: ascending walk, so the final write is the max consumer id
  let mut lastUse : Array (Option Nat) := Array.replicate n none
  let mut j := 0
  for nd in t.nodes do
    for p in nd.parents do
      lastUse := lastUse.set! p (some j)
    j := j + 1
  -- freeAt[k] = how many buffers die right after node k executes (terminal nodes never do)
  let mut freeAt : Array Nat := Array.replicate n 0
  for i in [0:n] do
    if let some k := lastUse[i]! then
      freeAt := freeAt.set! k (freeAt[k]! + 1)
  -- forward walk: named inputs pre-counted, each other node allocates at its id, operands
  -- last used at a node are freed only after it executes (op reads them, then writes)
  let isInput := fun (nd : Node Float) => nd.parents.isEmpty && nd.name.isSome
  let mut live := t.nodes.foldl (fun acc nd => if isInput nd then acc + 1 else acc) 0
  let mut peak := live
  j := 0
  for nd in t.nodes do
    unless isInput nd do
      live := live + 1
    peak := max peak live
    live := live - freeAt[j]!
    j := j + 1
  return peak

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
  /-- Total bytes of lookup-table data the kernel binds (`Σ width·layers·4`) — compulsory traffic
  the fused model must charge (amortized per launch by `intensityWithTables`); `0` for
  pure-arithmetic tapes. Per-fetch texture-cache traffic is an L1-level effect and is documented,
  not charged (a ≤ tens-of-KB table is cache-resident — which is the texture encoding's point). -/
  tableBytes : Nat := 0
  /-- Peak simultaneously-live node buffers of the eager carrier (`maxLiveNodes`): the
  `perElement` residency multiplier — peak eager memory of a `P`-pixel batch ≈
  `maxLive · P · 4` bytes, where `eagerBytes` is the corresponding *traffic*. A static
  lower bound (see `maxLiveNodes`); the fused megakernel's counterpart is
  `nInputs + nOut` registers-only residency. -/
  maxLive : Nat := 0

def aiReport (t : Tape Float) (nOut : Nat) (tables : Array LutTable := #[]) :
    AiReport := Id.run do
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
      eagerWords := eagerWords + n.parents.size + 1   -- reads each operand buffer, writes one result
      let k := n.name.getD "?"
      hist := hist.insert k ((hist.getD k 0) + 1)
  let histL := (hist.toList.toArray.qsort (fun a b => a.2 > b.2)).toList
  let tableBytes := tables.foldl (init := 0) fun acc tb => acc + tb.width * tb.layers * 4
  pure { nNodes := t.nodes.size, nInputs, nConsts, nOps, nOut, flops
       , eagerBytes := eagerWords * 4, hist := histL, tableBytes
       , maxLive := maxLiveNodes t }

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

/-- `intensity` for a kernel that binds lookup tables: the fused model's "DRAM only for
inputs/outputs" assumption gains one compulsory term — the table upload — charged **once per
launch and amortized over the `pixels` in flight** (`fusedBytes += tableBytes / pixels`, per-pixel
like the other terms). Per-fetch traffic is texture-cache-resident and documented, not charged
(`AiReport.tableBytes`). With no tables this definitionally reduces to `intensity`. -/
def intensityWithTables (rep : AiReport) (iters pixels : Nat) : Intensity :=
  let fusedBytes := (rep.nInputs + rep.nOut) * 4 + rep.tableBytes / (max pixels 1)
  let aiStep  := Float.ofNat rep.flops / Float.ofNat fusedBytes
  let aiFit   := Float.ofNat (rep.flops * iters) / Float.ofNat fusedBytes
  let aiEager := Float.ofNat rep.flops / Float.ofNat rep.eagerBytes
  { aiStep, aiFit, aiEager, fusedBytes, eagerBytes := rep.eagerBytes }

/-! ### Peak-memory shapes — the auto-scaling prior

The AI section above accounts *traffic*; deployment sizing needs *residency*: `bytes(P)` for a
`P`-pixel batch, so a driver can solve `P` (or a shard count) against a queried capacity
(`paradigm.platform`). Three static shapes fall out of the same `aiReport`, one per execution
style. They are priors — a measured probe (allocator `peakBytes` on device, child peak RSS on
the host) is the authority, because fixed overheads and free-promptness are runtime facts. -/

/-- Per-pixel **device** bytes of the FUSED megakernel: the fp32 input and output planes only —
every intermediate is a register. The marginal term of `fusedPeakBytes`, exposed on its own so a
descriptor emitter can bake the constant without restating the formula. -/
def AiReport.fusedBytesPerElem (rep : AiReport) : Nat :=
  (rep.nInputs + rep.nOut) * 4

/-- Peak **device** bytes of a `P`-pixel launch of the FUSED megakernel: inputs + outputs only
(every intermediate is a register), plus the bound tables once per launch. -/
def AiReport.fusedPeakBytes (rep : AiReport) (pixels : Nat) : Nat :=
  rep.fusedBytesPerElem * pixels + rep.tableBytes

/-- Peak **device (or CPU-stub) buffer** bytes of a `P`-pixel batch on the EAGER elementwise
carrier — the ideal-promptness lower bound `maxLive · P · 4` (see `maxLiveNodes`), plus the
bound tables. -/
def AiReport.eagerPeakBytes (rep : AiReport) (pixels : Nat) : Nat :=
  rep.maxLive * pixels * 4 + rep.tableBytes

/-- Per-pixel **host** bytes of a sharded CPU deployment around the eager stub carrier: the
fp64 input-column slices and stitched fp64 output columns (`8·(nInputs+nOut)` — each shard
copies its slice, and the totals are invariant in the shard count) plus the fp32 stub buffers
(`4·maxLive`). The static prior for a `Platform.MemShape.bytesPerElem`. -/
def AiReport.eagerHostBytesPerElem (rep : AiReport) : Nat :=
  8 * (rep.nInputs + rep.nOut) + 4 * rep.maxLive

end PropertyKindCalculus.Paradigm.TapeCodegen

end -- pkc-blanket-expose
end -- pkc-blanket
