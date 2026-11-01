/-
`paradigm.tape_codegen_julia` — **the Julia emitter**: the third rendering of a recorded, CSE'd
tape (`paradigm.tape_cse`), beside the fused CUDA kernel and the portable C stub of
`paradigm.tape_codegen`. Same DAG walk, same alphabet, a Julia function instead of a C one.

WHY A JULIA TARGET. A Julia host (a CliMA-style model, a Julia analysis notebook) can call a
function it is handed; it cannot call a Lean theorem. The emitter hands it the *sealed* algorithm:
the tape it renders is the one `paradigm.tape_seal`'s `semantic_seal` is stated over, so every input
of the Julia function is a named leaf of the tape, every constant is a baked leaf the hypergraph's
assumption ledger lists, and the body is the tape's arithmetic op for op. Nothing enters the Julia
code that did not enter the tape — that is what the seal of the computation says, and the rendering
adds no entry point: no literal that is not a leaf, no call that is not an alphabet op.

WHAT IS PROVED, WHAT IS TRUSTED. `evalTape` (`paradigm.tape_eval`) remains the denotation; the
emitter changes only the surface syntax, never the DAG. The per-op `rendering_table_*` theorems
below state, as `paradigm.tape_codegen`'s do for C, that `jlExpr` renders exactly the alphabet `cOp`
interprets. The trusted base the Julia target adds is Julia + LLVM compiling a straight-line
function, and Julia's `exp`/`log` (pure-Julia `Base.Math`, a third libm beside glibc and libdevice):
on `+ − × ÷ √ |·| min max` a `Float64` run is bit-identical to `evalTape` — Lean's `Float` *is*
binary64, so unlike the `float` CUDA kernel there is no narrowing at the boundary — and on `exp`/`log`
the honest check is an ulp bound (`apps.julia_parity`). The semantics choices the rendering pins:

  * no `@fastmath`, no `muladd` — Julia does not contract `a*b + c` to an FMA or re-associate unless
    asked, so the default is the `nvcc --fmad=false` regime; the header says so;
  * `min`/`max` render as `ifelse(a <= b, a, b)` / `ifelse(a <= b, b, a)`, which is *exactly* Lean's
    `Min Float`/`Max Float` (`minOfLe`/`maxOfLe`, `if x ≤ y then x else y`), NaN cases included. The C
    rendering's `fminf`/`fmaxf` return the non-NaN operand instead; this emitter sides with `cOp`;
  * `sqrt`/`log` of a negative argument throw a `DomainError` in Julia where IEEE (and `Float.sqrt`,
    `Float.log`, `sqrtf`, `logf`) return a quiet NaN; the emitted `tl_sqrt`/`tl_log` helpers restore
    the NaN, and are the identity on the non-negative domain (`-0.0` is not negative, so `sqrt(-0.0)
    = -0.0` and `log(-0.0) = -Inf` as in IEEE);
  * constants render as `T(reinterpret(Float64, 0x…))` from the double's bit pattern (Julia has no C99
    hex-float literal); `T = Float64` is the exact double, `T = Float32` the same round-to-nearest
    narrowing the C compiler performs on `floatLit`'s `…f` literal;
  * precision is the type parameter `T<:AbstractFloat`: one emitted function is the `Float64` parity
    twin of `evalTape` and the `Float32` deployment kernel;
  * `lutfetch` is the C stub's clamp/floor/lerp over the same flat `layers × width` row-major vector
    (`tl_lutfetch`), point mode bit-identical, hardware mode emulating the 9-bit weight.

Two surfaces are emitted from one body: a plain `function name!(out, in_…) … end` host loop
(`emitJulia`, no package dependencies — the **bit-exact twin**, what the parity probe gates), and a
KernelAbstractions.jl `@kernel` (`emitJuliaKA`) that the same `.jl` runs on CPU, CUDA, AMDGPU or
Metal — the **portability twin**, the Julia side of "choosing a carrier, not rewriting the model".
The portability twin is tolerance-only, like the `.hardware` table mode: a KernelAbstractions backend
may contract `a*b + c` to a fused multiply-add — KernelAbstractions 0.10's CPU backend compiles the
kernel through PoCL (OpenCL) with `fuse_muladd` on whenever the host has hardware FMA
(`src/pocl/compiler/compilation.jl`), and LLVM's NVPTX default is `fmad=true` — and a contraction
moves an intermediate by an ulp, which a conditioned tail amplifies: measured on the CPU backend at
1 ulp on 8 of 320 AVS outputs, and up to ~1100 ulps (relative ~1e-13) after the LM step's normal
equations and Cholesky solve. So the parity probe compares this surface by relative error
(`--ka`, `--ka-rtol`), reports the ulp figure, and never claims bit-identity for it.

A `module` file: imports the C/CUDA codegen it mirrors.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCodegen

@[expose] public section Blanket

open Runtime.Autograd (Tape Node)
open PropertyKindCalculus.Paradigm (LutTable lutNodeName?)

namespace PropertyKindCalculus.Paradigm.TapeCodegen.Julia

/-! ### Julia expression for one op node -/

/-- The Julia expression for op `nm` on already-emitted parent temporaries — the Julia twin of
`cExpr`, over the same alphabet. `min`/`max` are Lean's `minOfLe`/`maxOfLe` spelled out; `sqrt`/`log`
go through the NaN-restoring helpers the emitted header defines. -/
def jlExpr (nm : String) (ps : List Nat) : Except String String :=
  let v := fun (i : Nat) => s!"v{i}"
  match nm, ps with
  | "add",  [a, b] => .ok s!"{v a} + {v b}"
  | "sub",  [a, b] => .ok s!"{v a} - {v b}"
  | "mul",  [a, b] => .ok s!"{v a} * {v b}"
  | "div",  [a, b] => .ok s!"{v a} / {v b}"
  | "min",  [a, b] => .ok s!"ifelse({v a} <= {v b}, {v a}, {v b})"
  | "max",  [a, b] => .ok s!"ifelse({v a} <= {v b}, {v b}, {v a})"
  | "exp",  [a]    => .ok s!"exp({v a})"
  | "log",  [a]    => .ok s!"tl_log({v a})"
  | "sqrt", [a]    => .ok s!"tl_sqrt({v a})"
  | "abs",  [a]    => .ok s!"abs({v a})"
  | _, _ => .error s!"tape_codegen_julia: unsupported op `{nm}` (arity {ps.length})"

/-- Render a `Float` as an **exact** Julia literal of the kernel's precision `T`: the double's bit
pattern through `reinterpret(Float64, 0x…)`, converted to `T`. Zero renders as `zero(T)`; the
conversion `Float64 → Float32` is round-to-nearest, the same narrowing `floatLit`'s `…f` literal
receives from the C compiler. -/
def jlLit (x : Float) : String :=
  let bits : Nat := x.toBits.toNat
  if bits == 0 then "zero(T)"
  else
    let hex := String.ofList <| (List.range 16).map fun i =>
      Nat.digitChar ((bits / 2 ^ (60 - 4 * i)) % 16)
    s!"T(reinterpret(Float64, 0x{hex}))"

/-- The straight-line Julia kernel body: input reads, the per-node temporaries, the output stores,
and the tables the body fetches from. The Julia twin of `Codegen`; a separate type so an emitter
cannot be handed the C body by mistake. -/
structure JuliaCodegen where
  /-- Named input leaves in first-seen order (`collectInputs`) — the `in_<nm>` vector arguments. -/
  inputs : Array String
  /-- Number of output columns. -/
  numOutputs : Nat
  /-- `v<id> = …` lines, in node id order. -/
  body : Array String
  /-- `out[p, j] = v<id>` lines (1-based column `j`, column-major: column `j` is contiguous over `p`,
  the same memory layout as the C `out[j*P + p]`). -/
  outLines : Array String
  /-- Lookup tables referenced by `lutfetch` nodes, in first-seen order — each an extra
  `lut_<name>::AbstractVector{T}` argument holding the flat `layers × width` row-major samples. -/
  tables : Array LutTable := #[]
  /-- How `lutfetch` nodes are realised (irrelevant when `tables` is empty). -/
  lutMode : LutFilterMode := .point

/-- The Julia body lines — `genBody`'s walk with the Julia rendering of each node kind. -/
def genBodyJulia (t : Tape Float) (tables : Array LutTable := #[]) :
    Except String (Array String) := do
  let mut body : Array String := #[]
  let mut i : Nat := 0
  for n in t.nodes do
    if n.parents.isEmpty then
      match n.name with
      | some nm => body := body.push s!"        v{i} = in_{nm}[p]"
      | none    => body := body.push s!"        v{i} = {jlLit (nodeScalar n)}"
    else
      match n.name with
      | some nm =>
          match lutNodeName? nm with
          | some tn =>
              match tables.find? (·.name == tn), n.parents with
              | some tbl, #[l, u] =>
                  body := body.push
                    s!"        v{i} = tl_lutfetch(lut_{tbl.name}, {tbl.width}, {tbl.layers}, v{l}, v{u})"
              | some _, _ =>
                  .error s!"tape_codegen_julia: lutfetch node {i} expects parents [layer, u] (got {n.parents.size})"
              | none, _ =>
                  .error s!"tape_codegen_julia: lutfetch node {i} references unknown table `{tn}`"
          | none =>
              let e ← jlExpr nm n.parents.toList
              body := body.push s!"        v{i} = {e}"
      | none => .error s!"tape_codegen_julia: op node {i} has no op name"
    i := i + 1
  pure body

/-- Lower a CSE'd tape + its output ids to a Julia kernel — `gen`'s twin. The ABI fields
(`inputs`, `tables`) are the same pure functions of the tape `gen` uses, so the Julia function's
argument list is the C kernel's parameter list, name for name. -/
def genJulia (t : Tape Float) (outIds : List Nat) (tables : Array LutTable := #[])
    (lutMode : LutFilterMode := .point) : Except String JuliaCodegen :=
  (resolveTables (collectTableNames t) tables).bind fun resolved =>
    (genBodyJulia t tables).map fun body =>
      { inputs := collectInputs t
      , numOutputs := outIds.length
      , body
      , outLines := ((outIds.zipIdx).map (fun (oid, j) => s!"        out[p, {j + 1}] = v{oid}")).toArray
      , tables := resolved
      , lutMode }

/-! ### The emitted header: the pinned semantics, and the helpers -/

/-- The header every emitted file carries: what the rendering pins, so a reader of the `.jl`
alone knows which regime it is in. -/
def header : String := String.intercalate "\n"
  [ "# generated by paradigm.tape_codegen_julia — the Julia twin of the CUDA megakernel / C stub."
  , "# Semantics pinned by the emitter: no @fastmath, no muladd (no FMA contraction, no re-association);"
  , "# min/max are `ifelse(a <= b, a, b)` / `ifelse(a <= b, b, a)` (Lean's Min/Max Float, NaN included);"
  , "# tl_sqrt/tl_log return NaN on a negative argument where Julia would throw (IEEE behaviour);"
  , "# T = Float64 is bit-identical to Lean's evalTape on + - * / sqrt abs min max, ulp-close on exp/log;"
  , "# T = Float32 is the device precision of the CUDA kernel."
  , "# The plain host function is the bit-exact twin; the KernelAbstractions @kernel is the portability twin,"
  , "# tolerance-only: a backend may contract a*b + c to an FMA (the CPU backend compiles via PoCL with fuse_muladd)."
  , "" ]

/-- The NaN-restoring `sqrt`/`log` helpers (identity on the non-negative domain). -/
def mathHelpers : String := String.intercalate "\n"
  [ "@inline tl_sqrt(x::T) where {T<:AbstractFloat} = x < zero(T) ? T(NaN) : sqrt(x)"
  , "@inline tl_log(x::T) where {T<:AbstractFloat} = x < zero(T) ? T(NaN) : log(x)"
  , "" ]

/-- The `lutfetch` helper: the C stub's clamp/floor/lerp over the flat row-major table (point mode
bit-identical to the stub and the device kernel; hardware mode emulates the 9-bit weight,
tolerance-only). Empty when the kernel uses no tables. -/
def lutHelperJulia (cg : JuliaCodegen) : String :=
  if cg.tables.isEmpty then "" else
  let quant := match cg.lutMode with
    | .point => ""
    | .hardware => "    f = floor(f * T(256) + T(0.5)) / T(256)\n"
  String.intercalate "\n"
    [ "@inline function tl_lutfetch(tab::AbstractVector{T}, W::Int, LAYERS::Int, layer::T, u::T) where {T<:AbstractFloat}"
    , "    wmax = T(W - 1)"
    , "    uc = u < zero(T) ? zero(T) : (u > wmax ? wmax : u)"
    , "    L = unsafe_trunc(Int, layer + T(0.5))"
    , "    L = L < 0 ? 0 : (L > LAYERS - 1 ? LAYERS - 1 : L)"
    , "    j = floor(uc)"
    , s!"    f = uc - j\n{quant}    j0 = unsafe_trunc(Int, j)"
    , "    j1 = j0 + 1 < W ? j0 + 1 : W - 1"
    , "    base = L * W"
    , "    @inbounds a = tab[base + j0 + 1]"
    , "    @inbounds b = tab[base + j1 + 1]"
    , "    d = b - a"
    , "    fd = f * d"
    , "    return a + fd"
    , "end"
    , "" ]

/-- The argument list after `out`: `in_<x>::AbstractVector{T}, …, lut_<n>::AbstractVector{T}, …`. -/
def argList (cg : JuliaCodegen) : String :=
  String.join (cg.inputs.toList.map (fun nm => s!", in_{nm}::AbstractVector\{T}"))
    ++ String.join (cg.tables.toList.map (fun tb => s!", lut_{tb.name}::AbstractVector\{T}"))

/-- The plain-Julia host kernel: `name!(out, in_…, lut_…)` loops over the pixels of `out`'s first
axis and fills its `numOutputs` columns. No package dependencies; the parity probe's target. -/
def emitJulia (name : String) (cg : JuliaCodegen) : String :=
  let sig := s!"function {name}!(out::AbstractMatrix\{T}{argList cg}) where \{T<:AbstractFloat}\n"
  let loop := "    P = size(out, 1)\n    @inbounds for p in 1:P\n"
  let bod := String.join (cg.body.toList.map (· ++ "\n"))
  let out := String.join (cg.outLines.toList.map (· ++ "\n"))
  header ++ mathHelpers ++ lutHelperJulia cg ++ sig ++ loop ++ bod ++ out ++ "    end\n    return out\nend\n"

/-- The KernelAbstractions.jl twin: one work-item per pixel, the same body, so the one `.jl` runs
on CPU, CUDA, AMDGPU or Metal through the backend the caller launches it on
(`name_kernel!(backend)(out, in_…; ndrange = size(out, 1))`). Tolerance-only: the backend may
contract to FMA (see the module docstring), so this surface is compared in ulps, never bits. -/
def emitJuliaKA (name : String) (cg : JuliaCodegen) : String :=
  let ins := String.join (cg.inputs.toList.map (fun nm => s!", @Const(in_{nm})"))
    ++ String.join (cg.tables.toList.map (fun tb => s!", @Const(lut_{tb.name})"))
  let sig := s!"@kernel function {name}_kernel!(out{ins})\n"
  let idx := "    p = @index(Global)\n    T = eltype(out)\n    @inbounds begin\n"
  let bod := String.join (cg.body.toList.map (· ++ "\n"))
  let out := String.join (cg.outLines.toList.map (· ++ "\n"))
  header ++ "using KernelAbstractions\n" ++ mathHelpers ++ lutHelperJulia cg ++ sig ++ idx ++ bod ++ out
    ++ "    end\nend\n"

/-! ### The rendering table

`jlExpr` renders exactly the alphabet `cOp` interprets — the same statement
`examples.tape_codegen_end_to_end` makes for `cExpr`, so the two emitters are twins over one
denotation: wherever the Float interpreter has a value, both renderings have an expression. -/

/-- The binary alphabet: `cOp` computes the op and `jlExpr` renders it, for `add sub mul div min
max`. -/
theorem rendering_table_binary (i j : Nat) (x y : Float) :
    (cOp "add" [x, y] = .ok (x + y) ∧ (jlExpr "add" [i, j]).isOk) ∧
    (cOp "sub" [x, y] = .ok (x - y) ∧ (jlExpr "sub" [i, j]).isOk) ∧
    (cOp "mul" [x, y] = .ok (x * y) ∧ (jlExpr "mul" [i, j]).isOk) ∧
    (cOp "div" [x, y] = .ok (x / y) ∧ (jlExpr "div" [i, j]).isOk) ∧
    (cOp "min" [x, y] = .ok (Min.min x y) ∧ (jlExpr "min" [i, j]).isOk) ∧
    (cOp "max" [x, y] = .ok (Max.max x y) ∧ (jlExpr "max" [i, j]).isOk) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The unary alphabet, likewise: `exp log sqrt abs`. -/
theorem rendering_table_unary (i : Nat) (x : Float) :
    (cOp "exp" [x] = .ok (Float.exp x) ∧ (jlExpr "exp" [i]).isOk) ∧
    (cOp "log" [x] = .ok (Float.log x) ∧ (jlExpr "log" [i]).isOk) ∧
    (cOp "sqrt" [x] = .ok (Float.sqrt x) ∧ (jlExpr "sqrt" [i]).isOk) ∧
    (cOp "abs" [x] = .ok (Float.abs x) ∧ (jlExpr "abs" [i]).isOk) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The Julia rendering and the C rendering agree on **where** they are defined, op by op over the
alphabet: an op has a Julia expression exactly when it has a C one (the two emitters are twins over
the one interpreter, not two alphabets). -/
theorem jlExpr_isOk_eq_cExpr_binary (i j : Nat) :
    (jlExpr "add" [i, j]).isOk = (cExpr "add" [i, j]).isOk ∧
    (jlExpr "sub" [i, j]).isOk = (cExpr "sub" [i, j]).isOk ∧
    (jlExpr "mul" [i, j]).isOk = (cExpr "mul" [i, j]).isOk ∧
    (jlExpr "div" [i, j]).isOk = (cExpr "div" [i, j]).isOk ∧
    (jlExpr "min" [i, j]).isOk = (cExpr "min" [i, j]).isOk ∧
    (jlExpr "max" [i, j]).isOk = (cExpr "max" [i, j]).isOk :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `min`/`max` as rendered are Lean's: the `Min Float`/`Max Float` instances are `minOfLe`/`maxOfLe`,
`if x ≤ y then x else y` and `if x ≤ y then y else x` — the `ifelse(a <= b, a, b)` / `ifelse(a <= b,
b, a)` the emitter writes, NaN cases included (`x ≤ y` is false when either is NaN, so `min` returns
`y` and `max` returns `x`, as the emitted `ifelse` does). -/
theorem min_eq_ite (x y : Float) : Min.min x y = if x ≤ y then x else y := rfl

theorem max_eq_ite (x y : Float) : Max.max x y = if x ≤ y then y else x := rfl

end PropertyKindCalculus.Paradigm.TapeCodegen.Julia

end Blanket
