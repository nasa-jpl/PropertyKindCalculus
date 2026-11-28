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
  * `min`/`max` render as Julia's `min(a, b)` / `max(a, b)`, IEEE 754-2019 minimum/maximum like Lean
    4.36's `Min Float`/`Max Float`: a NaN operand gives NaN and `-0.0` orders below `+0.0`, the
    function the C rendering (`cExpr`) spells out, so interpreter and all three renderings agree;
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
    (`tl_lutfetch`), in binary64 and rounded once to `T`, point mode bit-identical, hardware mode
    emulating the 9-bit weight.

Two surfaces are emitted from one body: a plain `function name!(out, in_…) … end` host loop
(`emitJulia`, no package dependencies — the **bit-exact twin**, what the parity probe gates), and a
KernelAbstractions.jl `@kernel` (`emitJuliaKA`) that the same `.jl` runs on CPU, CUDA, AMDGPU or
Metal — the **portability twin**, the Julia side of "choosing a carrier, not rewriting the model".
A table fetch on `Float32` data uses no `Float64`, so it runs on Metal too.
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

open PropertyKindCalculus.Paradigm (TapeM CpuTape CpuNode)
open PropertyKindCalculus.Paradigm (LutTable lutNodeName?)

namespace PropertyKindCalculus.Paradigm.TapeCodegen.Julia

/-! ### The Julia printer

The emitter is a *printer* of the backend-neutral straight-line program `SL.genSL` reads off the
tape (`paradigm.tape_straight_line`): `printJulia` renders one program line, `genBodyJulia` is
`genSL` followed by `printJulia` line by line, `jlExpr` is `SL.mkOp` followed by `printJulia`. The
denotation theorem `SL.genSL_denotes` is therefore the Julia kernel's too, with nothing proved
about Julia specifically: what remains to trust is that each of `printJulia`'s dozen forms means,
in Julia without `@fastmath`/`muladd`, what `SL.SLExpr.denote` means. -/

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

/-- The Julia text of one program line — **the Julia printer**, total over `SLExpr`. `min`/`max`
are Julia's, the IEEE minimum/maximum Lean's `Min Float`/`Max Float` compute; `sqrt`/`log` go through the NaN-restoring
helpers the emitted header defines; a fetch is the `tl_lutfetch` helper on the table's flat vector. -/
def printJulia : SL.SLExpr → String
  | .input nm => s!"in_{nm}[p]"
  | .lit x => jlLit x
  | .bin o a b =>
      match o with
      | .add => s!"v{a} + v{b}"
      | .sub => s!"v{a} - v{b}"
      | .mul => s!"v{a} * v{b}"
      | .div => s!"v{a} / v{b}"
      | .pow => s!"tl_pow(v{a}, v{b})"
      | .min => s!"min(v{a}, v{b})"
      | .max => s!"max(v{a}, v{b})"
      | .fmin => s!"(isnan(v{b}) || (!isnan(v{a}) && (v{a} < v{b} || (v{a} == v{b} && signbit(v{a})))) ? v{a} : v{b})"
      | .fmax => s!"(isnan(v{b}) || (!isnan(v{a}) && (v{a} > v{b} || (v{a} == v{b} && !signbit(v{a})))) ? v{a} : v{b})"
  | .un o a =>
      match o with
      | .exp => s!"exp(v{a})"
      | .log => s!"tl_log(v{a})"
      | .sqrt => s!"tl_sqrt(v{a})"
      | .abs => s!"abs(v{a})"
  | .fetch _ tbl l u => s!"tl_lutfetch(lut_{tbl.name}, {tbl.width}, {tbl.layers}, v{l}, v{u})"

/-- The Julia expression for op `nm` on already-emitted parent temporaries — the Julia twin of
`cExpr`: the same program op line (`SL.mkOp`), printed by `printJulia`. -/
def jlExpr (nm : String) (ps : List Nat) : Except String String :=
  (SL.mkOp nm ps).map printJulia

/-- One body line of the Julia kernel: slot `i` as a `v<i>` binding. -/
def printLineJulia (e : SL.SLExpr) (i : Nat) : String := s!"        v{i} = {printJulia e}"

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

/-- The Julia body lines — the program `SL.genSL` reads off the tape, printed line by line by
`printJulia`. Fails exactly where `genBody` does (`genBodyJulia_isOk_eq_genBody`): the two emitters
print one program. -/
def genBodyJulia (t : CpuTape Float) (tables : Array LutTable := #[]) :
    Except String (Array String) :=
  (SL.genSL t tables).map fun prog => prog.zipIdx.map fun p => printLineJulia p.1 p.2

/-- `genBodyJulia` is the printer of the program: on a tape `genSL` accepts, its lines are
`printLineJulia` of the program's lines, slot by slot. -/
theorem genBodyJulia_of_genSL {t : CpuTape Float} {tables : Array LutTable} {prog : SL.SLProg}
    (h : SL.genSL t tables = .ok prog) :
    genBodyJulia t tables = .ok (prog.zipIdx.map fun p => printLineJulia p.1 p.2) := by
  unfold genBodyJulia; rw [h]; rfl

/-- The Julia body and the C body exist on exactly the same tapes — one program, two printers. -/
theorem genBodyJulia_isOk_eq_genBody (t : CpuTape Float) (tables : Array LutTable) :
    (genBodyJulia t tables).isOk = (genBody t tables).isOk := by
  unfold genBodyJulia genBody; cases SL.genSL t tables <;> rfl

/-- Lower a CSE'd tape + its output ids to a Julia kernel — `gen`'s twin. The ABI fields
(`inputs`, `tables`) are the same pure functions of the tape `gen` uses, so the Julia function's
argument list is the C kernel's parameter list, name for name. -/
def genJulia (t : CpuTape Float) (outIds : List Nat) (tables : Array LutTable := #[])
    (lutMode : LutFilterMode := .point) : Except String JuliaCodegen :=
  (checkWF t).bind fun _ =>
  (checkOutputs t outIds).bind fun _ =>
  (checkScalarLeaves t).bind fun _ =>
  (resolveTables (collectTableNames t) tables).bind fun resolved =>
    (genBodyJulia t tables).map fun body =>
      { inputs := collectInputs t
      , numOutputs := outIds.length
      , body
      , outLines := ((outIds.zipIdx).map (fun (oid, j) => s!"        out[p, {j + 1}] = v{oid}")).toArray
      , tables := resolved
      , lutMode }

/-- `genJulia` succeeds only on a well-formed tape — the same check `gen` makes. -/
theorem genJulia_wf {t : CpuTape Float} {outIds : List Nat} {tables : Array LutTable}
    {mode : LutFilterMode} {cg : JuliaCodegen} (h : genJulia t outIds tables mode = .ok cg) : WF t := by
  unfold genJulia at h
  cases hw : checkWF t with
  | error e => rw [hw] at h; simp [Except.bind] at h
  | ok u => exact checkWF_ok hw

/-- `genJulia` succeeds only when every constant leaf stores exactly one scalar — the same check
`gen` makes. -/
theorem genJulia_scalar_leaves {t : CpuTape Float} {outIds : List Nat} {tables : Array LutTable}
    {mode : LutFilterMode} {cg : JuliaCodegen} (h : genJulia t outIds tables mode = .ok cg) :
    ScalarLeaves t := by
  unfold genJulia at h
  cases hw : checkWF t with
  | error e => rw [hw] at h; simp [Except.bind] at h
  | ok u =>
  rw [hw] at h
  simp only [Except.bind] at h
  cases ho : checkOutputs t outIds with
  | error e => rw [ho] at h; simp at h
  | ok u =>
  rw [ho] at h
  simp only at h
  cases hs : checkScalarLeaves t with
  | error e => rw [hs] at h; simp at h
  | ok u => exact checkScalarLeaves_ok hs

/-- `genJulia` succeeds only with every output id in range — the same check `gen` makes. -/
theorem genJulia_outIds_lt {t : CpuTape Float} {outIds : List Nat} {tables : Array LutTable}
    {mode : LutFilterMode} {cg : JuliaCodegen} (h : genJulia t outIds tables mode = .ok cg) :
    ∀ o ∈ outIds, o < t.size := by
  unfold genJulia at h
  cases hw : checkWF t with
  | error e => rw [hw] at h; simp [Except.bind] at h
  | ok u =>
  rw [hw] at h
  simp only [Except.bind] at h
  cases ho : checkOutputs t outIds with
  | error e => rw [ho] at h; simp at h
  | ok u => exact checkOutputs_ok ho

/-! ### The emitted header: the pinned semantics, and the helpers -/

/-- The header every emitted file carries: what the rendering pins, so a reader of the `.jl`
alone knows which regime it is in. -/
def header : String := String.intercalate "\n"
  [ "# generated by paradigm.tape_codegen_julia — the Julia twin of the CUDA megakernel / C stub."
  , "# Semantics pinned by the emitter: no @fastmath, no muladd (no FMA contraction, no re-association);"
  , "# min/max are Julia's `min`/`max`: IEEE minimum/maximum (Lean's Min/Max Float), NaN propagates, -0.0 < +0.0;"
  , "# tl_sqrt/tl_log return NaN on a negative argument where Julia would throw (IEEE behaviour);"
  , "# tl_pow is C pow: its special cases are written out (Julia's ^ throws or differs there), ^ elsewhere;"
  , "# T = Float64 is bit-identical to Lean's evalTape on + - * / sqrt abs min max, ulp-close on exp/log/pow;"
  , "# T = Float32 is the device precision of the CUDA kernel."
  , "# The plain host function is the bit-exact twin; the KernelAbstractions @kernel is the portability twin,"
  , "# tolerance-only: a backend may contract a*b + c to an FMA (the CPU backend compiles via PoCL with fuse_muladd)."
  , "" ]

/-- The NaN-restoring `sqrt`/`log` helpers (identity on the non-negative domain), and `tl_pow`:
C `pow`'s special cases written out, Julia's `^` on finite nonzero operands where it cannot throw. -/
def mathHelpers : String := String.intercalate "\n"
  [ "@inline tl_sqrt(x::T) where {T<:AbstractFloat} = x < zero(T) ? T(NaN) : sqrt(x)"
  , "@inline tl_log(x::T) where {T<:AbstractFloat} = x < zero(T) ? T(NaN) : log(x)"
  , "@inline function tl_pow(x::T, y::T) where {T<:AbstractFloat}"
  , "    (y == zero(T) || x == one(T)) && return one(T)"
  , "    (isnan(x) || isnan(y)) && return T(NaN)"
  , "    if isinf(y)"
  , "        ax = abs(x)"
  , "        return ax == one(T) ? one(T) : ((ax < one(T)) == (y < zero(T)) ? T(Inf) : zero(T))"
  , "    end"
  , "    if isinf(x) || x == zero(T)"
  , "        r = isinf(x) == (y > zero(T)) ? T(Inf) : zero(T)"
  , "        return (signbit(x) && isinteger(y) && !isinteger(y / 2)) ? -r : r"
  , "    end"
  , "    (x < zero(T) && !isinteger(y)) && return T(NaN)"
  , "    r = abs(x)^y"
  , "    return (x < zero(T) && !isinteger(y / 2)) ? -r : r"
  , "end"
  , "" ]

/-- Binary64 `a + f*(b - a)` on finite `Float32` values, rounded once to `Float32`, in integer
arithmetic only: the table fetch for backends without `Float64` (Metal). -/
def softFloatJulia : String := String.intercalate "\n"
    [ "# Finite Float32 as sign, integer significand and exponent: x = (-1)^s * m * 2^e."
    , "@inline function tl_sf_split(x::Float32)"
    , "    bits = reinterpret(UInt32, x)"
    , "    ex = (bits >> 23) & 0x000000ff"
    , "    fr = (bits & 0x007fffff) % UInt64"
    , "    s = (bits >> 31) % UInt64"
    , "    return ex == 0x00000000 ? (s, fr, -149) : (s, fr | 0x0000000000800000, (ex % Int) - 150)"
    , "end"
    , "# Round m * 2^e to a 53-bit significand, ties to even; bit 0 of m may be a sticky bit."
    , "@inline function tl_sf_round(s::UInt64, m::UInt64, e::Int)"
    , "    m == 0x0000000000000000 && return (s, m, 0)"
    , "    k = 11 - leading_zeros(m)"
    , "    k <= 0 && return (s, m << (-k), e + k)"
    , "    q = m >> k"
    , "    r = m & ((0x0000000000000001 << k) - 0x0000000000000001)"
    , "    h = 0x0000000000000001 << (k - 1)"
    , "    q += ((r > h) | ((r == h) & ((q & 0x0000000000000001) == 0x0000000000000001))) % UInt64"
    , "    return q == 0x0020000000000000 ? (s, q >> 1, e + k + 1) : (s, q, e + k)"
    , "end"
    , "# Binary64 sum of two finite values, each with a significand of at most 53 bits."
    , "@inline function tl_sf_add(sa::UInt64, ma::UInt64, ea::Int, sb::UInt64, mb::UInt64, eb::Int)"
    , "    ma == 0x0000000000000000 && mb == 0x0000000000000000 && return (sa & sb, ma, 0)"
    , "    ma == 0x0000000000000000 && return tl_sf_round(sb, mb, eb)"
    , "    mb == 0x0000000000000000 && return tl_sf_round(sa, ma, ea)"
    , "    ka = leading_zeros(ma) - 2"
    , "    kb = leading_zeros(mb) - 2"
    , "    xa = ma << ka"
    , "    xb = mb << kb"
    , "    fa = ea - ka"
    , "    fb = eb - kb"
    , "    swap = (fb > fa) | ((fb == fa) & (xb > xa))"
    , "    sh = swap ? sb : sa"
    , "    xh = swap ? xb : xa"
    , "    fh = swap ? fb : fa"
    , "    sl = swap ? sa : sb"
    , "    xl = swap ? xa : xb"
    , "    fl = swap ? fa : fb"
    , "    dsh = fh - fl"
    , "    lo = dsh >= 62 ? 0x0000000000000001 :"
    , "        (xl >> dsh) | ((xl & ((0x0000000000000001 << dsh) - 0x0000000000000001)) != 0x0000000000000000) % UInt64"
    , "    sh == sl && return tl_sf_round(sh, xh + lo, fh)"
    , "    xh == lo && return (0x0000000000000000, 0x0000000000000000, 0)"
    , "    return tl_sf_round(sh, xh - lo, fh)"
    , "end"
    , "# Binary64 product of a significand below 2^24 and one below 2^53, both normalised first."
    , "@inline function tl_sf_mul(sf::UInt64, m1::UInt64, e1::Int, sd::UInt64, m2::UInt64, e2::Int)"
    , "    (m1 == 0x0000000000000000 || m2 == 0x0000000000000000) && return (sf ⊻ sd, 0x0000000000000000, 0)"
    , "    kf = leading_zeros(m1) - 40"
    , "    kd = leading_zeros(m2) - 11"
    , "    mf = m1 << kf"
    , "    md = m2 << kd"
    , "    ef = e1 - kf"
    , "    ed = e2 - kd"
    , "    ph = mf * (md >> 26)"
    , "    pl = mf * (md & 0x0000000003ffffff)"
    , "    q = ph + (pl >> 26)"
    , "    r = pl & 0x0000000003ffffff"
    , "    x = (q << 11) | (r >> 15) | ((r & 0x0000000000007fff) != 0x0000000000000000) % UInt64"
    , "    return tl_sf_round(sf ⊻ sd, x, ef + ed + 15)"
    , "end"
    , "# Round a binary64 value with a 53-bit significand to Float32, ties to even."
    , "@inline function tl_sf_narrow(s::UInt64, m::UInt64, e::Int)"
    , "    sbit = (s % UInt32) << 31"
    , "    m == 0x0000000000000000 && return reinterpret(Float32, sbit)"
    , "    top = e + 52"
    , "    q = top - 23 < -149 ? -149 : top - 23"
    , "    k = q - e"
    , "    n = 0x0000000000000000"
    , "    if k <= 60"
    , "        n = m >> k"
    , "        r = m & ((0x0000000000000001 << k) - 0x0000000000000001)"
    , "        h = 0x0000000000000001 << (k - 1)"
    , "        n += ((r > h) | ((r == h) & ((n & 0x0000000000000001) == 0x0000000000000001))) % UInt64"
    , "    end"
    , "    if n == 0x0000000001000000"
    , "        n = n >> 1"
    , "        q += 1"
    , "    end"
    , "    n < 0x0000000000800000 && return reinterpret(Float32, sbit | (n % UInt32))"
    , "    field = q + 150"
    , "    field >= 255 && return reinterpret(Float32, sbit | 0x7f800000)"
    , "    return reinterpret(Float32, sbit | ((field % UInt32) << 23) | ((n % UInt32) & 0x007fffff))"
    , "end"
    , "# a + f*(b - a) in binary64 arithmetic rounded once to Float32, using integers only."
    , "@inline function tl_lerp64(a::Float32, b::Float32, f::Float32)"
    , "    (isfinite(a) && isfinite(b)) || return a + f * (b - a)"
    , "    (sa, ma, ea) = tl_sf_split(a)"
    , "    (sb, mb, eb) = tl_sf_split(b)"
    , "    (sf, mf, ef) = tl_sf_split(f)"
    , "    (sd, md, ed) = tl_sf_add(sb, mb, eb, sa ⊻ 0x0000000000000001, ma, ea)"
    , "    (sp, mp, ep) = tl_sf_mul(sf, mf, ef, sd, md, ed)"
    , "    (sr, mr, er) = tl_sf_add(sa, ma, ea, sp, mp, ep)"
    , "    return tl_sf_narrow(sr, mr, er)"
    , "end" ]

/-- The `lutfetch` helper: `LutTable.refFetch`'s clamp/floor/lerp in binary64 over the flat
row-major table, rounded once to `T` — an empty table (`W == 0 || LAYERS == 0`) fetches `zero(T)`
as `refFetch` returns `0.0`. A NaN coordinate or layer returns NaN before the clamps, matching the
C stub and CUDA helper. The layer is clamped before it is truncated, so a huge finite layer cannot
overflow the index. Two methods give the same values: the generic one computes in `Float64`, and
the `Float32` one in `Float32` and integers (`softFloatJulia`), so it runs on a backend without
`Float64`. Point mode is the stub's arithmetic step for step; hardware mode emulates the 9-bit
weight, tolerance-only. Empty when the kernel uses no tables. -/
def lutHelperJulia (cg : JuliaCodegen) : String :=
  if cg.tables.isEmpty then "" else
  -- A weight that rounds to one is the next grid point at weight zero.
  let (quant, quant32) := match cg.lutMode with
    | .point => ("", "")
    | .hardware =>
      ( "    f = floor(f * 256.0 + 0.5) / 256.0\n    if f >= 1.0\n        j = j + 1.0\n        f = 0.0\n    end\n"
      , "    g = f * 256.0f0\n    gf = floor(g)\n    f = ifelse(g - gf >= 0.5f0, gf + 1.0f0, gf) / 256.0f0\n"
          ++ "    if f >= 1.0f0\n        j = j + 1.0f0\n        f = 0.0f0\n    end\n" )
  String.intercalate "\n"
    [ "@inline function tl_lutfetch(tab::AbstractVector{T}, W::Int, LAYERS::Int, layer32::T, u32::T) where {T<:AbstractFloat}"
    , "    (W == 0 || LAYERS == 0) && return zero(T)"
    , "    layer = Float64(layer32)"
    , "    u = Float64(u32)"
    , "    (isnan(layer) || isnan(u)) && return T(layer + u)"
    , "    wmax = Float64(W - 1)"
    , "    um = ifelse(wmax <= u, wmax, u)"
    , "    uc = ifelse(0.0 <= um, um, 0.0)"
    , "    lmax = Float64(LAYERS - 1)"
    , "    ls = layer + 0.5"
    , "    lm = ifelse(lmax <= ls, lmax, ls)"
    , "    lc = ifelse(0.0 <= lm, lm, 0.0)"
    , "    L = unsafe_trunc(Int, lc)"
    , "    j = floor(uc)"
    , s!"    f = uc - j\n{quant}    j0 = unsafe_trunc(Int, j)"
    , "    j1 = j0 + 1 < W ? j0 + 1 : W - 1"
    , "    base = L * W"
    , "    @inbounds a = Float64(tab[base + j0 + 1])"
    , "    @inbounds b = Float64(tab[base + j1 + 1])"
    , "    d = b - a"
    , "    fd = f * d"
    , "    return T(a + fd)"
    , "end"
    , softFloatJulia
    , "# The Float32 method: the same values with no Float64, for backends that lack it."
    , "@inline function tl_lutfetch(tab::AbstractVector{Float32}, W::Int, LAYERS::Int, layer::Float32, u::Float32)"
    , "    (W == 0 || LAYERS == 0) && return 0.0f0"
    , "    (isnan(layer) || isnan(u)) && return layer + u"
    , "    # The upper clamps compare integers: Float32(W - 1) is inexact above 2^24."
    , "    um = ifelse(4.6116860f18 <= u, 4.6116860f18, u)"
    , "    uc = ifelse(0.0f0 <= um, um, 0.0f0)"
    , "    lf = floor(layer)"
    , "    ls = ifelse(layer - lf >= 0.5f0, lf + 1.0f0, lf)"
    , "    lm = ifelse(4.6116860f18 <= ls, 4.6116860f18, ls)"
    , "    lc = ifelse(0.0f0 <= lm, lm, 0.0f0)"
    , "    L = min(unsafe_trunc(Int, lc), LAYERS - 1)"
    , "    j = floor(uc)"
    , s!"    f = uc - j\n{quant32}    j0 = unsafe_trunc(Int, j)"
    , "    if j0 >= W - 1"
    , "        j0 = W - 1"
    , "        f = 0.0f0"
    , "    end"
    , "    j1 = j0 + 1 < W ? j0 + 1 : W - 1"
    , "    base = L * W"
    , "    @inbounds a = tab[base + j0 + 1]"
    , "    @inbounds b = tab[base + j1 + 1]"
    , "    return tl_lerp64(a, b, f)"
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

/-- The binary alphabet: `cOp` computes the op and `jlExpr` renders it, for `add sub mul div pow min
max`. -/
theorem rendering_table_binary (i j : Nat) (x y : Float) :
    (cOp "add" [x, y] = .ok (x + y) ∧ (jlExpr "add" [i, j]).isOk) ∧
    (cOp "sub" [x, y] = .ok (x - y) ∧ (jlExpr "sub" [i, j]).isOk) ∧
    (cOp "mul" [x, y] = .ok (x * y) ∧ (jlExpr "mul" [i, j]).isOk) ∧
    (cOp "div" [x, y] = .ok (x / y) ∧ (jlExpr "div" [i, j]).isOk) ∧
    (cOp "pow" [x, y] = .ok (Float.pow x y) ∧ (jlExpr "pow" [i, j]).isOk) ∧
    (cOp "min" [x, y] = .ok (Min.min x y) ∧ (jlExpr "min" [i, j]).isOk) ∧
    (cOp "max" [x, y] = .ok (Max.max x y) ∧ (jlExpr "max" [i, j]).isOk) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The unary alphabet, likewise: `exp log sqrt abs`. -/
theorem rendering_table_unary (i : Nat) (x : Float) :
    (cOp "exp" [x] = .ok (Float.exp x) ∧ (jlExpr "exp" [i]).isOk) ∧
    (cOp "log" [x] = .ok (Float.log x) ∧ (jlExpr "log" [i]).isOk) ∧
    (cOp "sqrt" [x] = .ok (Float.sqrt x) ∧ (jlExpr "sqrt" [i]).isOk) ∧
    (cOp "abs" [x] = .ok (Float.abs x) ∧ (jlExpr "abs" [i]).isOk) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The Julia rendering and the C rendering agree on **where** they are defined, for every op name
and every parent list: both are printers of `SL.mkOp`, so an op has a Julia expression exactly when
it has a C one (the two emitters are twins over the one program, not two alphabets). -/
theorem jlExpr_isOk_eq_cExpr (nm : String) (ps : List Nat) :
    (jlExpr nm ps).isOk = (cExpr nm ps).isOk := by
  unfold jlExpr cExpr; cases SL.mkOp nm ps <;> rfl

/-- The binary alphabet, as the `#guard`s and the capstone chapter cite it. -/
theorem jlExpr_isOk_eq_cExpr_binary (i j : Nat) :
    (jlExpr "add" [i, j]).isOk = (cExpr "add" [i, j]).isOk ∧
    (jlExpr "sub" [i, j]).isOk = (cExpr "sub" [i, j]).isOk ∧
    (jlExpr "mul" [i, j]).isOk = (cExpr "mul" [i, j]).isOk ∧
    (jlExpr "div" [i, j]).isOk = (cExpr "div" [i, j]).isOk ∧
    (jlExpr "pow" [i, j]).isOk = (cExpr "pow" [i, j]).isOk ∧
    (jlExpr "min" [i, j]).isOk = (cExpr "min" [i, j]).isOk ∧
    (jlExpr "max" [i, j]).isOk = (cExpr "max" [i, j]).isOk :=
  ⟨jlExpr_isOk_eq_cExpr _ _, jlExpr_isOk_eq_cExpr _ _, jlExpr_isOk_eq_cExpr _ _,
   jlExpr_isOk_eq_cExpr _ _, jlExpr_isOk_eq_cExpr _ _, jlExpr_isOk_eq_cExpr _ _,
   jlExpr_isOk_eq_cExpr _ _⟩

/-- **The Julia kernel runs as the tape** — `SL.genSL_denotes` read through the printer: on a tape
the emitter accepts, the body lines are the program's lines printed, and the program runs as
`evalTapeT`. The Julia-specific content of this corollary is nil; that is the point. -/
theorem julia_body_denotes {tbls : Array LutTable} {tables : String → Option LutTable}
    (hT : SL.TablesAgree tbls tables) (env : String → Float) {t : CpuTape Float} {prog : SL.SLProg}
    (h : SL.genSL t tbls = .ok prog) :
    genBodyJulia t tbls = .ok (prog.zipIdx.map fun p => printLineJulia p.1 p.2) ∧
    evalTapeT tables env t = .ok (SL.run env prog) :=
  ⟨genBodyJulia_of_genSL h, SL.genSL_denotes hT env h⟩

/-- `min`/`max` as rendered are Lean's: the `Min Float`/`Max Float` instances are `Float.minimum` and
`Float.maximum`, the IEEE 754-2019 operations Julia's `min`/`max` and the C conditional compute. -/
theorem min_eq_minimum (x y : Float) : Min.min x y = Float.minimum x y := rfl

theorem max_eq_maximum (x y : Float) : Max.max x y = Float.maximum x y := rfl

end PropertyKindCalculus.Paradigm.TapeCodegen.Julia

end Blanket
