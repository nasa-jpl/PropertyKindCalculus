/-
`paradigm.batch_carrier` — **the CPU/GPU backend boundary as a PKC typeclass**, plus
coarse-grained pixel-axis `Task` parallelism for the CPU deployment.

WHY. The fit (`fit_tile`), dielectric, and retrieval kernels are already written once against
`[NumCarrier α]` — no per-pixel loop, no data branch. But the *deployment* apps
(`cli.tile_gpu`, `cli.tile_retrieve`) still name `CudaT` concretely in their plumbing:
constant lifting, host↔carrier marshaling, and the eager memory-discipline hooks. This class
hoists exactly that surface out of the apps, so they are written against `[BatchCarrier C]`
and never mention `CudaT`. The CPU/GPU distinction then lives ENTIRELY here — one instance
plus a build flag — not in the applications.

`runSharded` adds the CPU multicore lever: split the tile into contiguous pixel slices and
run the SAME whole-tile kernel on each slice on its own dedicated Lean `Task`. One fork per
chunk (not per op), so the whole op-chain runs per chunk — compute-per-fork is maximal and
per-op fork/join overhead is nil (the "maximize compute vs IO" granularity). Pixels are
independent, so this is exact. The GPU path is just `nChunks = 1` (one batch; the device
parallelizes internally). The `CudaT` CPU-stub ops are thread-safe — each allocates its own
output and shares no scratch (the CUDA scratch mutex is compiled only into the `.cu` build) —
so N chunks scale.

BUILD STATUS: additive module, NOT yet imported by any target. Wire it into the two apps
(replace `CudaT.const`/`.ofFloatArray`/`.toFloatArray` with the `BatchCarrier` projections,
and `Buffer.size`/`.release` in `fitAvsTR` with `BatchCarrier.liveSize`/`.release`), add
`[∀ s, NumCarrier (C s)] [BatchCarrier C]` to `run`/`fitAvsTR`, then
`lake build tile_gpu tile_retrieve` to verify before relying on it.
-/
import PropertyKindCalculus.Torch.Paradigm.CudaCarrier
import PropertyKindCalculus.Torch.Paradigm.Platform

open Spec
open PropertyKindCalculus.Paradigm (NumCarrier)
open PropertyKindCalculus.Paradigm.CudaCarrier (CudaT)
open Runtime.Autograd.Cuda (Buffer)

namespace PropertyKindCalculus.Paradigm

/-- A **batched numeric backend** `C : Shape → Type`: the host↔carrier marshaling and eager
memory-discipline hooks a whole-tile deployment needs, on top of the `[NumCarrier (C s)]`
arithmetic the kernels run through. GPU (`CudaT` under `-K cuda`) and CPU (`CudaT` stubs)
differ ONLY in this class; the fit/dielectric/retrieval kernels never name it.

Carriers must ALSO provide `[∀ s, NumCarrier (C s)]` (kept as a separate constraint rather
than bundled, so instance search stays simple). `CudaT` has both. -/
class BatchCarrier (C : Shape → Type) where
  /-- A uniform constant batch at shape `s` (every pixel the same value). -/
  const        : ∀ {s : Shape}, Float → C s
  /-- Marshal a host column (length `Shape.size s`) into the carrier. -/
  ofFloatArray : ∀ {s : Shape}, FloatArray → C s
  /-- Read a carrier batch back to a host column. -/
  toFloatArray : ∀ {s : Shape}, C s → FloatArray
  /-- Live storage measure of one batch — a non-zero liveness sentinel for the fit's
  degenerate-tile guard (`if touched == 0 then throw …`). Real element count on `CudaT`; a
  pure/GC carrier should return `Shape.size s` so the guard still discriminates. -/
  liveSize     : ∀ {s : Shape}, C s → UInt32 := fun _ => 0
  /-- Eagerly free a batch's storage, returning the amount reclaimed (0/no-op on GC-managed
  carriers; releases the device buffer on `CudaT`). -/
  release      : ∀ {s : Shape}, C s → UInt32 := fun _ => 0

/-- The GPU/CPU-stub carrier as a `BatchCarrier`. One instance for both builds — `-K cuda`
selects device vs host stub beneath the FFI. -/
instance : BatchCarrier CudaT where
  const        := fun v => CudaT.const v
  ofFloatArray := fun a => CudaT.ofFloatArray a
  toFloatArray := fun t => CudaT.toFloatArray t
  liveSize     := fun t => Buffer.size t.buf
  release      := fun t => Buffer.release t.buf

/-- **Fused forms** for a batched carrier (Layer 1) — a small, extensible family of *bit-exact
single-op replacements* for hot composed sub-expressions. A carrier-parametric `[NumCarrier α]` model
is a composition of primitive ops; where one composed shape is hot, a carrier can offer a **fused
form** it realizes as one device kernel (bit-identical to the composition, so it is a *refinement* of
the composed spec, not an approximation), and the model falls back to the plain `NumCarrier`
composition where no fused form is provided. This is the *targeted* companion to the general megakernel
codegen (`paradigm.tape_codegen`), which fuses the *whole* recorded model rather than one named shape.

Kept separate from `BatchCarrier` (general marshaling), **domain-neutral**, and **extensible**:
`scaledProdExp` (`exp(c·x·y)`) is the first form; the same pattern admits more as hot paths warrant —
e.g. `exp(a + c·x)` (affine exponent: Arrhenius, log-linear), `exp(−γ·x²)` (Gaussian / RBF),
`logSumExp`, `rsqrt`. A soil-moisture attenuation `exp(−2·b·ndvi)` is `scaledProdExp (−2) b ndvi`,
defined in the downstream science model (soil-moisture-model), not here. -/
class FusedExp (C : Shape → Type) where
  /-- The scaled product exponential `exp(c · x · y)` (left-associated) in one op — e.g. a Beer–Lambert
  two-way extinction `exp(−2·κ·ℓ)`. -/
  scaledProdExp : ∀ {s : Shape}, Float → C s → C s → C s

/-- `CudaT`'s scaled product exponential, via the portable `CudaT.scaledProdExp` (`exp(c·x·y)` composed
from the dual-backend device kernels): **one instance for both** the CPU-stub (`lake build`) and GPU
(`-K cuda`) builds, naming no CUDA-only symbol so the `Torch` library builds green without a GPU. A
`-K cuda` / deploy build may override `CudaT.scaledProdExp` with a single fused device kernel, a
bit-exact drop-in. -/
instance : FusedExp CudaT where
  scaledProdExp := fun c x y => CudaT.scaledProdExp c x y

namespace BatchCarrier

/-- Force the CPU-stub's one-time lazy init (external-class registration + the
deterministic-reductions flag) on the CURRENT thread, before any `Task` touches the backend,
so the benign first-use init races cannot fire during fan-out. A no-op cost on the GPU build.
The `IO.println` observing `a.size` keeps the pure warm-up call from being eliminated. -/
def warmup (C : Shape → Type) [BatchCarrier C] : IO Unit := do
  let a := BatchCarrier.toFloatArray (BatchCarrier.const (C := C) (s := Shape.dim 1 Shape.scalar) 0.0)
  IO.println s!"[batch] carrier warm ({a.size} elt)"

/-- The DEVICE capacity twin of `Platform.hostMemLimit` (`cudaMemGetInfo`, via the
allocator stats): what a batch-sizing decision may still claim on the current device.
`none` on the CPU stub, where there is no device and both counters read 0. Query AFTER
`warmup`: the CUDA context / library fixed tax is then already netted out of
`deviceFreeBytes`, so the answer needs no fixed-overhead model — solve the batch size
against it with the algorithm's per-pixel shape (`TapeCodegen.AiReport.fusedPeakBytes` /
`eagerPeakBytes`) and a safety factor for allocator fragmentation. -/
def deviceMemBudget : IO (Option Platform.MemBudget) := do
  let st ← Buffer.allocatorStats
  if st.deviceTotalBytes == 0 then return none
  return some { bytes := st.deviceFreeBytes.toNat, source := "cudaMemGetInfo:free" }

end BatchCarrier

/-! ### Coarse-grained, pixel-axis Task parallelism (the CPU deployment lever) -/

/-- Contiguous slice `a[lo:hi]` of a host column (its own copy, so tasks never share storage). -/
@[inline] def sliceFA (a : FloatArray) (lo hi : Nat) : FloatArray := Id.run do
  let mut r := FloatArray.emptyWithCapacity (hi - lo)
  for i in [lo:hi] do
    r := r.push (a[i]!)
  return r

/-- Append host columns end-to-end (chunk stitch). -/
@[inline] def concatFA (parts : Array FloatArray) : FloatArray := Id.run do
  let mut n := 0
  for p in parts do n := n + p.size
  let mut r := FloatArray.emptyWithCapacity n
  for p in parts do
    for i in [0:p.size] do r := r.push (p[i]!)
  return r

/--
Coarse-grained pixel-axis parallelism. Split each length-`total` input column into `nChunks`
contiguous slices, run the row-independent whole-tile kernel `k` on each slice — for
`nChunks > 1`, each on its own **dedicated** Lean `Task` (one thread per chunk, the whole
op-chain per chunk) — and concatenate the `nOut` per-chunk output columns.

`k len cols` receives a chunk's length and its sliced input columns and returns `nOut` output
columns of length `len`. `nChunks ≤ 1` runs `k` inline (the GPU path: one batch, the device
parallelizes internally). Rows (pixels) must be independent — which the AVS fit and the
Newton retrieval are. Call `BatchCarrier.warmup` once before this on the CPU build. -/
def runSharded (nChunks total nOut : Nat) (inCols : Array FloatArray)
    (k : Nat → Array FloatArray → IO (Array FloatArray)) : IO (Array FloatArray) := do
  if nChunks ≤ 1 then
    return (← k total inCols)
  let base := total / nChunks
  let rem  := total % nChunks
  -- spawn one dedicated task per contiguous chunk (dedicated ⇒ its own thread for CPU-bound work)
  let mut tasks : Array (Task (Except IO.Error (Array FloatArray))) := #[]
  let mut lo := 0
  for c in [0:nChunks] do
    let len := base + (if c < rem then 1 else 0)
    let hi := lo + len
    let slices := inCols.map (fun col => sliceFA col lo hi)
    let t ← IO.asTask (k len slices) Task.Priority.dedicated
    tasks := tasks.push t
    lo := hi
  -- gather in chunk order; propagate the first task error
  let mut chunkOuts : Array (Array FloatArray) := #[]
  for t in tasks do
    match t.get with
    | .ok cols => chunkOuts := chunkOuts.push cols
    | .error e => throw e
  -- stitch: output column j = its per-chunk slices concatenated in order
  let mut result : Array FloatArray := #[]
  for j in [0:nOut] do
    result := result.push (concatFA (chunkOuts.map (fun cols => cols[j]!)))
  return result

/-- `runSharded` with the shard count DECIDED rather than passed: `Platform.decideShards`
solves the algorithm's memory shape against THIS host's capacity (affinity/quota cores,
cgroup-aware memory budget), an explicit `override` (a `TILE_SHARDS`-style env contract)
winning verbatim when present. The decision — every term, with provenance — is announced on
one line before running, so an OOM-kill or an idle machine is diagnosable from the log
alone. `reservedBytes` is what the caller already holds regardless of the count (input
columns, outputs to be stitched); the shard count is additionally capped at `total` (a
shard needs at least one element). Returns the outputs and the decision, so callers can
report the count they actually ran. -/
def runShardedAuto (shape : Platform.MemShape) (total nOut : Nat)
    (inCols : Array FloatArray) (k : Nat → Array FloatArray → IO (Array FloatArray))
    (override : Option Nat := none) (reservedBytes : Nat := 0) :
    IO (Array FloatArray × Platform.ShardDecision) := do
  let d ← Platform.decideShards shape total reservedBytes override (hardCap := some total)
  IO.println s!"[batch] {d.describe}"
  let outs ← runSharded d.nShards total nOut inCols k
  return (outs, d)

end PropertyKindCalculus.Paradigm
