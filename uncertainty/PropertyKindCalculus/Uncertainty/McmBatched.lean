/-
`PropertyKindCalculus.Uncertainty.McmBatched` — the **batched Monte Carlo propagator** over the
`CudaT` carrier (Stage 4 of `UNCERTAINTY.md`, "Scale").

The Stage-0 `Mcm.run` is the reference method: draw `n` joint samples of the inputs, push each
through the scalar model, report the sample mean and standard uncertainty — `n` scalar model calls.
This module runs the *same* write-once `[NumCarrier α]` kernel at
`α := CudaT (Shape.dim n .scalar)` instead: each input's `n` draws become one length-`n` batch
tensor, and the whole model op-chain is **one batched launch** for the entire propagation.

**MCM batches more cleanly than SSPRC does, and it is worth saying why.** `SsprcBatched` needs one
launch *per input*, because SSPRC's whole construction is per-input: input `i`'s deviation
distribution is what you get by varying `i` alone with the others held at their means, so each input
needs its own batch with its own broadcast constants. MCM samples the joint directly — every input
varies in every draw — so there is nothing to hold fixed and nothing to iterate over. One launch
carries all `n` draws of all inputs, and the two moments come off it with two reductions.

**Parity is exact-by-construction on the draw order, which is what makes the check meaningful.**
`Mcm.run` advances a single PRNG state and, within each draw, samples the inputs in order. So the
`k`-th entry of input `i`'s column is the `(k · m + i)`-th draw of that same stream, for `m` inputs.
`sampleColumns` reproduces exactly that interleaving rather than filling each column from its own
stream — which would be an equally valid Monte Carlo and would make the parity harness compare two
different experiments, hiding any structural bug behind sampling noise.

⚠️ **Build note (how the batched numbers are verified).** As for `SsprcBatched`: `CudaT`'s device
ops are `@[extern]` FFI with no interpreter fallback, so a `#guard`/`#eval` of a `CudaT` value cannot
run at *build* time. This module therefore only *typechecks* under `lake build` (it lives in the
small `UncertaintyBatch` library); its numbers are checked by a compiled executable —
`lake exe mcm_batched_parity` (`apps/`) — which links the native `CudaT` code directly and asserts
parity with the scalar `Mcm.run` (the portable CPU stub on the default build, the device on a
`-K cuda=true` container build).
-/

module

public import PropertyKindCalculus.Uncertainty.Mcm
public import PropertyKindCalculus.Uncertainty.SsprcBatched

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty.McmBatched

open Spec TorchLean
open PropertyKindCalculus.Paradigm (NumCarrier)
open PropertyKindCalculus.Paradigm.CudaCarrier (CudaT)
open PropertyKindCalculus.Uncertainty (InputDist)
open PropertyKindCalculus.Uncertainty.SsprcBatched (BatchModel colOf batchMoments)

/-- **The `n` joint draws, transposed into one column per input.**

The draw order is `Mcm.run`'s: one PRNG state, advanced input-by-input within each draw. Column `i`
therefore holds draws `i`, `m + i`, `2m + i`, … of that stream, so the batched propagator sees the
*same* `n` joint samples the scalar one does, and a parity check compares two evaluations of one
experiment rather than two experiments. -/
def sampleColumns (inputs : List (InputDist Float)) (n : Nat) (seed : UInt64) :
    Array (Array Float) := Id.run do
  let m := inputs.length
  let mut cols : Array (Array Float) := Array.replicate m (Array.emptyWithCapacity n)
  let mut st := seed
  for _ in [0:n] do
    for i in [0:m] do
      match inputs[i]? with
      | some d =>
        let (x, st') := Mcm.sampleOne st d
        st := st'
        cols := cols.set! i ((cols[i]!).push x)
      | none => pure ()
  return cols

/-- **Batched MCM** — `Mcm.run` with all `n` joint draws evaluated in one batched `CudaT` launch
instead of `n` scalar model calls. `E(Y)` and `u(Y)` are read from the batch's two moments exactly
as the scalar loop reads them from its running sums: `u(Y)² = E[Y²] − E[Y]²`, the population
variance, not the sample one. -/
def run (model : BatchModel) (inputs : List (InputDist Float)) (n : Nat) (seed : UInt64) :
    Float × Float :=
  let s : Shape := Shape.dim n Shape.scalar
  let cols := sampleColumns inputs n seed
  let ts : List (CudaT s) :=
    (List.range inputs.length).map (fun i => CudaT.ofFloatArray (colOf (cols[i]!).toList))
  let (mf, msq) := batchMoments (model ts)
  (mf, Float.sqrt (msq - mf * mf))

end PropertyKindCalculus.Uncertainty.McmBatched

end -- pkc-blanket-expose
end -- pkc-blanket
