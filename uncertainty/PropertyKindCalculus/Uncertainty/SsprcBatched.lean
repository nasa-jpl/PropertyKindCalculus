/-
`PropertyKindCalculus.Uncertainty.SsprcBatched` — the **batched SSPRC propagator** over the `CudaT`
carrier (Stage 4 of `UNCERTAINTY.md`, "Scale").

The Stage-2 `Ssprc.run` evaluates each input's deviation distribution by *mapping the scalar model*
over its `Nᵢ` systematic samples — `Nᵢ` scalar model calls per input ([`Ssprc.deviationDist`]).
This module runs the *same* write-once `[NumCarrier α]` kernel at `α := CudaT (Shape.dim Nᵢ .scalar)`
instead: input `i`'s `Nᵢ` systematic samples become **one length-`Nᵢ` batch tensor**, the other
inputs broadcast constants at their means, and the whole model op-chain is **one batched launch** —
on a `-K cuda` build one GPU kernel per elementwise op, on the default build the portable CPU-stub
buffers (so this is exercised, and parity-checked, *without a GPU*). The per-input moments `E(Aᵢ)`,
`Var(Aᵢ)` are read with `Buffer.reduceMean` (the one reduction `NumCarrier`'s branchless-elementwise
interface deliberately does not carry), and `E(Y)` / `u(Y)` combine exactly as in `Ssprc.run` (means
and variances add under convolution: `E(Y) = R + Σ E(Aᵢ)`, `Var(Y) = Σ Var(Aᵢ)`).

⚠️ **Build note (how the batched numbers are verified).** `CudaT`'s device ops are `@[extern]` FFI
with no interpreter fallback, so a `#guard`/`#eval` of a `CudaT` value cannot run at *build* time —
the elaborator has no native `CudaT` symbols, and the TorchLean dependency graph cannot be
`precompileModules`-loaded into it (upstream `ProofWidgets`/`QuantumInfo` `:shared` facets do not
build). This module therefore only *typechecks* under `lake build` (it lives in the small
`UncertaintyBatch` library); its numbers are checked by a compiled executable —
`lake exe ssprc_batched_parity` (`apps/`) — which links the native `CudaT` code directly and asserts
parity with the scalar `Ssprc.run` (the portable CPU stub on the default build, the device on a
`-K cuda=true` container build).
-/
import PropertyKindCalculus.Uncertainty.Ssprc
import PropertyKindCalculus.Uncertainty.Carriers
import PropertyKindCalculus.Torch.Paradigm.CudaCarrier

namespace PropertyKindCalculus.Uncertainty.SsprcBatched

open Spec TorchLean
open PropertyKindCalculus.Paradigm (NumCarrier)
open PropertyKindCalculus.Paradigm.CudaCarrier (CudaT)
open Runtime.Autograd.Cuda (Buffer)
open PropertyKindCalculus.Uncertainty (InputDist)

/-- A write-once carrier-polymorphic scalar kernel as the propagators consume it: `List α → α` for
any `[NumCarrier α]`. At `α := Float` it is the scalar reference the Stage-2 `Ssprc.run` runs; at
`α := CudaT (Shape.dim N .scalar)` it evaluates all `N` samples in one op-chain. -/
abbrev BatchModel := {α : Type} → [NumCarrier α] → List α → α

/-- `List Float → FloatArray` — a host input column ready to upload. -/
def colOf (xs : List Float) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity xs.length
  for x in xs do a := a.push x
  return a

/-- Read a batched carrier value's mean reduction back to a host scalar (`reduceMean` returns a
length-1 buffer). -/
@[inline] def reduceMeanF {s : Shape} (t : CudaT s) : Float :=
  (Buffer.toFloatArray (Buffer.reduceMean t.buf))[0]!

/-- The two batched moments `(E[f], E[f²])` over the batch that produced `f` — from one launch each,
the raw material every propagator combines into `(E, Var)`. -/
@[inline] def batchMoments {s : Shape} (f : CudaT s) : Float × Float :=
  (reduceMeanF f, reduceMeanF (f * f))

/-- **Batched SSPRC** — `Ssprc.run` with every per-input deviation distribution evaluated in one
batched `CudaT` launch instead of `Nᵢ` scalar model calls. Reads `(E(Y), u(Y))` from the per-input
batched moments exactly as `Ssprc.run` does. -/
def run (model : BatchModel) (inputs : List (InputDist Float)) (ns : List Nat) : Float × Float :=
  let means := inputs.map (fun d => d.moments.mean)
  let R := model (α := Float) means
  Id.run do
    let mut eY := R
    let mut varY : Float := 0.0
    for i in [0:inputs.length] do
      match inputs[i]?, ns[i]? with
      | some d, some n =>
        let s : Shape := Shape.dim n Shape.scalar
        -- input i = its N systematic samples (one batch column); the others = constants at their means
        let samples : CudaT s := CudaT.ofFloatArray (colOf (Ssprc.systematicSamples d n))
        let cols : List (CudaT s) := (List.range inputs.length).map (fun j =>
          if j == i then samples else CudaT.const (means[j]!))
        -- one batched op-chain over all N samples of input i
        let (mf, msq) := batchMoments (model cols)
        eY := eY + (mf - R)               -- E(Aᵢ) = E[f over input i] − R
        varY := varY + (msq - mf * mf)    -- Var(Aᵢ) = E[f²] − E[f]²
      | _, _ => pure ()
    return (eY, Float.sqrt varY)

end PropertyKindCalculus.Uncertainty.SsprcBatched
