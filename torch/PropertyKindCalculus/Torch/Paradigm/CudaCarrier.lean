/-
`paradigm.cuda_carrier` — **the GPU carrier: `NumCarrier (CudaT s)` over TorchLean's CUDA buffers.**

The whole point of writing the fit against `[NumCarrier α]` (no per-pixel loop, no data branch) is that a
*new carrier* makes the same source run on new hardware with no algorithm change. The carriers that shipped
are all CPU: `Float` (scalar), `Tensor Float s` (eager `Spec`), `TapeBuilder s` (the recording tape). This
file adds the missing **GPU** carrier so `fit_tile.lmStep` / `avs_batch` / `spd_solve` run on the device.

It is an *eager* carrier: `CudaT s` wraps a TorchLean `Cuda.Buffer` (a contiguous float32 device buffer of
`Shape.size s` elements), and each `NumCarrier` operation is the corresponding pure device kernel
(`Buffer.{add,sub,mul,div,exp,sqrt,abs,log,min,max}` from `NN.Runtime.Autograd.Engine.Cuda.Buffer`). Those
ops are pure `opaque Buffer → Buffer`, so they satisfy `NumCarrier`'s total interface directly, and `Buffer`
carries a GC finalizer (`lean_register_external_class` → `cudaFree`), so eager intermediates free
automatically — no manual release, bounded peak memory. Under a plain `lake build` the same ops are the CPU
*stub* buffers, so this carrier also runs (and is parity-checked) without a GPU.

The AVS fit's transcendental surface is just `exp` (Mironov forward) and `sqrt` (Cholesky); it never calls
`sin/cos/tanh/cosh/sinh` (those live in the dielectric stage, not the Stage-2 fit). Those `MathFunctions`
fields are therefore provided as loud `panic!` stubs — present to satisfy the class, never reached by the
fit. (Add the real device kernels if a future kernel needs them.)
-/

module

public import PropertyKindCalculus.Paradigm.NumCarrier
public import PropertyKindCalculus.Torch.Paradigm.NumCarrierContext
public import NN.Tensor
public import NN.Runtime.Autograd.Engine.Cuda.Buffer
public import NN.Runtime.Autograd.Engine.Cuda.Kernels

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Spec TorchLean
open PropertyKindCalculus.Paradigm (NumCarrier)
open Runtime.Autograd.Cuda (Buffer)

namespace PropertyKindCalculus.Paradigm.CudaCarrier

/-- A length-`Shape.size s` float32 **device buffer** — the GPU carrier element. -/
structure CudaT (s : Shape) where
  buf : Buffer

namespace CudaT
variable {s : Shape}

/-- The element count of the batch as a `UInt32` (the buffer length). -/
@[inline] def szU (s : Shape) : UInt32 := (Shape.size s).toUInt32

instance : Add (CudaT s) := ⟨fun a b => ⟨Buffer.add a.buf b.buf⟩⟩
instance : Sub (CudaT s) := ⟨fun a b => ⟨Buffer.sub a.buf b.buf⟩⟩
instance : Mul (CudaT s) := ⟨fun a b => ⟨Buffer.mul a.buf b.buf⟩⟩
instance : Div (CudaT s) := ⟨fun a b => ⟨Buffer.div a.buf b.buf⟩⟩
instance : Min (CudaT s) := ⟨fun a b => ⟨Buffer.min a.buf b.buf⟩⟩
instance : Max (CudaT s) := ⟨fun a b => ⟨Buffer.max a.buf b.buf⟩⟩
instance : Zero (CudaT s) := ⟨⟨Buffer.zeros (szU s)⟩⟩
instance : One (CudaT s) := ⟨⟨Buffer.full (szU s) 1.0⟩⟩
instance : Coe Nat (CudaT s) := ⟨fun n => ⟨Buffer.full (szU s) n.toFloat⟩⟩
instance : Inhabited (CudaT s) := ⟨⟨Buffer.zeros (szU s)⟩⟩

instance : MathFunctions (CudaT s) where
  exp  := fun a => ⟨Buffer.exp a.buf⟩
  sqrt := fun a => ⟨Buffer.sqrt a.buf⟩
  abs  := fun a => ⟨Buffer.abs a.buf⟩
  log  := fun a => ⟨Buffer.log a.buf⟩
  pi   := ⟨Buffer.full (szU s) 3.141592653589793⟩
  sin  := fun _ => panic! "CudaT.sin: not a device kernel (the AVS fit uses no trig)"
  cos  := fun _ => panic! "CudaT.cos: not a device kernel (the AVS fit uses no trig)"
  tanh := fun _ => panic! "CudaT.tanh: not a device kernel (the AVS fit uses no trig)"
  cosh := fun _ => panic! "CudaT.cosh: not a device kernel (the AVS fit uses no trig)"
  sinh := fun _ => panic! "CudaT.sinh: not a device kernel (the AVS fit uses no trig)"

/-- The GPU carrier: the same branchless `+ − × ÷ min max exp sqrt` surface, on the device. -/
instance : NumCarrier (CudaT s) where

/-! ### Indexing (the one non-elementwise op this carrier exposes) -/

/-- **Gather** `Shape.size t` scalars from a length-`Shape.size s` device buffer at HOST indices
— `NN.Runtime.Autograd.Engine.Cuda.Kernels.Buffer.gatherVec`
(`torchlean_cuda_buffer_gather_vec`), one import away and already backed by both a real CUDA
kernel and a CPU parity stub, exactly the same "portable stub behind the same extern symbol"
shape every other op in this file already has — no new native code lands here, only a new Lean
name for an FFI TorchLean already ships. Indices are HOST data (a plain `Array Nat`), not a
second `CudaT` operand: the index computation itself is non-differentiable, data-dependent
control flow that stays off-device, the same division of labor
`NN.Runtime.Autograd.Engine.Cuda.Ops.Indexing`'s own tape wrappers already draw ("Indices are
non-differentiable and remain on the host"). `indices.size = Shape.size t` is UNCHECKED by this
wrapper — the same "caller's own responsibility" convention `ofFloatArray` already carries for
its own length match — and the underlying kernel "totalizes representable out-of-bounds indices
to 0" rather than faulting (`Kernels.gatherVec`'s own docstring), so a caller that wants an
exact index-out-of-range result (rather than silently reading element `0`) must route those
indices to a sentinel it controls, not rely on the kernel to refuse them. -/
@[inline] def gather {t : Shape} (src : CudaT s) (indices : Array Nat) : CudaT t :=
  ⟨Buffer.gatherVec src.buf (szU s) indices (szU t)⟩

/-! ### Host ↔ device bridges (for building inputs and reading results) -/

/-- Upload a host `FloatArray` of length `Shape.size s` as a device buffer. -/
@[inline] def ofFloatArray (a : FloatArray) : CudaT s := ⟨Buffer.ofFloatArray a⟩

/-- Download the device buffer to a host `FloatArray`. -/
@[inline] def toFloatArray (a : CudaT s) : FloatArray := Buffer.toFloatArray a.buf

/-- A constant batch (every pixel the same value). -/
@[inline] def const (v : Float) : CudaT s := ⟨Buffer.full (szU s) v⟩

/-- **Scaled product exponential** `exp(c · x · y)` (left-associated, `exp((c·x)·y)`) — a *fused form*
(`paradigm.batch_carrier`'s `FusedExp`) a batched deployment can request. Domain-neutral: it names no
problem domain, yet a soil-moisture two-way vegetation attenuation `exp(−2·b·ndvi)` is one instance
(`c = −2`, `x = b`, `y = ndvi`), as is a Beer–Lambert two-way extinction `exp(−2·κ·ℓ)`. This dispatches
to TorchLean's **single fused device kernel** `Buffer.scaledProdExp` (one launch instead of the four
`full`/`mul`/`mul`/`exp` ops), which the pinned `combined` now carries. That extern has **both** a CUDA
kernel and a portable C stub behind the same symbol (`torchlean_cuda_buffer_scaled_prod_exp`), so the
`Torch` library still builds green on **both** the CPU-stub (plain `lake build`) and the GPU (`-K cuda`)
build — no GPU required. The fused kernel is bit-identical to the same `exp((c·x)·y)` composed through
the `NumCarrier` ops (*same left-association*, verified when the op landed in TorchLean), so it stays an
exact twin of a composed `exp((c·x)·y)` (e.g. `avs_batch.attenuation`), not merely a close one. -/
@[inline] def scaledProdExp (c : Float) (x y : CudaT s) : CudaT s :=
  ⟨Buffer.scaledProdExp x.buf y.buf c⟩

end CudaT
end PropertyKindCalculus.Paradigm.CudaCarrier

end -- pkc-blanket-expose
end -- pkc-blanket
