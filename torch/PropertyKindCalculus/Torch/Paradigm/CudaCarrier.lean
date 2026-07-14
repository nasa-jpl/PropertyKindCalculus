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
import PropertyKindCalculus.Paradigm.NumCarrier
import PropertyKindCalculus.Torch.Paradigm.NumCarrierContext
import NN.Tensor
import NN.Runtime.Autograd.Engine.Cuda.Buffer

open Spec
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

/-! ### Host ↔ device bridges (for building inputs and reading results) -/

/-- Upload a host `FloatArray` of length `Shape.size s` as a device buffer. -/
@[inline] def ofFloatArray (a : FloatArray) : CudaT s := ⟨Buffer.ofFloatArray a⟩

/-- Download the device buffer to a host `FloatArray`. -/
@[inline] def toFloatArray (a : CudaT s) : FloatArray := Buffer.toFloatArray a.buf

/-- A constant batch (every pixel the same value). -/
@[inline] def const (v : Float) : CudaT s := ⟨Buffer.full (szU s) v⟩

end CudaT
end PropertyKindCalculus.Paradigm.CudaCarrier
