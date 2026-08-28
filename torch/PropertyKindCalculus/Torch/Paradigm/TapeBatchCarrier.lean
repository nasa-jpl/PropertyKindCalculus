/-
`paradigm.tape_batch_carrier` — the **`BatchCarrier` instance for the tape carrier**, so a whole-tile
deployment written against `[BatchCarrier C]` can be instantiated at `C := TapeBuilder` to *record*
(rather than run) its constant-lifting and host marshaling. Together with `paradigm.batch_carrier`'s
`CudaT` instance this gives `BatchCarrier` instances for **both** the executing carrier (CudaT — GPU
device / CPU stub by `-K cuda`) and the recording carrier (TapeBuilder).

The load-bearing field is `const`: it lets a fit's arbitrary-`Float` loop constants — the
Levenberg–Marquardt `λ` schedule and the box bounds `lb`/`ub` — enter a recording as baked constant
leaves (`TapeBuilder.const`, an unnamed `fill`-leaf), the one thing `NumCarrier` (offering only
`0`/`1`/`Nat` literals) cannot express. `ofFloatArray`/`toFloatArray` complete the instance honestly —
a recording bakes a host column as a data leaf, and reads one back by forcing the deferred program
through the reference `Float` interpreter — but a megakernel *compiles* a recording rather than
marshaling data through it, so only `const` is exercised by the codegen demos. `liveSize` reports the
shape size (a pure/GC carrier's non-zero liveness sentinel) and `release` is a no-op.

Plain (not a `module`) file: imports the tape carrier and the `BatchCarrier` class.
-/
import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
import PropertyKindCalculus.Torch.Paradigm.BatchCarrier

open Spec
open Runtime.Autograd (Tape TapeM)

namespace PropertyKindCalculus.Paradigm

/-- Distribute a flat, row-major host column across shape `s`, reading from offset `off` (the pure
`Tensor` analogue of `CudaT.ofFloatArray`; out-of-range reads fall back to `0.0`). -/
def TapeBuilder.tensorOfFloatArray : (s : Shape) → FloatArray → Nat → Tensor Float s
  | Shape.scalar,   a, off => Tensor.scalar (a[off]?.getD 0.0)
  | Shape.dim n s', a, off => Tensor.dim (fun i : Fin n =>
      TapeBuilder.tensorOfFloatArray s' a (off + i.val * Shape.size s'))

/-- **The tape carrier as a `BatchCarrier`.** `const` records an arbitrary host scalar as a baked
constant leaf — the load-bearing field, supplying a recording's `λ` schedule and box bounds.
`ofFloatArray` bakes a whole host column as a data leaf; `toFloatArray` forces the builder through
the reference `Float` interpreter and reads its result column (a recording is normally *compiled*,
not read back, so these two are honest completions rather than the intended deployment path). -/
instance instBatchCarrier : BatchCarrier TapeBuilder where
  const        := fun v => TapeBuilder.const v
  ofFloatArray := fun {s} a => ⟨TapeM.leaf (TapeBuilder.tensorOfFloatArray s a 0) (name := none)⟩
  toFloatArray := fun {s} b =>
    match TapeM.run Tape.empty b.run with
    | .ok (id, t) =>
        match t.nodes[id]? with
        | some node => (Spec.Tensor.toList node.value.tensor).foldl (fun acc x => acc.push x)
                          (FloatArray.emptyWithCapacity (Shape.size s))
        | none      => FloatArray.emptyWithCapacity 0
    | .error _  => FloatArray.emptyWithCapacity 0
  liveSize     := fun {s} _ => (Shape.size s).toUInt32
  release      := fun _ => 0

/-- Self-check: `BatchCarrier.const` at the tape carrier elaborates to a scalar `TapeBuilder`, i.e. the
arbitrary-`Float` constant-injection a recorded fit's loop constants need. -/
example : BatchCarrier.const (C := TapeBuilder) (s := Shape.scalar) 0.03 = TapeBuilder.const 0.03 := rfl

end PropertyKindCalculus.Paradigm
