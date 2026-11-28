/-
# Validation probes — the sharing tape carrier records what `cseCompact` leaves

Value probes for `PropertyKindCalculus.Torch.Paradigm.TapeSharedCarrier`. One kernel, written
once over the carrier classes, is recorded twice: at `TapeBuilder` then `cseCompact`, and at
`SharedTapeBuilder`. The two tapes must agree node for node (name, operands, value bits) and at
the output ids. The kernel reuses sub-expressions, so the `TapeBuilder` recording is larger than
its DAG and the comparison is not vacuous.

`PropertyKindCalculus.Examples.TapeSharedCse` proves this agreement for this kernel
(`kernel_shares_record`); the probes here show the comparison is not vacuous.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeSharedCarrier
meta import PropertyKindCalculus.Torch.Paradigm.TapeSharedCarrier

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.TapeShared

open TorchLean
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)

/-- A four-entry, two-layer table for the fetch probe. -/
def tbl : LutTable := { name := "probe", width := 2, layers := 2, values := #[0.0, 1.0, 2.0, 4.0] }

/-- A kernel that reuses every intermediate: two outputs over two inputs, naming each op of the
carrier alphabet (`+ - * /`, `^`, `min`/`max`, `fmin`/`fmax`, `sqrt`/`exp`/`log`/`abs`, a constant,
a `Nat` literal, a table fetch), and `min p p` / `max q q` on one shared node. -/
def kernel {C : Shape → Type} [BatchCarrier C] [∀ s, NumCarrier (C s)] [∀ s, LutInterp (C s)]
    (x y : C Shape.scalar) : C Shape.scalar × C Shape.scalar :=
  let k : C Shape.scalar := BatchCarrier.const 0.25
  let p := x * y + k
  let q := MathCarrier.sqrt (p * p + (2 : Nat))
  let r := BatchCarrier.fmin (BatchCarrier.fmax (q - p) k) (Max.max p (Min.min q x))
  let e := MathCarrier.exp (r / q) + MathCarrier.log q + MathCarrier.abs (r - q) + q ^ r
  let f := LutInterp.lutFetch tbl (Min.min k 1) (r * k)
  (e * e + r * q + f, (e + r) * (e + r) * p + f * f + Min.min p p + Max.max q q)

def xv : Tensor Float Shape.scalar := Tensor.full Shape.scalar 1.5
def yv : Tensor Float Shape.scalar := Tensor.full Shape.scalar (-0.75)

/-- A tape as comparable data: each node's name, operands and value bits. -/
def nodes (t : CpuTape Float) : Array (Option String × Array Nat × List UInt64) :=
  t.nodes.map (TapeCSE.nodeKey #[])

/-- The `TapeBuilder` recording: raw node count, the compacted tape, the remapped output ids. -/
def unshared : Except String (Nat × CpuTape Float × List Nat) := do
  let o := kernel (C := TapeBuilder) ⟨TapeM.leaf xv (name := some "x")⟩
    ⟨TapeM.leaf yv (name := some "y")⟩
  let (ids, t) ← TapeM.run Tape.empty (TapeBuilder.runAll [o.1, o.2])
  let (t', remap) := cseCompact t
  pure (t.size, t', ids.map (fun i => remap.getD i i))

/-- The `SharedTapeBuilder` recording. -/
def shared : Except String (CpuTape Float × List Nat) := do
  let o := kernel (C := SharedTapeBuilder) (SharedTapeBuilder.input "x" xv)
    (SharedTapeBuilder.input "y" yv)
  let (ids, t) ← SharedTapeM.record (SharedTapeBuilder.runAll [o.1, o.2])
  pure (t, ids)

/-- Both recordings succeed and give the same tape and the same output ids. -/
def agree : Bool :=
  match unshared, shared with
  | .ok (_, t, ids), .ok (t', ids') => nodes t == nodes t' && ids == ids'
  | _, _ => false

#guard agree

/-- A scalar and a one-element vector with the same name and value bits stay two leaves, each
with its own shape. -/
def mixedShapes : Except String (List Nat × List Shape) := do
  let (ids, t) ← SharedTapeM.recordRaw (do
    let a ← SharedTapeM.leaf (Tensor.full Shape.scalar (1.5 : Float)) (name := some "v")
    let b ← SharedTapeM.leaf (Tensor.full [1] (1.5 : Float)) (name := some "v")
    let c ← SharedTapeM.leaf (Tensor.full Shape.scalar (1.5 : Float)) (name := some "v")
    pure [a, b, c])
  pure (ids, t.nodes.toList.map (·.value.shape))

#guard mixedShapes == .ok ([0, 1, 0], [Shape.scalar, [1]])

/-- `record` rejects an input name that holds two tensors; one input used twice is accepted. -/
def nameGuard (y : Float) : Bool :=
  match SharedTapeM.record (do
    let a ← SharedTapeM.leaf (Tensor.full Shape.scalar (1.5 : Float)) (name := some "v")
    let b ← SharedTapeM.leaf (Tensor.full Shape.scalar y) (name := some "v")
    pure [a, b]) with
  | .ok _ => true
  | .error _ => false

#guard nameGuard 1.5 && !nameGuard 2.5
#guard (SharedTapeM.record (do
    let _ ← SharedTapeM.leaf (Tensor.full Shape.scalar (1.5 : Float)) (name := some "v")
    SharedTapeM.leaf (Tensor.full [1] (1.5 : Float)) (name := some "v"))).toOption.isNone

-- `un` and `bin` refuse an op of the other arity, before running an operand.
#guard match SharedTapeM.record (SharedTapeBuilder.un .add
    (SharedTapeBuilder.unsupported (s := Shape.scalar) "x")).run with
  | .error e => e == "SharedTapeBuilder.un: a binary op"
  | .ok _ => false
#guard (SharedTapeM.record (SharedTapeBuilder.un .add
    (SharedTapeBuilder.const (s := Shape.scalar) 1)).run).toOption.isNone
#guard (SharedTapeM.record (SharedTapeBuilder.bin .exp (SharedTapeBuilder.const (s := Shape.scalar) 1)
    (SharedTapeBuilder.const 2)).run).toOption.isNone

-- Not vacuous: the unshared recording is several times its DAG, and compaction removes nothing
-- from the shared one.
#guard match unshared, shared with
  | .ok (raw, t, _), .ok (t', _) =>
      raw > 4 * t.size && (cseCompact t').1.size == t'.size && t'.size > 20
  | _, _ => false

end PropertyKindCalculus.Tests.TapeShared

end Blanket
