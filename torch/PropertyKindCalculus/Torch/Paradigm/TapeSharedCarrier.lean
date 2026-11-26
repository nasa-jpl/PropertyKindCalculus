/-
`paradigm.tape_shared_carrier` — the **sharing tape carrier** `SharedTapeBuilder s`: a recording
carrier that emits each distinct sub-expression once.

`TapeBuilder` re-emits a sub-expression at every reference, so a kernel with heavy reuse unfolds
to its expression tree before `cseCompact` can collapse it (one trust-region fit step: tens of
millions of nodes for a few hundred distinct ones). `SharedTapeBuilder` applies the `cseCompact`
key *while recording*: the recording state carries a table from `(op name, operand ids)` to the
node that holds it (leaves: name and value bits), and an op whose key is present returns that
node instead of appending one. The tape stays the size of the DAG.

WHAT IS AND IS NOT PROVED. The `paradigm.tape_parity` theorems are stated for `TapeBuilder` and
do not mention this carrier. The link is the claim that recording a kernel here yields the tape
`cseCompact` yields from its `TapeBuilder` recording; it is checked by `#guard` on kernels small
enough to unfold (`Tests.Torch.TapeShared`), not proved.

COST. Memory is bounded by the DAG; time is not: a shared sub-expression is still *visited* once
per reference (each visit is a table lookup).

A `module` file: imports the tape carriers, the CSE key and the LUT vocabulary.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeBatchCarrier
public import PropertyKindCalculus.Torch.Paradigm.TapeCse
public import PropertyKindCalculus.Torch.Paradigm.LutCarrier
public import Std.Data.HashMap

@[expose] public section Blanket

open TorchLean
open FloatLib.Numerics (MathFunctions)

namespace PropertyKindCalculus.Paradigm

/-- The sharing recorder's state: the tape, and the nodes already on it by key. -/
structure SharedTape where
  tape   : CpuTape Float := Tape.empty
  /-- Op nodes by `(name, operand ids)`. -/
  ops    : Std.HashMap (String × Array Nat) Nat := {}
  /-- Leaves by `(name, value bits)`. -/
  leaves : Std.HashMap (Option String × List UInt64) Nat := {}

/-- The sharing recording monad. -/
abbrev SharedTapeM : Type → Type := StateT SharedTape Result

namespace SharedTapeM

/-- Run a recording program from the empty tape; yields its result and the recorded tape. -/
def record {β : Type} (m : SharedTapeM β) : Result (β × CpuTape Float) := do
  let (b, st) ← StateT.run m {}
  pure (b, st.tape)

/-- Record the op `name` on operands `ps` with `raw`, or return the node already holding it.
`name` must be the name `raw` gives its node. -/
def op (name : String) (ps : Array Nat) (raw : TapeM Float Nat) : SharedTapeM Nat := fun st =>
  -- Take the state apart so the tape stays unshared and `raw` pushes in place.
  let ⟨tape, ops, leaves⟩ := st
  match ops[(name, ps)]? with
  | some id => pure (id, ⟨tape, ops, leaves⟩)
  | none => do
    let (id, tape') ← raw tape
    pure (id, ⟨tape', ops.insert (name, ps) id, leaves⟩)

/-- Record a leaf holding `x`, or return the leaf with the same name and value bits. -/
def leaf {s : Shape} (x : Tensor Float s) (name : Option String := none) : SharedTapeM Nat :=
  fun st =>
    let ⟨tape, ops, leaves⟩ := st
    let key := (name,
      (TorchLean.Storage.toArray (SomeTensor.ofTensor x).tensor.buffer).toList.map Float.toBits)
    match leaves[key]? with
    | some id => pure (id, ⟨tape, ops, leaves⟩)
    | none => do
      let (id, tape') ← (TapeM.leaf x (name := name)) tape
      pure (id, ⟨tape', ops, leaves.insert key id⟩)

end SharedTapeM

/-- **The sharing tape carrier.** Running it appends the nodes of its sub-expression that are
not yet on the tape and returns the id of its result. -/
structure SharedTapeBuilder (s : Shape) where
  run : SharedTapeM Nat

namespace SharedTapeBuilder

variable {s : Shape}

/-- A constant leaf filled with the host scalar `x`. -/
def const (x : Float) : SharedTapeBuilder s := ⟨SharedTapeM.leaf (Tensor.full s x)⟩

/-- A named input leaf holding `x`. -/
def input (name : String) (x : Tensor Float s) : SharedTapeBuilder s :=
  ⟨SharedTapeM.leaf x (name := some name)⟩

/-- A `MathFunctions` field with no tape op: an error if run (as `TapeBuilder.unsupported`). -/
def unsupported (op : String) : SharedTapeBuilder s :=
  ⟨throw s!"SharedTapeBuilder: `{op}` has no elementwise tape op"⟩

/-- Lift a binary tape op named `name`: run both operands, emit or reuse one node. -/
@[inline] def bin (name : String) (f : Nat → Nat → TapeM Float Nat)
    (x y : SharedTapeBuilder s) : SharedTapeBuilder s :=
  ⟨do let a ← x.run; let b ← y.run; SharedTapeM.op name #[a, b] (f a b)⟩

/-- Lift a unary tape op named `name`: run the operand, emit or reuse one node. -/
@[inline] def un (name : String) (f : Nat → TapeM Float Nat)
    (x : SharedTapeBuilder s) : SharedTapeBuilder s :=
  ⟨do let a ← x.run; SharedTapeM.op name #[a] (f a)⟩

instance : Zero (SharedTapeBuilder s) := ⟨const 0⟩
instance : One (SharedTapeBuilder s) := ⟨const 1⟩
instance : Add (SharedTapeBuilder s) := ⟨bin "add" (TapeM.add (s := s))⟩
instance : Sub (SharedTapeBuilder s) := ⟨bin "sub" (TapeM.sub (s := s))⟩
instance : Mul (SharedTapeBuilder s) := ⟨bin "mul" (TapeM.mul (s := s))⟩
instance : Div (SharedTapeBuilder s) := ⟨bin "div" (TapeM.div (s := s))⟩
instance : Min (SharedTapeBuilder s) := ⟨bin "min" (TapeM.min (s := s))⟩
instance : Max (SharedTapeBuilder s) := ⟨bin "max" (TapeM.max (s := s))⟩
/-- The NaN-ignoring minimum (`Op.fmin`) as one shared tape node. -/
def fmin : SharedTapeBuilder s → SharedTapeBuilder s → SharedTapeBuilder s :=
  bin "fmin" (TapeM.fmin (s := s))
/-- The NaN-ignoring maximum (`Op.fmax`) as one shared tape node. -/
def fmax : SharedTapeBuilder s → SharedTapeBuilder s → SharedTapeBuilder s :=
  bin "fmax" (TapeM.fmax (s := s))
instance : Coe Nat (SharedTapeBuilder s) := ⟨fun n => const ((n : Float))⟩

instance : MathFunctions (SharedTapeBuilder s) where
  exp  := un "exp" (TapeM.exp  (s := s))
  log  := un "log" (TapeM.log  (s := s))
  abs  := un "abs" (TapeM.abs  (s := s))
  sqrt := un "sqrt" (TapeM.sqrt (s := s))
  pi   := const MathFunctions.pi
  sin  := fun _ => unsupported "sin"
  cos  := fun _ => unsupported "cos"
  tanh := fun _ => unsupported "tanh"
  cosh := fun _ => unsupported "cosh"
  sinh := fun _ => unsupported "sinh"

/-- The sharing tape carrier is a `NumCarrier`, op for op as `TapeBuilder`. -/
instance instNumCarrier : NumCarrier (SharedTapeBuilder s) where

/-- One shared `lutfetch:<name>` node: `TapeBuilder.lutFetchM` on the operands' ids. -/
instance : LutInterp (SharedTapeBuilder s) where
  lutFetch := fun tbl => bin tbl.nodeName
    (fun l u => (TapeBuilder.lutFetchM (s := s) tbl ⟨pure l⟩ ⟨pure u⟩).run)

end SharedTapeBuilder

/-- **The sharing tape carrier as a `BatchCarrier`**, field for field as `TapeBuilder`'s. -/
instance SharedTapeBuilder.instBatchCarrier : BatchCarrier SharedTapeBuilder where
  const        := fun v => SharedTapeBuilder.const v
  ofFloatArray := fun {s} a => ⟨SharedTapeM.leaf (TapeBuilder.tensorOfFloatArray s a 0)⟩
  toFloatArray := fun {s} b =>
    match SharedTapeM.record b.run with
    | .ok (id, t) =>
        match t.nodes[id]? with
        | some node => (TorchLean.Storage.toArray node.value.tensor.buffer).foldl
                          (fun acc x => acc.push x) (FloatArray.emptyWithCapacity (Shape.size s))
        | none      => FloatArray.emptyWithCapacity 0
    | .error _  => FloatArray.emptyWithCapacity 0
  fmin         := SharedTapeBuilder.fmin
  fmax         := SharedTapeBuilder.fmax
  liveSize     := fun {s} _ => (Shape.size s).toUInt32
  release      := fun _ => 0

end PropertyKindCalculus.Paradigm

end Blanket
